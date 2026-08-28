#lang racket

(require json
         racket/cmdline
         racket/file
         racket/list
         racket/match
         racket/path
         racket/port
         racket/pretty
         racket/runtime-path
         racket/set
         racket/string
         redex/reduction-semantics
         "check.rkt"
         "extract.rkt"
         "inventory.rkt"
         "syntax.rkt"
         "types.rkt")

(provide (struct-out lowering-case)
         (struct-out lowering-candidate)
         (struct-out lowering-manifest)
         (struct-out rr-case)
         (struct-out rr-fixture)
         (struct-out no-lowering)
         (struct-out lowered)
         (struct-out normalization)
         (struct-out case-report)
         (struct-out fence-report)
         (struct-out mutation-sweep-result)
         SmusniM3
         m3-lower
         display-normalize
         load-lowering-manifest
         load-parse-fixture
         load-rr-fixture
         validate-lowering-fixtures!
         refresh-parses!
         fragment-rule-ids
         datum->core
         parse-case-tokens
         parse-case-variants
         parse-case->sigma
         normalize-core
         redex-alpha-equivalent?
         site-signatures
         fixture-derivation-check
         generated-redex-check
         no-lowering-fails?
         aggregate-fence-disposition
         run-parse-mutation-sweeps
         run-lowering-gate
         lower)

(define-runtime-path tool-dir ".")
(define manifest-path (build-path tool-dir "inventory" "lowering.sexp"))
(define parse-dir (build-path tool-dir "inventory" "parses"))
(define rr-dir (build-path tool-dir "inventory" "rr"))

(struct lowering-case (index surface category promised-rows unresolved)
  #:transparent)
(struct lowering-candidate (source ordinal digest rules cases) #:transparent)
(struct lowering-manifest (families rule-count candidates) #:transparent)
(struct rr-case (index fields) #:transparent)
(struct rr-fixture (source ordinal digest cases) #:transparent)

;; `no-lowering` is a result of the derived relation, never a core term.
(struct no-lowering (rule cause premise detail) #:transparent)
(struct lowered (term rules) #:transparent)
(struct normalization (datum expansions) #:transparent)
(struct case-report
  (source ordinal index disposition cause rules expansions message produced expected)
  #:transparent)
(struct fence-report (source ordinal disposition cases) #:transparent)
(struct gentufa-terminal (kind text start stop) #:transparent)
(struct mutation-sweep-result
  (wrapper-attempts wrapper-allowlisted deletion-attempts failures)
  #:transparent)
(struct hoist-site (key operand relation label type deps declaration-index)
  #:transparent)

(define (site-variable-suggestion key)
  (string->symbol
   (string-append
    "$"
    (regexp-replace* #px"[^A-Za-z0-9_]" (symbol->string key) "_"))))

(define (build-global-hoist-datum properties site-data)
  (define avoid `(,properties ,site-data))
  (define site-variables (make-hash))
  (define allocated '())
  (for ([site (in-list site-data)])
    (match-define `(site ,key ,_operand ,_relation ,_label ,_type
                         (deps ,_ ...)) site)
    (define variable
      (variable-not-in (append avoid allocated)
                       (site-variable-suggestion key)))
    (hash-set! site-variables key variable)
    (set! allocated (cons variable allocated)))
  (define restrictor-member
    (variable-not-in (append avoid allocated) '$restrictor_member))
  (define nuclear-member
    (variable-not-in (append avoid allocated (list restrictor-member))
                     '$nuclear_member))
  (define bindings
    (for/list ([site (in-list site-data)])
      (match-define `(site ,key ,_operand ,_relation ,_label ,type
                           (deps ,dependencies ...)) site)
      (define dependency-variables
        (map (lambda (dependency) (hash-ref site-variables dependency))
             dependencies))
      `(,(hash-ref site-variables key) ,type
        (Context ,@dependency-variables))))
  (define (property-datum role member)
    (match-define `(property ,_ ,relation ,total ,event-mode)
      (findf (lambda (property) (eq? (second property) role)) properties))
    (define fills (make-hash (list (cons 1 member))))
    (for ([site (in-list site-data)])
      (match site
        [`(site ,key ,(== role) ,_relation ,label ,_type (deps ,_ ...))
         (hash-set! fills label (hash-ref site-variables key))]
        [_ (void)]))
    (unless (equal? (sort (hash-keys fills) <)
                    (range 1 (add1 total)))
      (error 'build-global-hoist-datum
             "property ~a does not have every row place filled" role))
    (define application
      `(,relation
        ,@(for/list ([label (in-range 1 (add1 total))])
            (hash-ref fills label))))
    `(λ (,member :: Entity)
       ,(if (eq? event-mode 'direct-event) `(Close ,application) application)))
  `(hoisted ,bindings
            ,(property-datum 'restrictor restrictor-member)
            ,(property-datum 'nuclear nuclear-member)))

(define (compose-global-exactly quantity hoisted)
  (match hoisted
    [`(hoisted ,bindings ,restrictor ,nuclear)
     (define body `(GlobalExactly ,quantity ,restrictor ,nuclear))
     (if (null? bindings)
         body
         `(Bind
           ,@(append-map
              (lambda (binding)
                (match-define `(,variable ,type ,computation) binding)
                (list `(,variable :: ,@type) computation))
              bindings)
           ,body))]
    [_ (error 'compose-global-exactly "invalid hoisted datum: ~e" hoisted)]))

;; M3's executable semantics. The Racket driver converts a validated gentufa
;; fixture to the small source view below; all core construction happens in
;; this Redex judgment. Rule names are the normative §11 ids and become the
;; formed-coverage evidence through `build-derivations`.
(define-language SmusniM3
  [x variable-not-otherwise-mentioned]
  [e any])

(define-metafunction SmusniM3
  app* : x (e ...) -> e
  [(app* x_R (e_arg ...)) (x_R e_arg ...)])

(define-metafunction SmusniM3
  pure-out : e x -> e
  [(pure-out lexical x_P) (λ (x_ref :: Entity) (x_P x_ref))
   (where x_ref ,(variable-not-in (term x_P) '$x))]
  [(pure-out described x_P)
   (λ (x_ref :: Entity)
     (SpeakerDescribes
      x_ref (λ (x_unit :: Referents Entity) (x_P x_unit))))
   (where x_ref ,(variable-not-in (term x_P) '$x))
   (where x_unit ,(variable-not-in (term (x_P x_ref)) '$y))])

(define-metafunction SmusniM3
  l0-out : e -> e
  [(l0-out (pure e_kind x_P)) (pure-out e_kind x_P)]
  [(l0-out (global-hoist e_properties e_sites))
   ,(build-global-hoist-datum (term e_properties) (term e_sites))])

(define-metafunction SmusniM3
  apply* : e (e ...) -> e
  [(apply* e_R (e_arg ...)) (e_R e_arg ...)])

(define-metafunction SmusniM3
  drop* : e (e ...) -> e
  [(drop* e_R ()) e_R]
  [(drop* e_R (e_label e_rest ...))
   (drop* (DropPlace e_R e_label) (e_rest ...))])

(define-metafunction SmusniM3
  force-out : e e -> e
  [(force-out assert e_body) (Assert e_body)]
  [(force-out mention e_body) (Mention e_body)])

(define-metafunction SmusniM3
  close-out : e e -> e
  [(close-out shorthand e_body) (Close e_body)]
  [(close-out actual e_body) (CloseClause (ActualClause e_body))]
  [(close-out clause e_body) (CloseClause e_body)])

(define-metafunction SmusniM3
  route-out : e -> e
  [(route-out (application x_R e_arg ...)) (x_R e_arg ...)]
  [(route-out (se-lambda x_R))
   (λ (x_left x_right :: Referents Entity) (x_R x_right x_left))
   (where x_left ,(variable-not-in (term x_R) '$new1))
   (where x_right ,(variable-not-in (term (x_R x_left)) '$new2))])

(define-metafunction SmusniM3
  connective-out : e e e -> e
  [(connective-out not e_left none) (ClauseNot (DirectClause e_left))]
  [(connective-out and e_left e_right)
   (ClauseAnd (DirectClause e_left) (DirectClause e_right))]
  [(connective-out or e_left e_right)
   (ClauseOr (DirectClause e_left) (DirectClause e_right))])

(define-metafunction SmusniM3
  cohe-out : e e e e -> e
  [(cohe-out e_force e_row e_left e_right)
   (Bind (x_relation :: PredTerm e_row) (Context)
     (force-out e_force (Close (x_relation e_left e_right))))
   (where x_relation
          ,(variable-not-in
            (term (e_force e_row e_left e_right)) '$r))])

(define-metafunction SmusniM3
  termset-out : e e x e x x -> e
  [(termset-out e_force e_n1 e_P1 e_n2 e_P2 x_Q)
   (Bind (x_left_set :: Referents Entity)
         (SelectExactly e_n1 (λ (x_left_unit :: Entity)
                               (e_P1 x_left_unit)))
         (x_right_set :: Referents Entity)
         (SelectExactly e_n2 (λ (x_right_unit :: Entity)
                               (e_P2 x_right_unit)))
     (force-out e_force
      (Distrib
       (λ (x_left :: Entity)
         (Distrib (λ (x_right :: Entity)
                    (Close (x_Q x_left x_right)))
                  x_right_set))
       x_left_set)))
   (where x_left_set
          ,(variable-not-in
            (term (e_force e_n1 e_P1 e_n2 e_P2 x_Q)) '$left))
   (where x_left_unit
          ,(variable-not-in (term (e_n1 e_P1 e_n2 e_P2 x_Q x_left_set)) '$x))
   (where x_right_set
          ,(variable-not-in
            (term (e_n1 e_P1 e_n2 e_P2 x_Q x_left_set x_left_unit))
            '$right))
   (where x_right_unit
          ,(variable-not-in
            (term (e_n1 e_P1 e_n2 e_P2 x_Q x_left_set x_left_unit
                        x_right_set))
            '$x))
   (where x_left
          ,(variable-not-in
            (term (e_n1 e_P1 e_n2 e_P2 x_Q x_left_set x_left_unit
                        x_right_set x_right_unit))
            '$l))
   (where x_right
          ,(variable-not-in
            (term (e_n1 e_P1 e_n2 e_P2 x_Q x_left_set x_left_unit
                        x_right_set x_right_unit x_left))
            '$r))])

(define-metafunction SmusniM3
  grade-out : e x e -> e
  [(grade-out e_force x_R e_arg)
   (Bind (x_scale :: Scale) (Context)
         (x_region :: Region Scale)
         (Vague (λ (x_cutoff :: Region Scale)
                  (AdmissibleCutoff x_scale x_cutoff)))
     (force-out e_force (Close ((Grade x_R x_scale x_region) e_arg))))
   (where x_scale ,(variable-not-in (term (e_force x_R e_arg)) '$s))
   (where x_region
          ,(variable-not-in (term (x_R e_arg x_scale)) '$reg))
   (where x_cutoff
          ,(variable-not-in (term (x_R e_arg x_scale x_region)) '$r))])

(define-metafunction SmusniM3
  scalar-out : e e x e -> e
  [(scalar-out e_force e_kind x_R e_arg)
   (Bind (x_domain :: ContrastDomain (RowOf x_R)) (Context)
     (force-out e_force (Close ((Scalar e_kind x_domain x_R) e_arg))))
   (where x_domain
          ,(variable-not-in (term (e_force e_kind x_R e_arg)) '$d))])

(define-metafunction SmusniM3
  zip-out : x (e ...) (e ...) -> e
  [(zip-out x_R (e_left ...) (e_right ...))
   (ZipWith
    (λ (x_left x_right :: Referents Entity)
      (Close (x_R x_left x_right)))
    (List e_left ...)
    (List e_right ...))
   (where x_left
          ,(variable-not-in (term (x_R e_left ... e_right ...)) '$left))
   (where x_right
          ,(variable-not-in
            (term (x_R e_left ... e_right ... x_left)) '$right))])

(define-metafunction SmusniM3
  nuclear-out : e e e -> e
  [(nuclear-out e_var Entity e_body)
   (λ (e_var :: Entity) e_body)]
  [(nuclear-out e_var (Referents Entity) e_body)
   (λ (e_var :: Referents Entity) e_body)])

(define-metafunction SmusniM3
  description-source : e x e x -> e
  [(description-source e_force x_Q positive x_ref)
   (force e_force (close shorthand (pred x_Q x_ref)))]
  [(description-source e_force x_Q positive-omit x_ref)
   (force e_force (close shorthand (omit (pred x_Q x_ref))))]
  [(description-source e_force x_Q negative x_ref)
   (force e_force (close clause (na (pred x_Q x_ref))))])

(define-metafunction SmusniM3
  le-cont-source : e x -> e
  [(le-cont-source (pure described x_P) x_ref) (l0 (pure described x_P))]
  [(le-cont-source (description x_Q e_polarity e_force) x_ref)
   (description-source e_force x_Q e_polarity x_ref)])

(define-metafunction SmusniM3
  cardinal-cont-source : e x x -> e
  [(cardinal-cont-source none x_Q x_ref)
   (close shorthand (pred x_Q x_ref))]
  [(cardinal-cont-source e_force x_Q x_ref)
   (force e_force (close shorthand (pred x_Q x_ref)))
   (side-condition (member (term e_force) '(assert mention)))])

(define-metafunction SmusniM3
  cardinal-sources : e e e x x e e x -> (e ...)
  [(cardinal-sources witness e_force e_n x_P x_Q () () x_witness)
   ((l0 (pure lexical x_P))
    (cardinal-cont-source e_force x_Q x_witness))]
  [(cardinal-sources global none e_n x_P x_Q e_properties e_sites x_unused)
   ((l0 (global-hoist e_properties e_sites)))])

(define-metafunction SmusniM3
  cardinal-compose : e e x (e ...) -> e
  [(cardinal-compose witness e_n x_witness (e_P e_Q_body))
   (Bind (x_witness :: Referents Entity)
         (SelectExactly e_n e_P)
     e_Q_body)]
  [(cardinal-compose global e_n x_unused (e_hoisted))
   ,(compose-global-exactly (term e_n) (term e_hoisted))])

(define-metafunction SmusniM3
  le-out : x e x e -> e
  [(le-out x_P (pure described x_P) x_ref e_property) e_property]
  [(le-out x_P e_continuation x_ref e_body)
   (Bind (x_ref :: Referents Entity)
         (Refer
          (λ (x_described :: Referents Entity)
            (SpeakerDescribes
             x_described
             (λ (x_unit :: Referents Entity) (x_P x_unit)))))
     e_body)
   (where x_described
          ,(variable-not-in
            (term (x_P e_continuation x_ref e_body)) '$described))
   (where x_unit
          ,(variable-not-in
            (term (x_P e_continuation x_ref e_body x_described)) '$unit))])

(define-metafunction SmusniM3
  threshold-out : e e e e -> e
  [(threshold-out e_force many e_P e_Q)
   (Bind (x_threshold :: Natural)
         (Vague (AdmissibleThreshold ManyK e_P))
     (force-out e_force (AtLeast x_threshold e_P e_Q)))
   (where x_threshold ,(variable-not-in (term (e_P e_Q)) '$n))]
  [(threshold-out e_force too-many e_P e_Q)
   (Bind (x_purpose :: Referents Entity) (Context)
         (x_threshold :: Natural)
         (Vague (AdmissibleThreshold TooManyK e_P x_purpose))
     (force-out e_force (MoreThan x_threshold e_P e_Q)))
   (where x_purpose ,(variable-not-in (term (e_P e_Q)) '$purpose))
   (where x_threshold
          ,(variable-not-in (term (e_P e_Q x_purpose)) '$n))])

(define-metafunction SmusniM3
  global-exactly-definition : e -> e
  [(global-exactly-definition e_term)
   ,(expand-global-exactly-datum (term e_term))])

(define-metafunction SmusniM3
  display-normalize : e e -> e
  [(display-normalize e_rows e_term)
   ,(let-values ([(normalized expansions)
                  (normalize-datum (term e_term) (load-inventory)
                                   (term e_rows))])
      `(normalized ,normalized ,expansions))])

(define-judgment-form SmusniM3
  #:mode (m3-lower I I O)
  #:contract (m3-lower e e e)

  [(where e_out (l0-out e_source))
   --------------------------------------------- "L0.1"
   (m3-lower e_RR (gentufa e_parse (l0 e_source)) e_out)]

  [(where e_out (app* x_R (e_arg ...)))
   --------------------------------------------- "L1.1"
   (m3-lower e_RR (gentufa e_parse (pred x_R e_arg ...)) e_out)]

  [(m3-lower e_RR (gentufa e_parse e_source) e_body)
   (where e_out (force-out e_force e_body))
   --------------------------------------------- "L1.2"
   (m3-lower e_RR (gentufa e_parse (force e_force e_source)) e_out)]

  [(m3-lower e_RR (gentufa e_parse e_source) e_body)
   (where e_out (close-out e_mode e_body))
   --------------------------------------------- "L1.3"
   (m3-lower e_RR (gentufa e_parse (close e_mode e_source)) e_out)]

  [(where e_out (route-out e_route))
   --------------------------------------------- "L1.4"
   (m3-lower e_RR (gentufa e_parse (route e_route)) e_out)]

  [(where e_relation (drop* x_R (e_label ...)))
   (where e_out (apply* e_relation (e_arg ...)))
   --------------------------------------------- "L1.5"
   (m3-lower e_RR
             (gentufa e_parse (drop x_R (e_label ...) e_arg ...)) e_out)]

  [(m3-lower e_RR (gentufa e_parse e_source) e_out)
   --------------------------------------------- "L1.6"
   (m3-lower e_RR (gentufa e_parse (omit e_source)) e_out)]

  [(where e_out (cohe-out e_force e_row e_left e_right))
   --------------------------------------------- "L1.8"
   (m3-lower e_RR
             (gentufa e_parse (cohe e_force e_row e_left e_right)) e_out)]

  [(where e_relation (Tanru x_M x_H))
   (where e_out (apply* e_relation (e_arg ...)))
   --------------------------------------------- "L1.10"
   (m3-lower e_RR (gentufa e_parse (tanru x_M x_H e_arg ...)) e_out)]

  [(where x_ref ,(variable-not-in (term (e_RR e_parse x_P x_Q)) '$r))
   (where x_unit
          ,(variable-not-in (term (e_RR e_parse x_P x_Q x_ref)) '$unit))
   (where e_continuation
          (description-source e_force x_Q e_polarity x_ref))
   (m3-lower e_RR (gentufa e_parse e_continuation) e_body)
   --------------------------------------------- "L3.1"
   (m3-lower e_RR (gentufa e_parse (lo x_P x_Q e_polarity e_force))
             (Bind (x_ref :: Referents Entity)
                   (Refer (λ (x_unit :: Referents Entity) (x_P x_unit)))
               e_body))]

  [(where x_ref ,(variable-not-in (term (e_RR e_parse x_P e_continuation))
                                  '$r))
   (where e_source (le-cont-source e_continuation x_ref))
   (m3-lower e_RR (gentufa e_parse e_source) e_body)
   (where e_out (le-out x_P e_continuation x_ref e_body))
   --------------------------------------------- "L3.2"
   (m3-lower e_RR (gentufa e_parse (le x_P e_continuation))
             e_out)]

  [(where x_ref ,(variable-not-in (term (e_RR e_parse e_name x_Q)) '$r))
   (where x_named
          ,(variable-not-in (term (e_RR e_parse e_name x_Q x_ref)) '$named))
   (where e_continuation
          (description-source e_force x_Q positive-omit x_ref))
   (m3-lower e_RR (gentufa e_parse e_continuation) e_body)
   --------------------------------------------- "L3.3"
   (m3-lower e_RR (gentufa e_parse (la e_name x_Q e_force))
             (Bind (x_ref :: Referents Entity)
                   (Refer (λ (x_named :: Referents Entity)
                            (Named e_name x_named)))
               e_body))]

  [(where x_unit ,(variable-not-in (term (e_RR e_parse x_P x_Q)) '$x))
   (m3-lower e_RR (gentufa e_parse (l0 (pure lexical x_P))) e_P)
   (m3-lower e_RR
             (gentufa e_parse (close shorthand (pred x_Q x_unit))) e_Q_body)
   --------------------------------------------- "L3.4"
   (m3-lower e_RR (gentufa e_parse (generic x_P x_Q))
             (Generic Typical e_P (λ (x_unit :: Entity) e_Q_body)))]

  [(where x_unit ,(variable-not-in (term (e_RR e_parse x_P)) '$x))
   --------------------------------------------- "L3.5"
   (m3-lower e_RR (gentufa e_parse (collection-base x_P))
             (Local (Refer (λ (x_unit :: Entity) (x_P x_unit)))))]

  [(where x_base ,(variable-not-in (term (e_RR e_parse x_P)) '$base))
   (where x_sets
          ,(variable-not-in (term (e_RR e_parse x_P x_base)) '$sets))
   (where x_set
          ,(variable-not-in (term (e_RR e_parse x_P x_base x_sets)) '$s))
   (m3-lower e_RR (gentufa e_parse (collection-base x_P)) e_base)
   --------------------------------------------- "L3.6"
   (m3-lower e_RR (gentufa e_parse (collection-set x_P))
             (Bind (x_base :: Referents Entity) e_base
               (Bind (x_sets :: Referents (Set Entity))
                     (Refer (λ (x_set :: Set Entity)
                              (Close (selcmi x_set x_base))))
                 (Mention x_sets))))]

  [(m3-lower e_RR (gentufa e_parse (le-unit x_P)) e_P)
   --------------------------------------------- "L3.9"
   (m3-lower e_RR (gentufa e_parse (inner-pa e_n x_P))
             (SelectExactly e_n e_P))]

  [(where x_people
          ,(variable-not-in (term (e_RR e_parse e_n x_P)) '$people))
   (where x_basis
          ,(variable-not-in
            (term (e_RR e_parse e_n x_P x_people)) '$κ))
   (where x_aggregate
          ,(variable-not-in
            (term (e_RR e_parse e_n x_P x_people x_basis)) '$aggregate))
   (m3-lower e_RR (gentufa e_parse (inner-pa e_n x_P)) e_selection)
   --------------------------------------------- "L3.14"
   (m3-lower e_RR (gentufa e_parse (luho e_n x_P))
             (Bind (x_people :: Referents Entity) (Local e_selection)
               (Bind (x_basis :: DecompositionBasis (Group Entity) Entity)
                     (Context (GroupBasisConstraint |lu'o| Entity) deps…)
                 (Bind (x_aggregate :: Referents (Group Entity))
                       (Massify x_basis x_people)
                   (Mention x_aggregate)))))]

  [(m3-lower e_RR
             (gentufa e_parse (le x_P (pure described x_P))) e_property)
   --------------------------------------------- "L3.15"
   (m3-lower e_RR (gentufa e_parse (le-unit x_P)) e_property)]

  [(where x_unit ,(variable-not-in (term (e_RR e_parse x_P x_Q)) '$x))
   (m3-lower e_RR (gentufa e_parse (l0 (pure lexical x_P))) e_P)
   (m3-lower e_RR
             (gentufa e_parse (close shorthand (pred x_Q x_unit))) e_Q_body)
   --------------------------------------------- "L5.1"
   (m3-lower e_RR (gentufa e_parse (every x_P x_Q))
             (Every e_P (λ (x_unit :: Entity) e_Q_body)))]

  [(where x_witness
          ,(variable-not-in
            (term (e_RR e_parse e_mode e_force e_n x_P x_Q
                        e_properties e_sites)) '$w))
   (where (e_subsource ...)
          (cardinal-sources e_mode e_force e_n x_P x_Q
                            e_properties e_sites x_witness))
   (m3-lower e_RR (gentufa e_parse e_subsource) e_part) ...
   (where e_out
          (cardinal-compose e_mode e_n x_witness (e_part ...)))
   --------------------------------------------- "L5.2"
   (m3-lower e_RR
             (gentufa e_parse
                      (cardinal e_mode e_force e_n x_P x_Q
                                e_properties e_sites))
             e_out)]

  [(where e_out (termset-out e_force e_n1 x_P1 e_n2 x_P2 x_Q))
   --------------------------------------------- "L5.3"
   (m3-lower e_RR
             (gentufa e_parse
                      (termset e_force e_n1 x_P1 e_n2 x_P2 x_Q)) e_out)]

  [(m3-lower e_RR (gentufa e_parse (close shorthand (pred x_Q e_var))) e_body)
   (where e_out (nuclear-out e_var e_type e_body))
   --------------------------------------------- "L5.7"
  (m3-lower e_RR (gentufa e_parse (nuclear e_var e_type x_Q))
             e_out)]

  [(m3-lower e_RR (gentufa e_parse e_left) e_left_clause)
   (m3-lower e_RR (gentufa e_parse e_right) e_right_clause)
   (where e_out (connective-out e_kind e_left_clause e_right_clause))
   --------------------------------------------- "L5.8"
   (m3-lower e_RR (gentufa e_parse
                            (clause-connect e_kind e_left e_right))
             e_out)]

  [(m3-lower e_RR (gentufa e_parse e_source) e_body)
   --------------------------------------------- "L5.9"
   (m3-lower e_RR (gentufa e_parse (na e_source))
             (ClauseNot (DirectClause e_body)))]

  [(where e_out (scalar-out e_force e_kind x_P e_arg))
   --------------------------------------------- "L5.11"
   (m3-lower e_RR
             (gentufa e_parse (scalar e_force e_kind x_P e_arg)) e_out)]

  [(m3-lower e_RR (gentufa e_parse
                            (clause-connect e_kind e_left e_right)) e_clause)
   --------------------------------------------- "L5.12"
   (m3-lower e_RR (gentufa e_parse
                            (sentence-connect e_kind e_left e_right))
             e_clause)]

  [(where e_out (zip-out x_R (e_left ...) (e_right ...)))
   --------------------------------------------- "L5.21"
   (m3-lower e_RR
             (gentufa e_parse (zip x_R (e_left ...) (e_right ...))) e_out)]

  [(where x_witness
          ,(variable-not-in (term (e_RR e_parse e_kind x_P x_Q)) '$w))
   (m3-lower e_RR (gentufa e_parse (l0 (pure lexical x_P))) e_P)
   (m3-lower e_RR (gentufa e_parse
                            (nuclear x_witness (Referents Entity) x_Q)) e_Q)
   (where e_out (threshold-out e_force e_kind e_P e_Q))
   --------------------------------------------- "L5.28"
   (m3-lower e_RR
             (gentufa e_parse (threshold e_force e_kind x_P x_Q)) e_out)]

  [(where e_out (grade-out e_force x_R e_arg))
   --------------------------------------------- "L5.29"
   (m3-lower e_RR
             (gentufa e_parse (grade e_force x_R e_arg)) e_out)] )

(define rr-field-names
  '(parse attach readings rows stores sites anaphora force))
(define no-lowering-causes
  '(rr-missing row-missing rule-underspecified implementation out-of-fragment))

(define (source-stem source)
  (path->string (path-replace-extension (file-name-from-path source) #"")))

(define (fixture-base-name source ordinal)
  (format "~a-~a" (source-stem source)
          (~r ordinal #:min-width 3 #:pad-string "0")))

(define (candidate-parse-path candidate)
  (build-path parse-dir
              (string-append
               (fixture-base-name (lowering-candidate-source candidate)
                                  (lowering-candidate-ordinal candidate))
               ".json")))

(define (candidate-rr-path candidate)
  (build-path rr-dir
              (string-append
               (fixture-base-name (lowering-candidate-source candidate)
                                  (lowering-candidate-ordinal candidate))
               ".sexp")))

(define (parse-case-datum datum source ordinal)
  (match datum
    [`(case ,(? exact-positive-integer? index) ,surface ,(? symbol? category)
            (promised-rows ,(? symbol? rows) ...) ,clauses ...)
     (unless (or (string? surface) (eq? surface #f))
       (error 'load-lowering-manifest
              "~a#~a case ~a surface must be a string or #f"
              source ordinal index))
     (define unresolved #f)
     (for ([clause (in-list clauses)])
       (match clause
         [`(unresolved ,(? string? note)) (set! unresolved note)]
         [else
          (error 'load-lowering-manifest
                 "invalid case clause in ~a#~a.~a: ~e"
                 source ordinal index clause)]))
     (when (and (not surface) (not unresolved))
       (error 'load-lowering-manifest
              "~a#~a.~a without a surface needs an unresolved reason"
              source ordinal index))
     (lowering-case index surface category rows unresolved)]
    [else
     (error 'load-lowering-manifest
            "invalid candidate case in ~a#~a: ~e" source ordinal datum)]))

(define (parse-candidate-datum datum)
  (match datum
    [`(candidate ,(? string? source) ,(? exact-positive-integer? ordinal)
                 ,(? string? digest) (rules ,(? string? rules) ...) ,cases ...)
     (define parsed-cases
       (for/list ([case-datum (in-list cases)])
         (parse-case-datum case-datum source ordinal)))
     (unless (equal? (map lowering-case-index parsed-cases)
                     (range 1 (add1 (length parsed-cases))))
       (error 'load-lowering-manifest
              "~a#~a case indexes must be consecutive from 1" source ordinal))
     (lowering-candidate source ordinal digest rules parsed-cases)]
    [else (error 'load-lowering-manifest "invalid candidate: ~e" datum)]))

(define (load-lowering-manifest [path manifest-path])
  (match (call-with-input-file path read)
    [`(smusni-lowering-manifest 1
        (fragment (families ,(? string? families) ...)
                  (lowering-judgments ,(? exact-positive-integer? count)))
        ,candidate-data ...)
     (define candidates (map parse-candidate-datum candidate-data))
     (define keys
       (for/list ([candidate (in-list candidates)])
         (cons (lowering-candidate-source candidate)
               (lowering-candidate-ordinal candidate))))
     (unless (= (length keys) (set-count (list->set keys)))
       (error 'load-lowering-manifest "duplicate candidate fence key"))
     (lowering-manifest families count candidates)]
    [else (error 'load-lowering-manifest "unsupported lowering manifest")]))

(define (fragment-rule-ids [manifest (load-lowering-manifest)]
                           [rules (spec-rules)])
  (define family-prefixes
    (for/list ([family (in-list (lowering-manifest-families manifest))])
      (string-append family ".")))
  (define ids
    (for/list ([rule (in-list rules)]
               #:when (and (eq? (cdr rule) 'map)
                           (for/or ([prefix (in-list family-prefixes)])
                             (string-prefix? (car rule) prefix))))
      (car rule)))
  (unless (= (length ids) (lowering-manifest-rule-count manifest))
    (error 'fragment-rule-ids
           "manifest records ~a lowering judgments, live spec has ~a: ~e"
           (lowering-manifest-rule-count manifest) (length ids) ids))
  ids)

(define (manifest-candidate-map manifest)
  (for/hash ([candidate (in-list (lowering-manifest-candidates manifest))])
    (values (cons (lowering-candidate-source candidate)
                  (lowering-candidate-ordinal candidate))
            candidate)))

(define (validate-candidates-against-fences! manifest)
  (define classified
    (classify-fences (read-all-fences) (load-manifest)))
  (define by-key
    (for/hash ([item (in-list classified)])
      (values (cons (fence-source item) (fence-ordinal item)) item)))
  (for ([candidate (in-list (lowering-manifest-candidates manifest))])
    (define key (cons (lowering-candidate-source candidate)
                      (lowering-candidate-ordinal candidate)))
    (define item
      (hash-ref by-key key
                (lambda ()
                  (error 'validate-lowering-fixtures!
                         "candidate fence does not exist: ~e" key))))
    (unless (eq? (fence-kind item) 'specimen)
      (error 'validate-lowering-fixtures! "candidate is not a specimen: ~e" key))
    (unless (string=? (fence-digest item) (lowering-candidate-digest candidate))
      (error 'validate-lowering-fixtures!
             "stale candidate digest for ~a#~a"
             (car key) (cdr key)))
    (unless (equal? (fence-rules item) (lowering-candidate-rules candidate))
      (error 'validate-lowering-fixtures!
             "candidate rules drifted for ~a#~a" (car key) (cdr key)))
    (define forms (read-core-forms (fence-content item)))
    (unless (= (length forms) (length (lowering-candidate-cases candidate)))
      (error 'validate-lowering-fixtures!
             "candidate ~a#~a has ~a core forms but ~a lowering cases"
             (car key) (cdr key) (length forms)
             (length (lowering-candidate-cases candidate))))))

(define (candidate-source-comments candidate)
  (define item
    (for/first ([fence (in-list
                        (classify-fences (read-all-fences) (load-manifest)))]
                #:when (and
                        (string=? (fence-source fence)
                                  (lowering-candidate-source candidate))
                        (= (fence-ordinal fence)
                           (lowering-candidate-ordinal candidate))))
      fence))
  (unless item
    (error 'candidate-source-comments "candidate fence is absent"))
  (define lines (string-split (fence-content item) "\n" #:trim? #f))
  (define forms (read-core-forms (fence-content item)))
  (for/list ([form (in-list forms)])
    (define line-index (sub1 (or (core-list-line form) 1)))
    (define comments
      (let loop ([index (sub1 line-index)] [found '()])
        (cond
          [(negative? index) found]
          [else
           (define match
             (regexp-match #px"^;[ ]?(.*)$" (list-ref lines index)))
           (if match
               (loop (sub1 index) (cons (second match) found))
               found)])))
    (unless (pair? comments)
      (error 'candidate-source-comments
             "~a#~a form at line ~a has no leading comment"
             (fence-source item) (fence-ordinal item) (core-list-line form)))
    ;; §2 defines the first line of the contiguous comment header as the
    ;; Lojban source. Later lines explain the reading and must not replace it.
    (first comments)))

(define (read-json-file path)
  (call-with-input-file path read-json))

(define (json-ref object key who)
  (unless (hash? object) (error who "expected JSON object, got ~e" object))
  (hash-ref object key
            (lambda () (error who "missing JSON field ~a" key))))

(define (load-parse-fixture candidate)
  (define path (candidate-parse-path candidate))
  (unless (file-exists? path)
    (error 'load-parse-fixture "missing parse fixture ~a" path))
  (define data (read-json-file path))
  (unless (equal? (json-ref data 'schema 'load-parse-fixture)
                  "smusni-gentufa-parse-fixture-1")
    (error 'load-parse-fixture "unsupported parse fixture schema: ~a" path))
  (unless (and (equal? (json-ref data 'source 'load-parse-fixture)
                       (lowering-candidate-source candidate))
               (equal? (json-ref data 'ordinal 'load-parse-fixture)
                       (lowering-candidate-ordinal candidate))
               (equal? (json-ref data 'fence_sha1 'load-parse-fixture)
                       (lowering-candidate-digest candidate)))
    (error 'load-parse-fixture "parse metadata drift: ~a" path))
  (define fixture-cases (json-ref data 'cases 'load-parse-fixture))
  (define source-comments (candidate-source-comments candidate))
  (unless (= (length fixture-cases)
             (length (lowering-candidate-cases candidate)))
    (error 'load-parse-fixture "parse case count drift: ~a" path))
  (for ([expected (in-list (lowering-candidate-cases candidate))]
        [actual (in-list fixture-cases)]
        [source-comment (in-list source-comments)])
    (unless (and (= (json-ref actual 'index 'load-parse-fixture)
                    (lowering-case-index expected))
                 (equal? (json-ref actual 'surface 'load-parse-fixture)
                         (lowering-case-surface expected))
                 (equal? (string->symbol
                          (json-ref actual 'category 'load-parse-fixture))
                         (lowering-case-category expected))
                 (equal? (json-ref actual 'source_comment 'load-parse-fixture)
                         source-comment))
      (error 'load-parse-fixture "parse case metadata drift: ~a" path))
    (when (lowering-case-surface expected)
      (unless (string-contains? source-comment
                                (lowering-case-surface expected))
        (error 'load-parse-fixture
               "surface ~s is not present in its source comment ~s: ~a"
               (lowering-case-surface expected) source-comment path)))
    (if (lowering-case-surface expected)
        (unless (hash? (json-ref actual 'parse 'load-parse-fixture))
          (error 'load-parse-fixture "case ~a has no raw parse: ~a"
                 (lowering-case-index expected) path))
        (unless (eq? (json-ref actual 'parse 'load-parse-fixture) #f)
          (error 'load-parse-fixture "unresolved case unexpectedly has a parse: ~a"
                 path))))
  data)

(define (parse-rr-fields field-data source ordinal index)
  (define fields (make-hash))
  (for ([field (in-list field-data)])
    (match field
      [`(,(? symbol? name) ,value)
       (when (hash-has-key? fields name)
         (error 'load-rr-fixture "duplicate RR field ~a at ~a#~a.~a"
                name source ordinal index))
       (hash-set! fields name value)]
      [else
       (error 'load-rr-fixture "invalid RR field at ~a#~a.~a: ~e"
              source ordinal index field)]))
  (define unknown
    (filter (lambda (name) (not (member name rr-field-names)))
            (hash-keys fields)))
  (when (pair? unknown)
    (error 'load-rr-fixture
           "RR fixture at ~a#~a.~a has unknown fields ~e"
           source ordinal index (sort unknown symbol<?)))
  (make-immutable-hash (hash->list fields)))

(define (load-rr-fixture candidate [_inv (load-inventory)])
  (define path (candidate-rr-path candidate))
  (unless (file-exists? path)
    (error 'load-rr-fixture "missing RR fixture ~a" path))
  (match (call-with-input-file path read)
    [`(smusni-rr-fixture 1
        (fence ,(? string? source) ,(? exact-positive-integer? ordinal)
               ,(? string? digest))
        ,case-data ...)
     (unless (and (string=? source (lowering-candidate-source candidate))
                  (= ordinal (lowering-candidate-ordinal candidate))
                  (string=? digest (lowering-candidate-digest candidate)))
       (error 'load-rr-fixture "RR metadata drift: ~a" path))
     (define cases
       (for/list ([datum (in-list case-data)])
         (match datum
           [`(case ,(? exact-positive-integer? index) (rr ,fields ...))
            (rr-case index (parse-rr-fields fields source ordinal index))]
           [else (error 'load-rr-fixture "invalid RR case in ~a: ~e" path datum)])))
     (unless (equal? (map rr-case-index cases)
                     (map lowering-case-index
                          (lowering-candidate-cases candidate)))
       (error 'load-rr-fixture "RR case indexes drift: ~a" path))
     (for ([case (in-list cases)])
       (define rows (hash-ref (rr-case-fields case) 'rows (lambda () '())))
       (unless (and (list? rows) (andmap symbol? rows))
         (error 'load-rr-fixture "RR rows must be a symbol list: ~a" path)))
     (rr-fixture source ordinal digest cases)]
    [else (error 'load-rr-fixture "unsupported RR fixture: ~a" path)]))

(define (capture-command executable arguments [stdin #f])
  (define out (open-output-string))
  (define err (open-output-string))
  (define ok?
    (parameterize ([current-output-port out]
                   [current-error-port err]
                   [current-input-port
                    (if stdin (open-input-string stdin) (current-input-port))])
      (apply system* executable arguments)))
  (values ok? (get-output-string out) (get-output-string err)))

(define (jbotci-path)
  (or (find-executable-path "jbotci")
      (error 'refresh-parses! "jbotci is not on PATH")))

(define (jbotci-version executable)
  (define-values (ok? out err) (capture-command executable '("--version")))
  (unless ok? (error 'refresh-parses! "jbotci --version failed: ~a" err))
  (string-trim out))

(define (gentufa-parse executable surface)
  (define-values (ok? out err)
    (capture-command executable (list "gentufa" "--format" "json" surface)))
  (unless ok?
    (error 'refresh-parses! "gentufa failed for ~s: ~a" surface err))
  (call-with-input-string out read-json))

(define (pretty-json-string value)
  (define compact (jsexpr->string value))
  (define jq (find-executable-path "jq"))
  (if jq
      (let-values ([(ok? out err) (capture-command jq '(".") compact)])
        (if ok? out
            (error 'refresh-parses! "jq failed while formatting JSON: ~a" err)))
      (string-append compact "\n")))

(define (parse-fixture-jsexpr candidate executable version)
  (define source-comments (candidate-source-comments candidate))
  (hasheq
   'schema "smusni-gentufa-parse-fixture-1"
   'source (lowering-candidate-source candidate)
   'ordinal (lowering-candidate-ordinal candidate)
   'fence_sha1 (lowering-candidate-digest candidate)
   'jbotci_version version
   'cases
   (for/list ([case (in-list (lowering-candidate-cases candidate))]
              [source-comment (in-list source-comments)])
     (define surface (lowering-case-surface case))
     (hasheq
      'index (lowering-case-index case)
      'surface (or surface #f)
      'source_comment source-comment
      'category (symbol->string (lowering-case-category case))
      'command (if surface
                   (list "jbotci" "gentufa" "--format" "json" surface)
                   '())
      'parse (if surface (gentufa-parse executable surface) #f)
      'unresolved (or (lowering-case-unresolved case) #f)))))

(define (refresh-parses! [manifest (load-lowering-manifest)])
  (make-directory* parse-dir)
  (define executable (jbotci-path))
  (define version (jbotci-version executable))
  (for ([candidate (in-list (lowering-manifest-candidates manifest))])
    (define content
      (pretty-json-string (parse-fixture-jsexpr candidate executable version)))
    (call-with-output-file (candidate-parse-path candidate)
      #:exists 'truncate/replace
      (lambda (out) (display content out))))
  (printf "lowering parses refreshed: ~a fences, ~a cases; ~a\n"
          (length (lowering-manifest-candidates manifest))
          (for/sum ([candidate (in-list (lowering-manifest-candidates manifest))])
            (length (lowering-candidate-cases candidate)))
          version))

(define (validate-lowering-fixtures! [manifest (load-lowering-manifest)])
  (fragment-rule-ids manifest)
  (validate-candidates-against-fences! manifest)
  (define inv (load-inventory))
  (for ([candidate (in-list (lowering-manifest-candidates manifest))])
    (load-parse-fixture candidate)
    (load-rr-fixture candidate inv))
  (void))

(define (datum->core datum [source 'lowering])
  (define (walk value)
    (if (list? value)
        (core-list (map walk value) source #f #f #f #f)
        (core-atom value source #f #f #f #f)))
  (define ast (walk datum))
  (validate-core-form ast)
  ast)

(define (parse-case-variants parse-case)
  (define raw (json-ref parse-case 'parse 'parse-case-variants))
  (define variants (mutable-set))
  (define (walk value)
    (cond
      [(hash? value)
       (for ([(key child) (in-hash value)])
         (set-add! variants key)
         (walk child))]
      [(list? value) (for ([child (in-list value)]) (walk child))]
      [else (void)]))
  (walk raw)
  (list->set (set->list variants)))

(define (parse-terminal-spans raw)
  (define found '())
  (define (walk value)
    (cond
      [(hash? value)
       (when (and (hash-has-key? value 'phonemes)
                  (hash-has-key? value 'span))
         (match (hash-ref value 'span)
           [(list (? exact-nonnegative-integer? start)
                  (? exact-nonnegative-integer? stop))
            (set! found (cons (cons start stop) found))]
           [_ (void)]))
       (for ([child (in-hash-values value)]) (walk child))]
      [(list? value) (for ([child (in-list value)]) (walk child))]
      [else (void)]))
  (walk raw)
  (remove-duplicates found))

(define (spans-overlap? left right)
  (and (< (car left) (cdr right)) (< (car right) (cdr left))))

(define (parse-case-tokens parse-case)
  (define surface (json-ref parse-case 'surface 'parse-case-tokens))
  (unless (string? surface)
    (error 'parse-case-tokens "case has no surface string"))
  (define raw (json-ref parse-case 'parse 'parse-case-tokens))
  (unless (and (hash? raw) (hash-has-key? raw 'RegularText))
    (error 'parse-case-tokens "case is not a gentufa RegularText parse"))
  (define terminal-spans (parse-terminal-spans raw))
  (define token-spans (regexp-match-positions* #px"[^[:space:]]+" surface))
  (for/list ([span (in-list token-spans)])
    (unless (for/or ([terminal (in-list terminal-spans)])
              (spans-overlap? span terminal))
      (error 'parse-case-tokens
             "surface token ~s has no terminal in the stored gentufa parse"
             (substring surface (car span) (cdr span))))
    (substring surface (car span) (cdr span))))

(define (rr-fields-value rr)
  (cond [(rr-case? rr) (rr-case-fields rr)]
        [(hash? rr) rr]
        [else #f]))

(define (missing-rr-fields fields)
  (if fields
      (filter (lambda (name) (not (hash-has-key? fields name))) rr-field-names)
      rr-field-names))

(define (typed-lowered datum rules [inv (load-inventory)])
  (with-handlers
      ([exn:fail?
        (lambda (exception)
          (no-lowering (if (null? rules) "M3" (last rules))
                       'implementation
                       "produced core term does not type-check"
                       (exn-message exception)))])
    (define ast (datum->core datum))
    (define typed (infer-core ast (hash) inv))
    (if (null? (typing-gaps typed))
        (lowered ast rules)
        (no-lowering (if (null? rules) "M3" (last rules))
                     'implementation
                     "produced core term has unresolved typing gaps"
                     (typing-gaps typed)))))

(define (unstress text)
  (list->string
   (filter (lambda (character) (not (char=? character #\u0301)))
           (string->list (string-normalize-nfd text)))))

(define (gentufa-terminals value)
  (define found '())
  (define (walk node [kind #f])
    (cond
      [(hash? node)
       (if (and kind (hash-has-key? node 'phonemes)
                (hash-has-key? node 'span))
           (match (hash-ref node 'span)
             [(list start stop)
              (set! found
                    (cons (gentufa-terminal
                           kind (unstress (hash-ref node 'phonemes)) start stop)
                          found))]
             [_ (void)])
           (for ([(key child) (in-hash node)]) (walk child key)))]
      [(list? node) (for ([child (in-list node)]) (walk child kind))]
      [else (void)]))
  (walk value)
  (sort (remove-duplicates found) < #:key gentufa-terminal-start))

(define (tag-values value wanted)
  (define found '())
  (define (walk node)
    (cond
      [(hash? node)
       (for ([(key child) (in-hash node)])
         (when (eq? key wanted) (set! found (cons child found)))
         (walk child))]
      [(list? node) (for ([child (in-list node)]) (walk child))]
      [else (void)]))
  (walk value)
  (reverse found))

(define (first-tag value wanted)
  (define values (tag-values value wanted))
  (and (pair? values) (first values)))

(define (has-tag? value wanted)
  (pair? (tag-values value wanted)))

(define (terminal-texts value [kind #f])
  (for/list ([terminal (in-list (gentufa-terminals value))]
             #:when (or (not kind) (eq? kind (gentufa-terminal-kind terminal))))
    (gentufa-terminal-text terminal)))

(define (terminal-signatures value)
  (for/list ([terminal (in-list (gentufa-terminals value))])
    (list (gentufa-terminal-kind terminal)
          (gentufa-terminal-text terminal)
          (gentufa-terminal-start terminal)
          (gentufa-terminal-stop terminal))))

(define (first-terminal value kind)
  (define found (terminal-texts value kind))
  (and (pair? found) (first found)))

(define number-values
  (hash "no" 0 "pa" 1 "re" 2 "ci" 3 "vo" 4 "mu" 5
        "xa" 6 "ze" 7 "bi" 8 "so" 9))

(define reference-values
  (hash "mi" 'Speaker "do" 'Audience "ti" 'This "ta" 'That "tu" 'Yonder))

(define sumti-semantic-tags
  (seteq 'ProSumti 'NameSumti 'LaheSumti
         'DescriptorWithGadriSumti 'DescriptorWithoutGadriSumti))

(define term-semantic-tags
  (set-add sumti-semantic-tags 'PlaceTaggedSumtiTerm))

;; These are grammar-only wrappers on the direct path from a connected term
;; (or a LAhE inner sumti) to its first semantic construct. A handler may look
;; through these wrappers, but never through an unrecognized node merely
;; because a familiar descendant and the same terminal multiset remain.
(define transparent-term-path-keys
  (seteq 'ConnectedTerm 'leading_term 'SumtiTerm 'Sumti 'sumti
         'base_sumti 'leading_sumti 'SimpleSumti 'SumtiBase 'inner_sumti))

(define bridi-semantic-tags (seteq 'BridiWithLeadingTerms 'RelationOnlyBridi))
(define transparent-bridi-path-keys
  (seteq 'BridiStatement 'bridi 'StatementBase 'StatementOrFragmentStatement
         'leading_statement 'trailing_statement))
(define tail-semantic-tags (seteq 'SelbriSimpleBridiTail))
(define transparent-tail-path-keys
  (seteq 'bridi_tail 'BridiTailWithPossibleTailTerms 'first))
(define root-semantic-tags
  (seteq 'IStatementConnection 'BridiStatement 'FragmentStatement))
(define transparent-root-path-keys
  (seteq 'RegularText 'paragraphs 'TextParagraphWithAdditionalNiho 'first
         'SimpleParagraph 'initial 'StatementOrFragmentStatement
         'StatementBase))
(define joi-semantic-tags (seteq 'JoiConnective))
(define transparent-joi-path-keys
  (seteq 'ConnectedTerm 'leading_term 'SumtiTerm 'base_sumti 'leading_sumti
         'continuations 'connective 'JoikConnective))
(define fahu-operand-path-keys
  (seteq 'ConnectedTerm 'leading_term 'SumtiTerm 'base_sumti 'leading_sumti
         'continuations 'sumti 'SimpleSumti 'SumtiBase))
(define termset-descriptor-path-keys
  (seteq 'ConnectedTerm 'leading_term 'SumtiTerm 'base_sumti 'leading_sumti
         'continuations 'sumti 'SimpleSumti 'SumtiBase))
(define termset-connective-path-keys
  (seteq 'ConnectedTerm 'leading_term 'SumtiTerm 'base_sumti 'leading_sumti
         'continuations 'connective))
(define connection-tail-tags (seteq 'SimpleIConnectiveStatementTail))
(define transparent-connection-tail-keys (seteq 'continuations))
(define jek-tags (seteq 'JekConnective))
(define transparent-jek-path-keys
  (seteq 'IStandardStatementConnective 'connective))
(define fragment-tags (seteq 'TermsFragment))
(define transparent-fragment-path-keys (seteq 'FragmentStatement))
(define supported-special-connective-keys
  (seteq 'joi 'cehe 'ja 'Plain 'PlainWord 'Cmavo 'phonemes 'span))
(define supported-selbri-keys
  (seteq 'UntaggedSelbri 'CoSelbri 'leading_selbri 'additional_units
         'first_unit 'first 'LinkedTanruUnit 'base 'WordTanruUnit
         'TanruUnitAtom 'conversions 'ScalarNegatedTanruUnit 'nahe
         'inner_unit 'inner_selbri 'NegatedSelbri 'na 'GohaWordTanruUnit
         'Plain 'PlainWord 'Gismu 'Cmavo 'phonemes 'span))
(define transparent-terminal-path-keys (seteq 'Plain 'PlainWord))
(define transparent-number-terminal-path-keys
  (seteq 'PaRunQuantifier 'number 'first_number 'Plain 'PlainWord))
(define description-tail-tags
  (seteq 'RelationDescriptionTail 'QuantifierRelationDescriptionTail))

(define (unrecognized-hash-keys value supported)
  (define found (mutable-set))
  (define (walk node)
    (cond
      [(hash? node)
       (for ([(key child) (in-hash node)])
         (unless (set-member? supported key) (set-add! found key))
         (walk child))]
      [(list? node) (for ([child (in-list node)]) (walk child))]
      [else (void)]))
  (walk value)
  (sort (set->list found) symbol<?))

(define (unrecognized-direct-keys value supported)
  (if (hash? value)
      (sort (filter (lambda (key) (not (set-member? supported key)))
                    (hash-keys value))
            symbol<?)
      '(not-a-hash)))

(define (decode-terminal-leaf subtree kind rule
                              [transparent transparent-terminal-path-keys])
  (define direct
    (direct-semantic-node subtree (seteq kind) rule transparent))
  (cond
    [(no-lowering? direct) direct]
    [else
     (define payload (second direct))
     (define unknown
       (unrecognized-direct-keys payload (seteq 'phonemes 'span)))
     (define phonemes (and (hash? payload) (hash-ref payload 'phonemes #f)))
     (define span (and (hash? payload) (hash-ref payload 'span #f)))
     (if (and (null? unknown) (string? phonemes)
              (match span [(list (? exact-nonnegative-integer?)
                                 (? exact-nonnegative-integer?)) #t]
                          [_ #f]))
         (unstress phonemes)
         (no-lowering rule 'rule-underspecified
                      "terminal leaf has an unknown or malformed child"
                      (hasheq 'kind kind 'unknown unknown
                              'phonemes phonemes 'span span)))]))

(define (decode-simple-selbri subtree rule)
  (define decoded (selbri-view subtree))
  (cond
    [(no-lowering? decoded) decoded]
    [else
     (define residue
       (filter values
               (list (and (hash-ref decoded 'tanru #f) 'tanru)
                     (and (hash-ref decoded 'conversion #f) 'conversion)
                     (and (hash-ref decoded 'scalar #f) 'scalar)
                     (and (hash-ref decoded 'negated #f) 'negated))))
     (if (null? residue)
         (hash-ref decoded 'relation)
         (no-lowering rule 'rule-underspecified
                      "descriptor relation child has unconsumed modifiers"
                      residue))]))

(define (semantic-node-candidates subtree semantic-tags)
  (define candidates '())
  (define (walk node path)
    (cond
      [(hash? node)
       (for ([(key child) (in-hash node)])
         (define next-path (append path (list key)))
         (if (set-member? semantic-tags key)
             (set! candidates (cons (list key child path) candidates))
             (walk child next-path)))]
      [(list? node) (for ([child (in-list node)]) (walk child path))]
      [else (void)]))
  (walk subtree '())
  (reverse candidates))

(define (unrecognized-semantic-path-keys candidates transparent-keys)
  (remove-duplicates
   (append-map
    (lambda (candidate)
      (filter (lambda (key) (not (set-member? transparent-keys key)))
              (third candidate)))
    candidates)))

(define (direct-semantic-node subtree semantic-tags rule
                              [transparent-keys transparent-term-path-keys])
  (define candidates (semantic-node-candidates subtree semantic-tags))
  (cond
    [(not (= (length candidates) 1))
     (no-lowering rule 'rule-underspecified
                  "term does not have exactly one direct semantic construct"
                  (map (lambda (candidate)
                         (list (first candidate) (third candidate)))
                       candidates))]
    [else
     (define candidate (first candidates))
     (define path (third candidate))
     (define unrecognized
       (unrecognized-semantic-path-keys candidates transparent-keys))
     (if (null? unrecognized)
         candidate
         (no-lowering rule 'rule-underspecified
                      "semantic construct is nested under an unknown wrapper"
                      (hasheq 'path path 'unknown unrecognized)))]))

(define (rr-value fields name)
  (hash-ref fields name (lambda () '())))

(define (rr-has? fields name value)
  (member value (rr-value fields name)))

(define (same-members? left right)
  (and (= (length left) (length right))
       (for/and ([item (in-list left)])
         (= (count (lambda (candidate) (equal? candidate item)) left)
            (count (lambda (candidate) (equal? candidate item)) right)))))

(define (require-readings fields expected rule)
  (define actual (rr-value fields 'readings))
  (if (same-members? actual expected)
      #t
      (no-lowering rule 'rr-missing
                   "RR.readings does not exactly select this lowering path"
                   (hasheq 'expected expected 'actual actual))))

(define (require-rows fields expected rule)
  (define actual (rr-value fields 'rows))
  (define wanted (remove-duplicates expected))
  (if (same-members? actual wanted)
      #t
      (no-lowering rule 'rr-missing
                   "RR.rows does not exactly select every lexical row used"
                   (hasheq 'expected wanted 'actual actual))))

(define (require-row-present fields relation rule)
  (if (member relation (rr-value fields 'rows))
      #t
      (no-lowering rule 'rr-missing
                   "RR.rows omits a lexical row used by the parse"
                   relation)))

(define (require-sites fields expected rule)
  (define actual (rr-value fields 'sites))
  (if (equal? actual expected)
      #t
      (no-lowering rule 'rr-missing
                   "RR.sites kind/order/dependencies do not match the rule"
                   (hasheq 'expected expected 'actual actual))))

(define (first-failure . checks)
  (findf no-lowering? checks))

(define (require-empty-resolution-fields fields rule)
  (define unexpected
    (for/list ([name (in-list '(attach stores anaphora))]
               #:when (pair? (rr-value fields name)))
      (cons name (rr-value fields name))))
  (if (null? unexpected)
      #t
      (no-lowering rule 'rr-missing
                   "this M3 path has no consumer for nonempty RR fields"
                   unexpected)))

(define (parsed-relation subtree)
  (define gismu (remove-duplicates (terminal-texts subtree 'Gismu)))
  (cond [(pair? gismu) (string->symbol (last gismu))]
        [(member "co'e" (terminal-texts subtree 'Cmavo)) '|co'e|]
        [else #f]))

(define (sumti-view subtree)
  (define direct (direct-semantic-node subtree sumti-semantic-tags "M3"))
  (define tag (and (list? direct) (first direct)))
  (define node (and (list? direct) (second direct)))
  (cond
    [(no-lowering? direct) direct]
    [(eq? tag 'LaheSumti)
     (define unknown
       (unrecognized-direct-keys node (seteq 'lahe 'inner_sumti)))
     (define op
       (if (null? unknown)
           (decode-terminal-leaf (hash-ref node 'lahe) 'Cmavo "L3.14")
           (no-lowering "L3.14" 'rule-underspecified
                        "LAhE node has an unknown direct child" unknown)))
     (define inner (sumti-view (hash-ref node 'inner_sumti)))
     (cond [(no-lowering? op) op]
           [(no-lowering? inner) inner]
           [else `(lahe ,op ,inner)])]
    [(eq? tag 'DescriptorWithGadriSumti)
     (define descriptor node)
     (cond
       [(or (has-tag? descriptor 'RestrictiveBridiRelativeClause)
            (has-tag? descriptor 'NonrestrictiveBridiRelativeClause)
            (has-tag? descriptor 'RelativeClause))
       (no-lowering "L4" 'out-of-fragment
                     "relative-clause description is outside F₀-M3"
                     (terminal-texts descriptor))]
       [else
        (define descriptor-unknown
          (unrecognized-direct-keys descriptor (seteq 'description 'tail)))
        (define gadri
          (if (null? descriptor-unknown)
              (decode-terminal-leaf (hash-ref descriptor 'description)
                                    'Cmavo "L3.1")
              (no-lowering "L3.1" 'rule-underspecified
                           "descriptor has an unknown direct child"
                           descriptor-unknown)))
        (define tail-container (hash-ref descriptor 'tail))
        (define tail-container-unknown
          (unrecognized-direct-keys tail-container
                                    (seteq 'leading_tail_elements 'tail)))
        (define leading
          (hash-ref tail-container 'leading_tail_elements (lambda () #hasheq())))
        (define direct-tail
          (if (null? tail-container-unknown)
              (direct-semantic-node (hash-ref tail-container 'tail)
                                    description-tail-tags "L3.1" (seteq))
              (no-lowering "L3.1" 'rule-underspecified
                           "description tail has an unknown direct child"
                           tail-container-unknown)))
        (define tail-node (and (list? direct-tail) (second direct-tail)))
        (define tail-unknown
          (if tail-node
              (unrecognized-direct-keys tail-node (seteq 'quantifier 'selbri))
              '()))
        (define quantifier-node
          (and tail-node (hash-ref tail-node 'quantifier (lambda () #f))))
        (define quantifier-word
          (and quantifier-node
               (decode-terminal-leaf quantifier-node 'Cmavo "L3.9"
                                     transparent-number-terminal-path-keys)))
        (define count
          (and (string? quantifier-word)
               (hash-ref number-values quantifier-word #f)))
        (define relation
          (and tail-node (null? tail-unknown)
               (decode-simple-selbri (hash-ref tail-node 'selbri) "L3.1")))
        (cond
          [(no-lowering? gadri) gadri]
          [(no-lowering? direct-tail) direct-tail]
          [(pair? tail-unknown)
           (no-lowering "L3.1" 'rule-underspecified
                        "description relation tail has an unknown child"
                        tail-unknown)]
          [(no-lowering? quantifier-word) quantifier-word]
          [(no-lowering? relation) relation]
          [(and (hash? leading) (positive? (hash-count leading)))
           (no-lowering "L3.11" 'rule-underspecified
                        "description has unimplemented leading semantic children"
                        (terminal-texts leading))]
          [else `(description ,gadri ,relation ,count)])])]
    [(eq? tag 'DescriptorWithoutGadriSumti)
     (define quantified node)
     (define unknown
       (unrecognized-direct-keys quantified (seteq 'quantifier 'selbri)))
     (define quantifier-node (hash-ref quantified 'quantifier))
     (define q-word
       (if (null? unknown)
           (decode-terminal-leaf quantifier-node 'Cmavo "L5.2"
                                 transparent-number-terminal-path-keys)
           (no-lowering "L5.2" 'rule-underspecified
                        "quantified sumti has an unknown direct child" unknown)))
     (define relation
       (and (not (no-lowering? q-word))
            (decode-simple-selbri (hash-ref quantified 'selbri) "L5.2")))
     (define quantity
       (and (string? q-word) (hash-ref number-values q-word q-word)))
     (cond [(no-lowering? q-word) q-word]
           [(no-lowering? relation) relation]
           [else `(quantifier ,quantity ,relation)])]
    [(eq? tag 'NameSumti)
     (define named node)
     (define unknown (unrecognized-direct-keys named (seteq 'la 'names)))
     (define la-word
       (if (null? unknown)
           (decode-terminal-leaf (hash-ref named 'la) 'Cmavo "L3.3")
           (no-lowering "L3.3" 'rule-underspecified
                        "name sumti has an unknown direct child" unknown)))
     (define name-nodes (hash-ref named 'names (lambda () '())))
     (define decoded-names
       (if (list? name-nodes)
           (map (lambda (name-node)
                  (decode-terminal-leaf name-node 'Cmevla "L3.3"))
                name-nodes)
           (list (no-lowering "L3.3" 'rule-underspecified
                              "name list is malformed" name-nodes))))
     (define failure (or (and (no-lowering? la-word) la-word)
                         (findf no-lowering? decoded-names)))
     (cond [failure failure]
           [(and (equal? la-word "la") (= (length decoded-names) 1))
            `(name ,(first decoded-names))]
           [else (no-lowering "L3.3" 'rule-underspecified
                              "name sumti requires la and one name"
                              (hasheq 'la la-word 'names decoded-names))])]
    [(eq? tag 'ProSumti)
     (define pro node)
     (define word (decode-terminal-leaf pro 'Cmavo "L1.4"))
     (if (no-lowering? word) word
         (let ([word word])
           (cond [(hash-ref reference-values word #f)
                  => (lambda (value) `(value ,value))]
                 [(equal? word "zi'o") '(deleted)]
                 [else (no-lowering "L1.4" 'rule-underspecified
                                    "unsupported parsed pro-sumti" word)])))]
    [else
     (no-lowering "M3" 'out-of-fragment
                  "unsupported gentufa sumti construct"
                  (sort (set->list (parse-case-variants
                                    (hasheq 'parse subtree 'surface "")))
                        symbol<?))]))

(define (term-view connected-term)
  (cond
    [(member "fa'u" (terminal-texts connected-term 'Cmavo))
     (define direct-joi
       (direct-semantic-node connected-term joi-semantic-tags "L5.21"
                             transparent-joi-path-keys))
     (define unknown-joi-keys
       (if (list? direct-joi)
           (unrecognized-hash-keys (second direct-joi)
                                   supported-special-connective-keys)
           '()))
     (define operand-candidates
       (semantic-node-candidates connected-term sumti-semantic-tags))
     (define unknown-operand-paths
       (unrecognized-semantic-path-keys operand-candidates
                                        fahu-operand-path-keys))
     (define ordered-operands
       (sort operand-candidates <
             #:key (lambda (candidate)
                     (define terminals (gentufa-terminals (second candidate)))
                     (if (null? terminals) +inf.0
                         (gentufa-terminal-start (first terminals))))))
     (define decoded-operands
       (for/list ([candidate (in-list ordered-operands)])
         (sumti-view (hasheq (first candidate) (second candidate)))))
     (define operand-values
       (for/list ([operand (in-list decoded-operands)])
         (match operand [`(value ,value) value] [_ #f])))
     (define accounted-terminals
       (append (if (list? direct-joi)
                   (terminal-signatures (second direct-joi)) '())
               (append-map (lambda (candidate)
                             (terminal-signatures (second candidate)))
                           ordered-operands)))
     (cond [(no-lowering? direct-joi) direct-joi]
           [(pair? unknown-joi-keys)
            (no-lowering "L5.21" 'rule-underspecified
                         "fa'u connective has an unknown inner wrapper"
                         unknown-joi-keys)]
           [(pair? unknown-operand-paths)
            (no-lowering "L5.21" 'rule-underspecified
                         "fa'u operand is nested under an unknown wrapper"
                         unknown-operand-paths)]
           [(findf no-lowering? decoded-operands)
            => values]
           [(not (same-members? (terminal-signatures connected-term)
                                accounted-terminals))
            (no-lowering "L5.21" 'rule-underspecified
                         "fa'u has unconsumed child terminals"
                         (hasheq 'all (terminal-signatures connected-term)
                                 'accounted accounted-terminals))]
           [(and (= (length operand-values) 2)
                 (not (member #f operand-values)))
            `(zip-values ,operand-values)]
           [else
            (no-lowering "L5.21" 'rule-underspecified
                         "fa'u requires exactly two decoded referential operands"
                         decoded-operands)])]
    [else
     (define direct
       (direct-semantic-node connected-term term-semantic-tags "L1.4"))
     (cond
       [(no-lowering? direct) direct]
       [(eq? (first direct) 'PlaceTaggedSumtiTerm)
        (define node (second direct))
        (define fa
          (decode-terminal-leaf (hash-ref node 'fa) 'Cmavo "L1.4"))
        (define label (hash "fa" 1 "fe" 2 "fi" 3 "fo" 4 "fu" 5))
        (define sumti (sumti-view (hash-ref node 'sumti)))
        (define accounted
          (append (terminal-signatures (hash-ref node 'fa))
                  (terminal-signatures (hash-ref node 'sumti))))
        (cond [(no-lowering? fa) fa]
              [(no-lowering? sumti) sumti]
              [(not (and fa (hash-has-key? label fa)
                         (same-members? (terminal-signatures node)
                                        accounted)))
               (no-lowering "L1.4" 'rule-underspecified
                            "FA term has unconsumed semantic children"
                            (terminal-texts node))]
              [else `(label ,(hash-ref label fa) ,sumti)])]
       [else
        (sumti-view (hasheq (first direct) (second direct)))])]))

(define (selbri-view subtree)
  (define unknown-keys
    (unrecognized-hash-keys subtree supported-selbri-keys))
  (define relation (parsed-relation subtree))
  (define gismu (remove-duplicates (terminal-texts subtree 'Gismu)))
  (define cmavo (terminal-texts subtree 'Cmavo))
  (define conversion-words
    (filter (lambda (word) (member word '("se" "te" "ve" "xe"))) cmavo))
  (define scalar-word
    (findf (lambda (word) (member word '("na'e" "to'e" "no'e"))) cmavo))
  (define negated? (has-tag? subtree 'NegatedSelbri))
  (define expected-cmavo
    (append conversion-words
            (if scalar-word (list scalar-word) '())
            (if negated? '("na") '())
            (if (equal? relation '|co'e|) '("co'e") '())))
  (cond
    [(pair? unknown-keys)
     (no-lowering "L1.1" 'rule-underspecified
                  "selbri contains an unknown grammar wrapper"
                  unknown-keys)]
    [(not relation)
     (no-lowering "L1.1" 'rule-underspecified
                  "selbri parse has no supported lexical relation" cmavo)]
    [(> (length gismu) 2)
     (no-lowering "L1.10" 'rule-underspecified
                  "selbri has an unsupported relation composition" gismu)]
    [(not (same-members? cmavo expected-cmavo))
     (no-lowering "L1.1" 'rule-underspecified
                  "selbri contains unconsumed cmavo" cmavo)]
    [(or (> (length conversion-words) 1)
         (and (pair? conversion-words)
              (not (equal? conversion-words '("se")))))
     (no-lowering "L1.4" 'rule-underspecified
                  "only one se conversion is mechanically implemented"
                  conversion-words)]
    [(and scalar-word (or negated? (pair? conversion-words)))
     (no-lowering "L5.11" 'rule-underspecified
                  "combined scalar, negation, or conversion is unimplemented"
                  cmavo)]
    [else
     (hasheq 'relation relation
             'tanru (and (>= (length gismu) 2)
                         (map string->symbol (take-right gismu 2)))
             'conversion (and (equal? conversion-words '("se")) 'se)
             'scalar (and (has-tag? subtree 'ScalarNegatedTanruUnit)
                          (cond [(equal? scalar-word "na'e") 'OtherThan]
                                [(equal? scalar-word "to'e") 'Opposite]
                                [(equal? scalar-word "no'e") 'Neutral]
                                [else #f]))
             'negated negated?)]))

(define (collect-bridi-terms bridi tail)
  (define leading (hash-ref bridi 'leading_terms (lambda () '())))
  (define trailing (if tail (hash-ref tail 'terms (lambda () '())) '()))
  (append leading trailing))

(define (termset-views term-node)
  (define descriptors (tag-values term-node 'DescriptorWithoutGadriSumti))
  (define connectives (tag-values term-node 'CeheConnective))
  (define descriptor-candidates
    (semantic-node-candidates term-node
                              (seteq 'DescriptorWithoutGadriSumti)))
  (define connective-candidates
    (semantic-node-candidates term-node (seteq 'CeheConnective)))
  (define unknown-paths
    (append
     (unrecognized-semantic-path-keys descriptor-candidates
                                      termset-descriptor-path-keys)
     (unrecognized-semantic-path-keys connective-candidates
                                      termset-connective-path-keys)))
  (define unknown-connective-keys
    (remove-duplicates
     (append-map
      (lambda (connective)
        (unrecognized-hash-keys connective
                                supported-special-connective-keys))
      connectives)))
  (define accounted
    (append
     (append-map terminal-signatures descriptors)
     (append-map terminal-signatures connectives)))
  (cond
    [(or (not (= (length descriptors) 2))
         (not (= (length connectives) 1))
         (pair? unknown-paths)
         (pair? unknown-connective-keys)
         (not (equal? (terminal-texts (first connectives) 'Cmavo) '("ce'e")))
         (not (same-members? (terminal-signatures term-node) accounted)))
     (no-lowering "L5.3" 'rule-underspecified
                  "termset has unconsumed or malformed semantic children"
                  (hasheq 'descriptors (length descriptors)
                          'connectives (map terminal-texts connectives)
                          'unknown-paths unknown-paths
                          'unknown-connective-keys unknown-connective-keys
                          'all (terminal-signatures term-node)
                          'accounted accounted))]
    [else
     (define views
       (for/list ([descriptor (in-list descriptors)])
         (sumti-view (hasheq 'DescriptorWithoutGadriSumti descriptor))))
     (or (findf no-lowering? views) views)]))

(define (bridi-view statement)
  (define direct-bridi
    (direct-semantic-node statement bridi-semantic-tags "L1.1"
                          transparent-bridi-path-keys))
  (if (no-lowering? direct-bridi)
      direct-bridi
      (let* ([bridi (second direct-bridi)]
             [tail-root (hash-ref bridi 'bridi_tail (lambda () bridi))]
             [direct-tail
              (direct-semantic-node tail-root tail-semantic-tags "L1.1"
                                    transparent-tail-path-keys)]
             [tail (and (list? direct-tail) (second direct-tail))]
             [selbri (and tail (selbri-view (hash-ref tail 'selbri)))])
        (if (or (not selbri) (no-lowering? selbri))
            (or (and (no-lowering? direct-tail) direct-tail)
                selbri (no-lowering "L1.1" 'rule-underspecified
                                    "bridi tail has no simple selbri" #f))
            (let* ([term-nodes (collect-bridi-terms bridi tail)]
                   [cu-node (hash-ref bridi 'cu (lambda () #f))]
                   [cu-word
                    (and cu-node
                         (decode-terminal-leaf cu-node 'Cmavo "L1.1"))]
                   [accounted-terminals
                    (append (terminal-signatures (hash-ref tail 'selbri))
                            (append-map terminal-signatures term-nodes)
                            (if cu-node (terminal-signatures cu-node) '()))])
              (cond
                [(no-lowering? cu-word) cu-word]
                [(and cu-word (not (equal? cu-word "cu")))
                 (no-lowering "L1.1" 'rule-underspecified
                              "bridi separator is not cu" cu-word)]
                [(not (same-members? (terminal-signatures bridi)
                                     accounted-terminals))
                 (no-lowering "L1.1" 'rule-underspecified
                              "bridi contains unconsumed direct terminals"
                              (hasheq 'all (terminal-signatures bridi)
                                      'accounted accounted-terminals))]
                [(and (= (length term-nodes) 1)
                      (has-tag? (first term-nodes) 'CeheConnective))
                 (define views (termset-views (first term-nodes)))
                 (if (no-lowering? views) views
                     (hasheq 'selbri selbri
                             'terms views
                             'termset #t))]
                [else
                 (define terms (map term-view term-nodes))
                 (if (ormap no-lowering? terms)
                     (findf no-lowering? terms)
                     (hasheq 'selbri selbri 'terms terms
                             'termset #f))]))))))

(define (force-from-rr fields [markers '()])
  (define force (rr-value fields 'force))
  (cond [(equal? force (cons 'assert markers)) 'assert]
        [(equal? force (cons 'mention markers)) 'mention]
        [else (no-lowering "L1.2" 'rr-missing
                           "RR.force must select exactly one supported consumer"
                           (hasheq 'expected-markers markers 'actual force))]))

(define (close-mode-from-rr fields [negated? #f] [connected? #f])
  (define readings (rr-value fields 'readings))
  (cond [(or negated? connected?)
         (if (member 'actual readings) 'actual
             (no-lowering "L1.3" 'rr-missing
                          "RR.readings lacks actual mode" readings))]
        [else 'shorthand]))

(define (validated-path fields rule readings rows sites
                        #:force? [force? #f]
                        #:force-markers [force-markers '()])
  (define checks
    (list (require-readings fields readings rule)
          (require-rows fields rows rule)
          (require-sites fields sites rule)
          (require-empty-resolution-fields fields rule)))
  (define failure (apply first-failure checks))
  (cond [failure failure]
        [force?
         (define force (force-from-rr fields force-markers))
         (if (no-lowering? force) force force)]
        [(null? (rr-value fields 'force)) #t]
        [else
         (no-lowering rule 'rr-missing
                      "RR.force is nonempty on a path with no force consumer"
                      (rr-value fields 'force))]))

(define (row-slot-type relation label inv)
  (define row (inventory-row inv relation))
  (and row (exact-positive-integer? label)
       (<= label (row-decl-total row))
       ;; The bounded fixture-row contract currently types every ordinary
       ;; lexical place as a referential Entity slot. The label and arity are
       ;; still resolved from the selected row, never from a predicate table.
       '(Referents Entity)))

(define (global-expected-sites predicate relation inv)
  (define expected (make-hash))
  (define failure #f)
  (for ([operand (in-list `((restrictor ,predicate) (nuclear ,relation)))])
    (match-define (list role row-name) operand)
    (define row (inventory-row inv row-name))
    (cond
      [(not row)
       (set! failure
             (no-lowering "L0.1" 'row-missing
                          "global-reading operand row is absent" row-name))]
      [else
       (for ([label (in-range 2 (add1 (row-decl-total row)))])
         (define key
           (string->symbol (format "~a-~a-~a" role row-name label)))
         (hash-set! expected key
                    (list role row-name label
                          (row-slot-type row-name label inv))))]))
  (or failure expected))

(define (bare-variable-dependency? dependency)
  (and (symbol? dependency)
       (string-prefix? (symbol->string dependency) "$")))

(define (stable-site-toposort sites)
  (let loop ([remaining sites] [ordered '()] [bound '()])
    (cond
      [(null? remaining) (reverse ordered)]
      [else
       (define ready
         (findf (lambda (site)
                  (andmap (lambda (dependency) (member dependency bound))
                          (hoist-site-deps site)))
                remaining))
       (if ready
           (loop (remove ready remaining)
                 (cons ready ordered)
                 (cons (hoist-site-key ready) bound))
           #f)])))

(define (global-hoist-source fields quantity predicate relation inv)
  (define checks
    (list (require-readings fields '(global-exact) "L5.2")
          (require-rows fields (list predicate relation) "L5.2")
          (require-empty-resolution-fields fields "L5.2")))
  (define basic-failure (apply first-failure checks))
  (cond
    [basic-failure basic-failure]
    [(pair? (rr-value fields 'force))
     (no-lowering "L5.2" 'rr-missing
                  "global reading has no force consumer"
                  (rr-value fields 'force))]
    [else
     (define expected (global-expected-sites predicate relation inv))
     (cond
       [(no-lowering? expected) expected]
       [else
        (define actual (rr-value fields 'sites))
        (define seen (mutable-set))
        (define parsed '())
        (define failure #f)
        (for ([entry (in-list actual)] [index (in-naturals)])
          (match entry
            [`(omit ,(? symbol? key) (deps ,(? list? deps)))
             (define member-dependencies
               (filter (lambda (dependency)
                         (match dependency
                           [`(member ,role)
                            (member role '(restrictor nuclear))]
                           [_ #f]))
                       deps))
             (define outer-dependencies
               (filter (lambda (dependency)
                         (match dependency
                           [`(outer ,(? bare-variable-dependency?)) #t]
                           [_ #f]))
                       deps))
             (define malformed-dependencies
               (filter (lambda (dependency)
                         (not (or (symbol? dependency)
                                  (member dependency member-dependencies)
                                  (member dependency outer-dependencies))))
                       deps))
             (define site-deps
               (filter (lambda (dependency)
                         (and (symbol? dependency)
                              (not (bare-variable-dependency? dependency))))
                       deps))
             (cond
               [(set-member? seen key)
                (set! failure
                      (no-lowering "L0.1" 'rr-missing
                                   "duplicate hoist-site identity" key))]
               [(not (hash-has-key? expected key))
                (set! failure
                      (no-lowering "L0.1" 'rr-missing
                                   "unknown hoist-site identity" key))]
               [(pair? member-dependencies)
                (set! failure
                      (no-lowering "L0.1" 'rr-missing
                                   "hoist site depends on a comprehension member"
                                   (list key member-dependencies)))]
               [(pair? outer-dependencies)
                (set! failure
                      (no-lowering
                       "L0.1" 'rule-underspecified
                       "outer-binder dependency needs environment threading"
                       (list key outer-dependencies)))]
               [(or (ormap bare-variable-dependency? deps)
                    (pair? malformed-dependencies))
                (set! failure
                      (no-lowering
                       "L0.1" 'rr-missing
                       "dependency identity needs a site, (member role), or (outer $var) namespace"
                       (list key deps)))]
               [else
                (set-add! seen key)
                (match-define (list operand row label type)
                  (hash-ref expected key))
                (set! parsed
                      (cons (hoist-site key operand row label type site-deps index)
                            parsed))])]
            [_
             (set! failure
                   (no-lowering "L0.1" 'rr-missing
                                "unsupported global-reading site record"
                                entry))]))
        (define sites (reverse parsed))
        (define declared-keys (map hoist-site-key sites))
        (define missing
          (filter (lambda (key) (not (member key declared-keys)))
                  (hash-keys expected)))
        (define unknown-dependencies
          (remove-duplicates
           (for*/list ([site (in-list sites)]
                       [dependency (in-list (hoist-site-deps site))]
                       #:unless (member dependency declared-keys))
             dependency)))
        (define ordered (and (not failure)
                             (null? missing)
                             (null? unknown-dependencies)
                             (stable-site-toposort sites)))
        (cond
          [failure failure]
          [(pair? missing)
           (no-lowering "L0.1" 'rr-missing
                        "RR.sites omits required pure-position sites"
                        missing)]
          [(pair? unknown-dependencies)
           (no-lowering "L0.1" 'rr-missing
                        "hoist site has an unknown dependency"
                        unknown-dependencies)]
          [(not ordered)
           (no-lowering "L0.1" 'rr-missing
                        "hoist-site dependency graph contains a cycle"
                        (map (lambda (site)
                               (list (hoist-site-key site)
                                     (hoist-site-deps site)))
                             sites))]
          [else
           `(cardinal global none ,quantity ,predicate ,relation
                      ((property restrictor ,predicate
                                 ,(row-decl-total (inventory-row inv predicate))
                                 ,(row-decl-event-mode
                                   (inventory-row inv predicate)))
                       (property nuclear ,relation
                                 ,(row-decl-total (inventory-row inv relation))
                                 ,(row-decl-event-mode
                                   (inventory-row inv relation))))
                      ,(for/list ([site (in-list ordered)])
                         `(site ,(hoist-site-key site)
                                ,(hoist-site-operand site)
                                ,(hoist-site-relation site)
                                ,(hoist-site-label site)
                                ,(hoist-site-type site)
                                (deps ,@(hoist-site-deps site)))))] )])]))

(define (ordinary-fills terms)
  (define next 1)
  (define fills (make-hash))
  (define deleted '())
  (define explicit-labels '())
  (define unsupported '())
  (for ([term (in-list terms)])
    (match term
      [`(label ,label (value ,value))
       (set! explicit-labels (cons label explicit-labels))
       (if (or (hash-has-key? fills label) (member label deleted))
           (set! unsupported (cons `(duplicate-label ,label) unsupported))
           (begin
             (hash-set! fills label value)
             (set! next (max next (add1 label)))))]
      [`(label ,label (deleted))
       (set! explicit-labels (cons label explicit-labels))
       (if (or (hash-has-key? fills label) (member label deleted))
           (set! unsupported (cons `(duplicate-label ,label) unsupported))
           (begin
             (set! deleted (cons label deleted))
             (set! next (max next (add1 label)))))]
      [`(value ,value)
       (let loop ()
         (when (or (hash-has-key? fills next) (member next deleted))
           (set! next (add1 next))
           (loop)))
       (hash-set! fills next value)
       (set! next (add1 next))]
      [`(deleted)
       (set! deleted (cons next deleted))
       (set! next (add1 next))]
      [_ (set! unsupported (cons term unsupported))]))
  (values fills (reverse deleted) (reverse unsupported)
          (reverse explicit-labels)))

(define (se-base-label label)
  (case label [(1) 2] [(2) 1] [else label]))

(define (route-place-map fills deleted conversion)
  (if (eq? conversion 'se)
      (values
       (for/hash ([(label value) (in-hash fills)])
         (values (se-base-label label) value))
       (map se-base-label deleted))
      (values fills deleted)))

(define (fill-arguments fills deleted total)
  (define live-labels
    (filter (lambda (label) (not (member label deleted)))
            (range 1 (add1 total))))
  (define filled-labels (sort (hash-keys fills) <))
  (define positional-prefix (take live-labels (min (length live-labels)
                                                    (length filled-labels))))
  (define positions
    (map (lambda (label) (index-of live-labels label)) filled-labels))
  (cond
    [(equal? filled-labels positional-prefix)
     (map (lambda (label) (hash-ref fills label)) filled-labels)]
    [(and (pair? positions)
          (andmap exact-nonnegative-integer? positions)
          (equal? positions
                  (range (first positions) (+ (first positions)
                                              (length positions)))))
     (cons (string->symbol (format ":~a" (first filled-labels)))
           (map (lambda (label) (hash-ref fills label)) filled-labels))]
    [else
     (append*
      (for/list ([label (in-list filled-labels)])
        (list (string->symbol (format ":~a" label))
              (hash-ref fills label))))]))

(define (application-source view fields inv)
  (define selbri (hash-ref view 'selbri))
  (define relation (hash-ref selbri 'relation))
  (define row-check (require-row-present fields relation "L1.1"))
  (if (no-lowering? row-check)
      row-check
      (let-values ([(surface-fills surface-deleted unsupported explicit-labels)
                    (ordinary-fills (hash-ref view 'terms))])
        (if (pair? unsupported)
            (no-lowering "L1.4" 'rule-underspecified
                         "parsed term cannot be placed without dropping it"
                         unsupported)
            (let-values ([(fills deleted)
                          (route-place-map
                           surface-fills surface-deleted
                           (hash-ref selbri 'conversion #f))])
        (define row (inventory-row inv relation))
        (if (not row)
            (no-lowering "L1.1" 'row-missing
                         "selected lexical row is absent" relation)
            (let* ([total (row-decl-total row)]
                   [bad-labels
                    (filter (lambda (label) (or (< label 1) (> label total)))
                            (append (hash-keys fills) deleted))]
                   [arguments (fill-arguments fills deleted total)]
                   [base
                    (cond
                      [(hash-ref selbri 'conversion #f)
                       `(route (application ,relation ,@arguments))]
                      [(pair? deleted)
                       `(drop ,relation ,deleted ,@arguments)]
                      [(not (equal? (sort (hash-keys fills) <)
                                    (range 1 (add1 (hash-count fills)))))
                       `(route (application ,relation ,@arguments))]
                      [(hash-ref selbri 'tanru #f)
                       (match-define (list modifier head)
                         (hash-ref selbri 'tanru))
                       `(tanru ,modifier ,head ,@arguments)]
                      [else `(pred ,relation ,@arguments)])]
                   [provided (+ (hash-count fills) (length deleted))])
              (cond
                [(pair? bad-labels)
                 (no-lowering "L1.4" 'rule-underspecified
                              "place label falls outside the selected row"
                              bad-labels)]
                [(and (hash-ref selbri 'conversion #f) (pair? deleted))
                 (no-lowering "L1.5" 'rule-underspecified
                              "combined conversion and place deletion is unimplemented"
                              deleted)]
                [(and (hash-ref selbri 'tanru #f)
                      (or (hash-ref selbri 'conversion #f)
                          (pair? deleted)
                          (pair? explicit-labels)))
                 (no-lowering "L1.10" 'rule-underspecified
                              "tanru combined with conversion, FA, or deletion is unimplemented"
                              (hasheq 'conversion
                                      (hash-ref selbri 'conversion #f)
                                      'labels explicit-labels
                                      'deleted deleted))]
                [else (if (< provided total) `(omit ,base) base)]))))))))

(define (view->sigma view category fields inv)
  (define selbri (hash-ref view 'selbri))
  (define relation (hash-ref selbri 'relation))
  (define negated? (hash-ref selbri 'negated))
  (define tanru (hash-ref selbri 'tanru #f))
  (define terms (hash-ref view 'terms))
  (define sentence? (eq? category 'sentence))
  (define (readings extras)
    (append (if sentence? '(actual) '()) extras))
  (define (force-or-none)
    (if sentence? (force-from-rr fields) 'none))
  (define view-shape
    (cond
      [(hash-ref view 'termset) 'termset]
      [(and (= (length terms) 2)
            (andmap (lambda (term)
                      (match term [`(zip-values ,(? list?)) #t] [_ #f]))
                    terms))
       'zip]
      [(and (= (length terms) 1)
            (match (first terms) [`(description ,_ ,_ ,_) #t] [_ #f]))
       'description]
      [(and (= (length terms) 1)
            (match (first terms) [`(name ,_) #t] [_ #f]))
       'name]
      [(and (= (length terms) 1)
            (match (first terms) [`(lahe ,_ ,_) #t] [_ #f]))
       'lahe]
      [(and (= (length terms) 1)
            (match (first terms) [`(quantifier ,_ ,_) #t] [_ #f]))
       'quantifier]
      [(hash-ref selbri 'scalar #f) 'scalar]
      [(equal? relation '|co'e|) 'cohe]
      [(member 'gradable (rr-value fields 'readings)) 'grade]
      [else 'ordinary]))
  (define active-modifiers
    (append (if tanru '(tanru) '())
            (if (hash-ref selbri 'conversion #f) '(conversion) '())
            (if (hash-ref selbri 'scalar #f) '(scalar) '())
            (if negated? '(negated) '())))
  (define allowed-modifiers
    (case view-shape
      [(ordinary) '(tanru conversion negated)]
      [(description) '(negated)]
      [(scalar) '(scalar)]
      [else '()]))
  (define modifier-residue
    (filter (lambda (modifier) (not (member modifier allowed-modifiers)))
            active-modifiers))
  (cond
    [(pair? modifier-residue)
     (define first-residue (first modifier-residue))
     (no-lowering
      (case first-residue
        [(tanru) "L1.10"] [(conversion) "L1.4"]
        [(scalar) "L5.11"] [(negated) "L5.9"])
      'rule-underspecified
      "parsed selbri modifier is not consumed by this view composition"
      (hasheq 'shape view-shape 'active active-modifiers
              'allowed allowed-modifiers 'residue modifier-residue))]
    [(and tanru
          (or (hash-ref view 'termset)
              (hash-ref selbri 'scalar #f)
              (member 'gradable (rr-value fields 'readings))
              (not (andmap (lambda (term)
                             (match term [`(value ,_) #t] [_ #f]))
                           terms))))
     (no-lowering "L1.10" 'rule-underspecified
                  "tanru has an unconsumed sibling modifier or term form"
                  (hasheq 'terms terms
                          'conversion (hash-ref selbri 'conversion #f)
                          'scalar (hash-ref selbri 'scalar #f)
                          'readings (rr-value fields 'readings)))]
    [(and (= (length terms) 2)
          (andmap (lambda (term)
                    (match term [`(zip-values ,(? list?)) #t] [_ #f]))
                  terms))
     (define check
       (validated-path fields "L5.21" (readings '(zip)) (list relation) '()
                       #:force? sentence?))
     (if (no-lowering? check) check
         (match* ((first terms) (second terms))
           [(`(zip-values ,left) `(zip-values ,right))
            (define source `(zip ,relation ,left ,right))
            (if sentence? `(force ,check ,source) source)]))]
    [(hash-ref view 'termset)
     (if (and (= (length terms) 2)
              (andmap (lambda (term)
                        (match term [`(quantifier ,(? number?) ,_) #t] [_ #f]))
                      terms))
         (match* ((first terms) (second terms))
           [(`(quantifier ,n1 ,p1) `(quantifier ,n2 ,p2))
            (define check
              (validated-path fields "L5.3" (readings '(full-product))
                              (list p1 p2 relation) '()
                              #:force? sentence?))
            (if (no-lowering? check) check
                `(termset ,(force-or-none) ,n1 ,p1 ,n2 ,p2 ,relation))])
         (no-lowering "L5.3" 'rule-underspecified
                      "termset shape is not mechanically supported" terms))]
    [(and (= (length terms) 1)
          (match (first terms) [`(description ,_ ,_ ,_) #t] [_ #f]))
     (match (first terms)
       [`(description ,gadri ,predicate ,count)
        (if count
            (no-lowering (if (zero? count) "L3.10" "L3.9")
                         'rule-underspecified
                         "inner description quantity is not implemented on this path"
                         (hasheq 'gadri gadri 'count count
                                 'predicate predicate))
            (case (string->symbol gadri)
          [(lo)
           (define check
             (validated-path fields "L3.1" (readings '())
                             (list predicate relation) '()
                             #:force? sentence?))
           (if (no-lowering? check) check
               `(lo ,predicate ,relation
                    ,(if negated? 'negative 'positive) ,(force-or-none)))]
          [(le)
           (define check
             (validated-path fields "L3.2" (readings '(le))
                             (list predicate relation 'skicu) '()
                             #:force? sentence?))
           (if (no-lowering? check) check
               `(le ,predicate
                    (description ,relation
                                 ,(if negated? 'negative 'positive)
                                 ,(force-or-none))))]
          [(|lo'i|)
           (no-lowering "L3.6" 'out-of-fragment
                        "lo'i bridi argument lowering is not implemented" terms)]
          [(|lo'e|)
           (define check
             (validated-path fields "L3.4" (readings '(typical))
                             (list predicate relation) '()
                             #:force? sentence?))
           (if (no-lowering? check) check
               (if sentence?
                   `(force ,check (generic ,predicate ,relation))
                   `(generic ,predicate ,relation)))]
              [else (no-lowering "L3.1" 'rule-underspecified
                                 "unsupported parsed gadri" gadri)]))])]
    [(and (= (length terms) 1)
          (match (first terms) [`(name ,_) #t] [_ #f]))
     (match-define `(name ,name) (first terms))
     (define check
       (validated-path fields "L3.3" (readings '(name)) (list relation) '()
                       #:force? sentence?))
     (if (no-lowering? check) check
         `(la ,name ,relation ,(force-or-none)))]
    [(and (= (length terms) 1)
          (match (first terms) [`(lahe ,_ ,_) #t] [_ #f]))
     (match (first terms)
       [`(lahe "lu'o" (description "le" ,predicate ,(? number? count)))
        (no-lowering "L3.14" 'rule-underspecified
                     "LAhE bridi argument lowering is not implemented"
                     (first terms))]
       [_ (no-lowering "L3.14" 'rule-underspecified
                       "unsupported LAhE parse" (first terms))])]
    [(and (= (length terms) 1)
          (match (first terms) [`(quantifier ,_ ,_) #t] [_ #f]))
     (match (first terms)
       [`(quantifier ,quantity ,predicate)
        (cond
          [(equal? quantity "ro")
           (define check
             (validated-path fields "L5.1" (readings '(importing))
                             (list predicate relation) '()
                             #:force? sentence?))
           (if (no-lowering? check) check
               (if sentence?
                   `(force ,check (every ,predicate ,relation))
                   `(every ,predicate ,relation)))]
          [(number? quantity)
           (if (member 'global-exact (rr-value fields 'readings))
               (global-hoist-source fields quantity predicate relation inv)
               (let ([check
                      (validated-path fields "L5.2"
                                      (readings '(witness-set))
                                      (list predicate relation) '()
                                      #:force? sentence?)])
                 (if (no-lowering? check) check
                     `(cardinal witness ,(force-or-none) ,quantity
                                ,predicate ,relation () ())))) ]
          [(equal? quantity "so'i")
           (define expected-sites `((threshold many (deps ()))))
           (define check
             (validated-path fields "L5.28" (readings '(many))
                             (list predicate relation) expected-sites
                             #:force? sentence?))
           (if (no-lowering? check) check
               `(threshold ,(force-or-none) many ,predicate ,relation))]
          [(equal? quantity "du'e")
           (define expected-sites
             `((purpose too-many (deps ()))
               (threshold too-many (deps (purpose)))))
           (define check
             (validated-path fields "L5.28" (readings '(too-many))
                             (list predicate relation) expected-sites
                             #:force? sentence?))
           (if (no-lowering? check) check
               `(threshold ,(force-or-none) too-many ,predicate ,relation))]
          [else (no-lowering "L5.2" 'rule-underspecified
                             "unsupported parsed quantity" quantity)])])]
    [else
     (cond
       [(and (hash-ref selbri 'tanru #f) (null? terms))
        (no-lowering "L1.10" 'rule-underspecified
                     "tanru parse has no resolved head-place fill" selbri)]
       [(hash-ref selbri 'scalar #f)
        (define expected-sites `((contrast-domain ,relation (deps ()))))
        (define check
          (validated-path fields "L5.11" (readings '(other-than))
                          (list relation) expected-sites #:force? sentence?))
        (if (no-lowering? check) check
            (if (not (= (length terms) 1))
            (no-lowering "L5.11" 'rr-missing
                         "scalar bridi must have exactly one argument" terms)
            (match (first terms)
              [`(value ,argument)
               `(scalar ,(force-or-none) ,(hash-ref selbri 'scalar)
                        ,relation ,argument)]
              [_ (no-lowering "L5.11" 'rule-underspecified
                              "unsupported scalar argument" (first terms))])))]
       [(equal? relation '|co'e|)
        (define check
          (validated-path fields "L1.8" (readings '(ellipsis)) '()
                          '((relation cohe (deps ()))) #:force? sentence?))
        (if (or (no-lowering? check) (not (= (length terms) 2)))
            (if (no-lowering? check) check
                (no-lowering "L1.8" 'rule-underspecified
                             "co'e requires exactly two placed arguments" terms))
            (let ([values
                   (for/list ([term (in-list terms)])
                     (match term [`(value ,value) value] [_ #f]))])
              (if (member #f values)
                  (no-lowering "L1.8" 'rule-underspecified
                               "co'e has an unsupported argument" terms)
                  `(cohe ,(force-or-none)
                         (Row (1 (Referents Entity)) (2 (Referents Entity)))
                         ,@values))))]
       [(member 'gradable (rr-value fields 'readings))
        (define expected-sites
          `((scale ,relation (deps ()))
            (cutoff ,relation (deps (scale)))))
        (define check
          (validated-path fields "L5.29" (readings '(gradable))
                          (list relation) expected-sites #:force? sentence?))
        (if (and (not (no-lowering? check)) (= (length terms) 1))
            (match (first terms)
              [`(value ,argument) `(grade ,(force-or-none) ,relation ,argument)]
              [_ (no-lowering "L5.29" 'rule-underspecified
                              "unsupported gradable argument" (first terms))])
            (if (no-lowering? check) check
                (no-lowering "L5.29" 'rule-underspecified
                             "gradable bridi requires exactly one argument"
                             terms)))]
       [else
        (define expected-rows
          (if tanru tanru (list relation)))
        (define expected-sites
          (if tanru
              `((tanru-link
                 ,(string->symbol
                   (format "~a-~a" (first tanru) (second tanru)))
                 (deps ())))
              '()))
        (define expected-readings (if sentence? '(actual) '()))
        (define check
          (validated-path fields "L1.1" expected-readings
                          expected-rows expected-sites #:force? sentence?))
        ;; Structural placement is checked before the RR agreement check so an
        ;; unconsumed parsed term is reported as the adapter defect it is,
        ;; rather than being masked by the extra row that term selected.
        (define placed (application-source view fields inv))
        (define app (if (no-lowering? placed) placed
                        (if (no-lowering? check) check placed)))
        (if (no-lowering? app) app
            (cond
              [(eq? category 'predication) app]
              [(eq? category 'selbri)
               (if (hash-ref selbri 'conversion #f)
                   `(route (se-lambda ,relation))
                   app)]
              [(eq? category 'content)
               (no-lowering "L5.21" 'out-of-fragment
                            "content-level connective lowering is not formed"
                            relation)]
              [else
               `(force ,check
                       (close ,(if negated? 'actual 'shorthand)
                              ,(if negated? `(na ,app) app)))]))])]))

(define (statement->sigma statement category fields inv)
  (define connection
    (and (hash? statement)
         (hash-ref statement 'IStatementConnection (lambda () #f))))
  (if connection
      (let* ([leading (hash-ref connection 'leading_statement)]
             [continuations (hash-ref connection 'continuations)]
             [direct-tail
              (and (= (length continuations) 1)
                   (direct-semantic-node
                    (first continuations) connection-tail-tags "L5.12"
                    transparent-connection-tail-keys))]
             [tail (and (list? direct-tail) (second direct-tail))])
        (if (or (not tail) (no-lowering? direct-tail))
            (or (and (no-lowering? direct-tail) direct-tail)
            (no-lowering "L5.12" 'rule-underspecified
                         "unsupported statement connection shape" connection))
            (let* ([left-view (bridi-view leading)]
                   [trailing (hash-ref tail 'trailing_statement)]
                   [connective (hash-ref tail 'connective)]
                   [i-node (hash-ref tail 'i (lambda () #f))]
                   [i-word
                    (if i-node
                        (decode-terminal-leaf i-node 'Cmavo "L5.12")
                        (no-lowering "L5.12" 'rule-underspecified
                                     "statement connection has no i separator"
                                     #f))]
                   [tail-unknown
                    (unrecognized-direct-keys
                     tail (seteq 'connective 'i 'trailing_statement))]
                   [direct-jek
                    (direct-semantic-node connective jek-tags "L5.12"
                                          transparent-jek-path-keys)]
                   [unknown-jek-keys
                    (if (list? direct-jek)
                        (unrecognized-hash-keys
                         (second direct-jek)
                         supported-special-connective-keys)
                        '())]
                   [right-view (bridi-view trailing)]
                   [tanru-connection?
                    (and (not (no-lowering? left-view))
                         (not (no-lowering? right-view))
                         (or (hash-ref (hash-ref left-view 'selbri) 'tanru #f)
                             (hash-ref (hash-ref right-view 'selbri)
                                       'tanru #f)))]
                   [connective-words (terminal-texts connective 'Cmavo)]
                   [jek (and (= (length connective-words) 1)
                             (first connective-words))]
                   [all-terminals (terminal-signatures connection)]
                   [separators
                    (filter (lambda (entry)
                              (match entry
                                [`(Cmavo "i" ,_ ,_) #t]
                                [_ #f]))
                            all-terminals)]
                   [accounted
                    (append (terminal-signatures leading)
                            (terminal-signatures trailing)
                            (terminal-signatures connective)
                            separators)]
                   [kind (cond [(equal? jek "je") 'and]
                               [(equal? jek "ja") 'or]
                               [else #f])])
              (if (or (no-lowering? left-view) (no-lowering? right-view)
                      (pair? tail-unknown)
                      (no-lowering? i-word) (not (equal? i-word "i"))
                      (no-lowering? direct-jek) (pair? unknown-jek-keys)
                      tanru-connection? (not kind)
                      (not (= (length separators) 1))
                      (not (same-members? all-terminals accounted)))
                  (or (and (no-lowering? left-view) left-view)
                      (and (no-lowering? right-view) right-view)
                      (and (no-lowering? i-word) i-word)
                      (and (not (no-lowering? i-word))
                           (not (equal? i-word "i"))
                           (no-lowering "L5.12" 'rule-underspecified
                                        "statement separator is not i" i-word))
                      (and (pair? tail-unknown)
                           (no-lowering
                            "L5.12" 'rule-underspecified
                            "statement tail has an unknown direct child"
                            tail-unknown))
                      (and (no-lowering? direct-jek) direct-jek)
                      (and tanru-connection?
                           (no-lowering
                            "L1.10" 'rule-underspecified
                            "tanru inside a sentence connection is unimplemented"
                            (list (and (not (no-lowering? left-view))
                                       (hash-ref (hash-ref left-view 'selbri)
                                                 'tanru #f))
                                  (and (not (no-lowering? right-view))
                                       (hash-ref (hash-ref right-view 'selbri)
                                                 'tanru #f)))))
                      (no-lowering "L5.12" 'rule-underspecified
                                   "statement connection has unconsumed children"
                                   (hasheq 'connective connective-words
                                           'unknown-connective-keys
                                           unknown-jek-keys
                                           'all all-terminals
                                           'accounted accounted)))
                  (let* ([left-relation
                          (hash-ref (hash-ref left-view 'selbri) 'relation)]
                         [right-relation
                          (hash-ref (hash-ref right-view 'selbri) 'relation)]
                         [check
                          (validated-path
                           fields "L5.12" '(actual)
                           (list left-relation right-relation) '()
                           #:force? #t #:force-markers '(connected))]
                         [left (if (no-lowering? check) check
                                   (application-source left-view fields inv))]
                         [right (if (no-lowering? check) check
                                    (application-source right-view fields inv))])
                    (if (or (no-lowering? left) (no-lowering? right))
                        (or (and (no-lowering? left) left)
                            (and (no-lowering? right) right)
                            check)
                        `(force ,check
                                (close actual
                                       (sentence-connect ,kind ,left ,right)))))))))
      (let ([view (bridi-view statement)])
        (if (no-lowering? view) view (view->sigma view category fields inv)))))

(define (fragment->sigma raw fields inv)
  (define direct-fragment
    (direct-semantic-node raw fragment-tags "M3"
                          transparent-fragment-path-keys))
  (if (no-lowering? direct-fragment)
      direct-fragment
      (let* ([fragment (second direct-fragment)]
             [terms (hash-ref fragment 'terms (lambda () #f))]
             [direct-terms?
              (and (list? terms)
                   (for/and ([term (in-list terms)])
                     (and (hash? term)
                          (= (hash-count term) 1)
                          (hash-has-key? term 'ConnectedTerm))))]
             [view (and direct-terms? (= (length terms) 1)
                        (term-view (first terms)))])
        (cond
          [(not direct-terms?)
           (no-lowering "M3" 'rule-underspecified
                        "terms fragment has an unknown direct term wrapper"
                        (and (list? terms)
                             (map (lambda (term)
                                    (and (hash? term) (hash-keys term)))
                                  terms)))]
          [(no-lowering? view) view]
          [(match view [`(description "lo'i" ,predicate ,count) #t] [_ #f])
           (match-define `(description "lo'i" ,predicate ,count) view)
           (if count
               (no-lowering (if (zero? count) "L3.10" "L3.9")
                            'rule-underspecified
                            "inner quantity on a collection fragment is unimplemented"
                            (hasheq 'count count 'predicate predicate))
               (let ([check
                      (validated-path fields "L3.6" '(lohi)
                                      (list predicate 'selcmi) '()
                                      #:force? #t)])
                 (if (no-lowering? check) check
                     (if (eq? check 'mention)
                         `(collection-set ,predicate)
                         (no-lowering "L3.6" 'rr-missing
                                      "lo'i utterance requires mention force"
                                      check)))))]
          [(match view [`(lahe "lu'o" (description "le" ,predicate ,count)) #t]
                       [_ #f])
           (match-define
             `(lahe "lu'o" (description "le" ,predicate ,count)) view)
           (define check
             (validated-path fields "L3.14" '(le inner-pa)
                             (list predicate 'skicu)
                             '((group-basis luho (deps ()))) #:force? #t))
           (if (no-lowering? check) check
               (if (eq? check 'mention)
                   `(luho ,count ,predicate)
                   (no-lowering "L3.14" 'rr-missing
                                "lu'o utterance requires mention force" check)))]
          [else (no-lowering "M3" 'out-of-fragment
                             "unsupported parsed terms fragment" view)]))))

(define (parse-case->sigma parse-case fields [inv (load-inventory)])
  (define raw (hash-ref parse-case 'parse))
  (define category (string->symbol (hash-ref parse-case 'category)))
  (define direct-root
    (direct-semantic-node raw root-semantic-tags "M3"
                          transparent-root-path-keys))
  (cond
    [(no-lowering? direct-root) direct-root]
    [(eq? (first direct-root) 'IStatementConnection)
     (statement->sigma
      (hasheq 'IStatementConnection (second direct-root)) category fields inv)]
    [(eq? (first direct-root) 'BridiStatement)
     (statement->sigma
      (hasheq 'BridiStatement (second direct-root)) category fields inv)]
    [(eq? (first direct-root) 'FragmentStatement)
     (fragment->sigma
      (hasheq 'FragmentStatement (second direct-root)) fields inv)]
    [else
     (no-lowering "M3" 'out-of-fragment
                  "gentufa parse has no supported statement root"
                  (sort (set->list (parse-case-variants parse-case)) symbol<?))]))

(define mutation-empty-deletion-pass-through-keys
  (seteq 'leading_tail_elements 'leading_terms 'terms 'conversions
         'additional_units 'continuations))
(define mutation-nonsemantic-deletion-pass-through-keys (seteq 'cu))

(define (internal-json-key-occurrences value)
  (define found '())
  (define (walk node path)
    (cond
      [(hash? node)
       (for ([(key child) (in-hash node)])
         (when (or (hash? child) (list? child))
           (set! found (cons (list path key child) found)))
         (walk child (append path (list (list 'key key)))))]
      [(list? node)
       (for ([child (in-list node)] [index (in-naturals)])
         (walk child (append path (list (list 'index index)))))]
      [else (void)]))
  (walk value '())
  (sort found string<?
        #:key (lambda (occurrence)
                (format "~s" (list (first occurrence)
                                    (second occurrence))))))

(define (mutate-json-key-at value parent-path wanted mode)
  (define (walk node path)
    (cond
      [(null? path)
       (unless (hash? node)
         (error 'mutate-json-key-at "target parent is not a hash"))
       (for/hasheq ([(key child) (in-hash node)]
                    #:unless (and (eq? mode 'delete) (eq? key wanted)))
         (values (if (and (eq? mode 'rename) (eq? key wanted))
                     'UnknownSweptWrapper key)
                 child))]
      [else
       (match (first path)
         [`(key ,key-step)
          (unless (hash? node)
            (error 'mutate-json-key-at "key path enters a non-hash"))
          (for/hasheq ([(key child) (in-hash node)])
            (values key (if (eq? key key-step)
                            (walk child (rest path)) child)))]
         [`(index ,index-step)
          (unless (list? node)
            (error 'mutate-json-key-at "index path enters a non-list"))
          (for/list ([child (in-list node)] [index (in-naturals)])
            (if (= index index-step) (walk child (rest path)) child))])]))
  (walk value parent-path))

(define (mutation-source-result parse-case fields inv raw)
  (with-handlers
      ([exn:fail?
        (lambda (exception)
          (no-lowering "M3" 'implementation
                       "mutated parse was structurally refused"
                       (exn-message exception)))])
    (parse-case->sigma (hash-set parse-case 'parse raw) fields inv)))

(define (run-parse-mutation-sweeps [manifest (load-lowering-manifest)]
                                   [inv (load-inventory)])
  (define wrapper-attempts 0)
  (define wrapper-allowlisted 0)
  (define deletion-attempts 0)
  (define failures '())
  (define (record! source ordinal index mode key baseline mutated expectation)
    (set! failures
          (cons (list (case-key source ordinal index) mode key expectation
                      baseline mutated)
                failures)))
  (for ([candidate (in-list (lowering-manifest-candidates manifest))])
    (define parse-cases (hash-ref (load-parse-fixture candidate) 'cases))
    (define rr-cases (rr-fixture-cases (load-rr-fixture candidate inv)))
    (for ([parse-case (in-list parse-cases)]
          [rr (in-list rr-cases)])
      (define raw (hash-ref parse-case 'parse))
      (when (hash? raw)
        (define fields (rr-case-fields rr))
        (define baseline (mutation-source-result parse-case fields inv raw))
        (for ([occurrence (in-list (internal-json-key-occurrences raw))])
          (match-define (list parent-path key child) occurrence)
          (define key-at-path (list key parent-path))
          (define rename-allowlisted? #f)
          (define deletion-allowlisted?
            (or (set-member? mutation-nonsemantic-deletion-pass-through-keys key)
                (and (set-member? mutation-empty-deletion-pass-through-keys key)
                     (or (and (hash? child) (zero? (hash-count child)))
                         (and (list? child) (null? child))))))
          (define renamed
            (mutation-source-result
             parse-case fields inv
             (mutate-json-key-at raw parent-path key 'rename)))
          (set! wrapper-attempts (add1 wrapper-attempts))
          (if rename-allowlisted?
              (begin
                (set! wrapper-allowlisted (add1 wrapper-allowlisted))
                (unless (equal? renamed baseline)
                  (record! (lowering-candidate-source candidate)
                           (lowering-candidate-ordinal candidate)
                           (hash-ref parse-case 'index) 'rename key-at-path
                           baseline renamed
                           'allowlisted-must-be-unchanged)))
              (unless (and (no-lowering? renamed)
                           (or (not (no-lowering? baseline))
                               (not (equal? renamed baseline))))
                (record! (lowering-candidate-source candidate)
                         (lowering-candidate-ordinal candidate)
                         (hash-ref parse-case 'index) 'rename key-at-path
                         baseline renamed
                         'unknown-wrapper-must-refuse)))
          (define deleted
            (mutation-source-result
             parse-case fields inv
             (mutate-json-key-at raw parent-path key 'delete)))
          (set! deletion-attempts (add1 deletion-attempts))
          (if deletion-allowlisted?
              (unless (equal? deleted baseline)
                (record! (lowering-candidate-source candidate)
                         (lowering-candidate-ordinal candidate)
                         (hash-ref parse-case 'index) 'delete key-at-path
                         baseline deleted
                         'allowlisted-empty-deletion-must-be-unchanged))
              (unless (or (no-lowering? deleted)
                          (not (equal? deleted baseline)))
                (record! (lowering-candidate-source candidate)
                         (lowering-candidate-ordinal candidate)
                         (hash-ref parse-case 'index) 'delete key-at-path
                         baseline deleted
                         'subtree-deletion-must-refuse-or-change)))))))
  (mutation-sweep-result wrapper-attempts wrapper-allowlisted
                         deletion-attempts (reverse failures)))

(define (rr->redex rr)
  (define fields (rr-fields-value rr))
  `(rr ,@(for/list ([name (in-list rr-field-names)])
           `(,name ,(hash-ref fields name (lambda () 'missing))))))

(define (parse-evidence parse-case)
  `(parse
    (tokens ,@(parse-case-tokens parse-case))
    (variants ,@(sort (set->list (parse-case-variants parse-case)) symbol<?))))

(define (derivation-rule-ids derivation)
  (append (if (derivation-name derivation)
              (list (derivation-name derivation)) '())
          (append-map derivation-rule-ids (derivation-subs derivation))))

(define (derivation-trace derivation)
  `(,(or (derivation-name derivation) 'unnamed)
    ,@(map derivation-trace (derivation-subs derivation))))

(define (typed-output-datum? datum [inv (load-inventory)])
  (with-handlers ([exn:fail? (lambda (_) #f)])
    (define result (infer-core (datum->core datum) (hash) inv))
    (null? (typing-gaps result))))

(define (derivable-outputs-type? rr-term sigma)
  (define input `(gentufa generated ,sigma))
  (define derivations (build-derivations (m3-lower ,rr-term ,input e_out)))
  (and (pair? derivations)
       (for/and ([derivation (in-list derivations)])
         (typed-output-datum? (fourth (derivation-term derivation))))))

(define (fixture-derivation-check rr sigma)
  (define rr-term (rr->redex rr))
  (derivable-outputs-type? rr-term sigma))

(define (generated-redex-check [attempts 20])
  (with-handlers
      ([exn:fail?
        (lambda (exception)
          (values 'unavailable 0 (exn-message exception)))])
    (define result
      (redex-check
       SmusniM3
       #:satisfying (m3-lower e_RR e_source e_output)
       (typed-output-datum? (term e_output))
       #:attempts attempts
       #:print? #f))
    (if (eq? result #t)
        (values 'passed attempts #f)
        (values 'counterexample attempts result))))

(define (redex-lower parse-case rr)
  (define sigma (parse-case->sigma parse-case (rr-fields-value rr)))
  (if (no-lowering? sigma)
      sigma
      (let* ([rr-term (rr->redex rr)]
             [input `(gentufa ,(parse-evidence parse-case) ,sigma)]
             [derivations (build-derivations (m3-lower ,rr-term ,input e_out))])
        (cond
          [(null? derivations)
           (no-lowering "M3" 'implementation
                        "Redex judgment has no derivation for parsed source view"
                        sigma)]
          [(not (= (length derivations) 1))
           (no-lowering
            "M3" 'implementation
            "Redex judgment has multiple derivations; attribution is ambiguous"
            (map derivation-trace derivations))]
          [else
           (define derivation (first derivations))
           (typed-lowered
            (fourth (derivation-term derivation))
            (remove-duplicates (derivation-rule-ids derivation)))]))))

(define (lower parse-case rr)
  (define fields (rr-fields-value rr))
  (define missing (missing-rr-fields fields))
  (cond
    [(pair? missing)
     (no-lowering "M3" 'rr-missing
                  "required RR fields are absent" missing)]
    [(not (hash? parse-case))
     (no-lowering "M3" 'implementation
                  "lower expects one parse-case JSON object" parse-case)]
    [(not (string? (hash-ref parse-case 'surface #f)))
     (no-lowering "M3" 'rule-underspecified
                  "candidate has no Lojban surface parse" #f)]
    [else
     (with-handlers
         ([exn:fail?
           (lambda (exception)
             (no-lowering "M3" 'implementation
                          "could not read gentufa parse case"
                          (exn-message exception)))])
       (redex-lower parse-case rr))]))

(define (core->plain node)
  (cond [(core-atom? node) (core-atom-value node)]
        [(core-list? node) (map core->plain (core-list-elements node))]
        [else node]))

(define (datum-head datum)
  (and (list? datum) (pair? datum) (symbol? (first datum)) (first datum)))

(define (label-symbol? value)
  (and (symbol? value)
       (string-prefix? (symbol->string value) ":")))

(define (numeric-label value)
  (and (label-symbol? value)
       (let ([text (substring (symbol->string value) 1)])
         (and (regexp-match? #px"^[1-9][0-9]*$" text)
              (string->number text)))))

(define (fill-map arguments total)
  (define result (make-hash))
  (define event #f)
  (let loop ([rest arguments] [next 1])
    (cond
      [(null? rest) (values result event)]
      [(and (pair? (cdr rest)) (label-symbol? (car rest)))
       (define label (car rest))
       (define value (cadr rest))
       (if (eq? label ':Eventuality)
           (set! event value)
           (let ([number (numeric-label label)])
             (when number (hash-set! result number value))))
       (loop (cddr rest) next)]
      [else
       (define available
         (for/first ([index (in-range next (add1 total))]
                     #:unless (hash-has-key? result index))
           index))
       (when available (hash-set! result available (car rest)))
       (loop (cdr rest) (if available (add1 available) next))])))

(define (binding-datum variable type computation body)
  `(Bind (,variable :: ,@type) ,computation ,body))

(define (wrap-contexts missing body)
  (for/fold ([result body]) ([entry (in-list (reverse missing))])
    (match-define (cons _label variable) entry)
    (binding-datum variable '(Referents Entity) '(Context) result)))

(define (expand-close-datum operand inv rr-rows)
  (define head (datum-head operand))
  (define row (and head (member head rr-rows) (inventory-row inv head)))
  (cond
    [(not row) (values `(Close ,operand) '())]
    [else
     (define total (row-decl-total row))
     (define-values (fills explicit-event) (fill-map (rest operand) total))
     (cond
       [explicit-event
        ;; The explicit-event case is already fully written at its use sites;
        ;; retain it rather than inventing a second display spelling.
       (values `(Close ,operand) '("Close explicit-event (§4.6/L1.3)"))]
       [else
        (define missing
          (let-values
              ([(entries _avoid)
                (for/fold ([entries '()] [avoid operand])
                          ([label (in-range 1 (add1 total))]
                           #:unless (hash-has-key? fills label))
                  (define variable
                    (variable-not-in
                     avoid (string->symbol (format "$ctx~a" label))))
                  (values (cons (cons label variable) entries)
                          (cons variable avoid)))])
            (reverse entries)))
        (for ([entry (in-list missing)])
          (hash-set! fills (car entry) (cdr entry)))
        (define event-variable
          (variable-not-in (cons (map cdr missing) operand) '$event))
        (define labelled-arguments
          (append*
           (for/list ([label (in-range 1 (add1 total))])
             (list (string->symbol (format ":~a" label))
                   (hash-ref fills label)))))
        (define application `(,head ,@labelled-arguments))
        (define expanded
          (case (row-decl-event-mode row)
            [(direct-event)
             `(CloseClause
               (ActualClause
                (λ (,event-variable :: Referents Eventuality)
                  ,(wrap-contexts
                    missing
                    `(,head ,@labelled-arguments :Eventuality ,event-variable)))))]
            [else
             (wrap-contexts
              missing
              `(CloseClause (ActualClause (StateClause ,application))))]))
        (values expanded
                (append '("Close (§4.6/L1.3)")
                        (if (null? missing)
                            '()
                            (list (format "~a omitted place~a (P15/L1.6)"
                                          (length missing)
                                          (if (= (length missing) 1) "" "s"))))))])]))

(define (plain-binder-parts binder)
  (define flat
    (if (and (= (length binder) 1) (list? (first binder)))
        (first binder)
        binder))
  (define separator (index-of flat '::))
  (and separator
       (list (filter symbol? (take flat separator))
             (drop flat (add1 separator)))))

(define (substitute-free-symbol datum old replacement)
  (define (walk value)
    (cond
      [(symbol? value) (if (eq? value old) replacement value)]
      [(not (list? value)) value]
      [else
       (match value
         [`(λ ,binder ,body)
          (define parts (and (list? binder) (plain-binder-parts binder)))
          `(λ ,binder
             ,(if (and parts (member old (first parts))) body (walk body)))]
         [`(Let ,binder ,rhs ,body)
          (define parts (and (list? binder) (plain-binder-parts binder)))
          `(Let ,binder ,(walk rhs)
             ,(if (and parts (member old (first parts))) body (walk body)))]
         [`(Bind . ,pieces)
          (define body (last pieces))
          (define alternating (drop-right pieces 1))
          (define shadowed? #f)
          (define rewritten
            (append*
             (for/list ([index (in-range 0 (length alternating) 2)])
               (define binder (list-ref alternating index))
               (define rhs (list-ref alternating (add1 index)))
               (define parts
                 (and (list? binder) (plain-binder-parts binder)))
               (define result (list binder (if shadowed? rhs (walk rhs))))
               (when (and parts (member old (first parts)))
                 (set! shadowed? #t))
               result)))
          `(Bind ,@rewritten ,(if shadowed? body (walk body)))]
         [_ (map walk value)])]))
  (walk datum))

(define (property-components datum)
  (match datum
    [`(λ ,(? list? binder) ,body)
     (define parts (plain-binder-parts binder))
     (and parts (= (length (first parts)) 1)
          (list (first (first parts)) (second parts) body))]
    [_ #f]))

(define effectful-definition-heads
  '(Context Vague Refer SelectExactly SelectAtLeast SelectSome SelectAllBut
            MaxRefer Bind Let Perform))

(define (syntactically-pure-definition-operand? datum)
  (define components (property-components datum))
  (and components
       (let pure? ([value (third components)])
         (cond
           [(not (list? value)) #t]
           [(member (datum-head value) effectful-definition-heads) #f]
           [else (andmap pure? value)]))))

(define (instantiate-property components member)
  (substitute-free-symbol (third components) (first components) member))

(define (expand-global-exactly-datum datum)
  (match datum
    [`(GlobalExactly ,count ,restrictor ,nuclear)
     (define p (property-components restrictor))
     (define q (property-components nuclear))
     (if (and p q (equal? (second p) (second q))
              (syntactically-pure-definition-operand? restrictor)
              (syntactically-pure-definition-operand? nuclear))
         (let* ([member
                 (variable-not-in datum '$global_member)]
                [binder `(,member :: ,@(second p))])
           `(= (Card
                (SetOf
                 (λ ,binder
                   (∧ ,(instantiate-property p member)
                      ,(instantiate-property q member)))))
               ,count))
         datum)]
    [_ datum]))

(define pure-position-heads
  '(SetOf SelectExactly SelectAtLeast SelectSome SelectAllBut
          Every No Exactly AtLeast Some AtMost MoreThan FewerThan
          GlobalExactly Most Generic Refer))

(define (lexical-property-lambda? datum inv)
  (match datum
    [`(λ ,_binder ,body)
     (define head (datum-head body))
     (and head (inventory-row inv head) body)]
    [_ #f]))

(define (reference-level-lambda? datum)
  (match datum
    [`(λ ,binder ,_body)
     (define flat (if (and (pair? binder) (list? (first binder)))
                      (first binder) binder))
     (define separator (index-of flat '::))
     (and separator
          (pair? (drop flat (add1 separator)))
          (eq? (list-ref flat (add1 separator)) 'Referents))]
    [_ #f]))

(define (normalize-datum datum inv rr-rows)
  (define expansions '())
  (define (note! text)
    (unless (member text expansions) (set! expansions (cons text expansions))))
  (define (walk value [parent #f] [operand-index #f])
    (cond
      [(not (list? value)) value]
      [else
       ;; Expand explicit §12 heads before descending into their operands.
       ;; Otherwise the generic pure-position display pass can rewrite an
       ;; operand in a way the already-expanded specimen never exposes.
       (define definition-expanded
         (case (datum-head value)
           [(GlobalExactly) (term (global-exactly-definition ,value))]
           [else value]))
       (if (not (equal? definition-expanded value))
           (begin
             (note! (case (datum-head value)
                      [(GlobalExactly) "§12 definition of `GlobalExactly`"]))
             (walk definition-expanded parent operand-index))
           (let ([walked
                  (for/list ([item (in-list value)] [index (in-naturals)])
                    (walk item (datum-head value) index))])
             (match walked
         [`(Close ,operand)
          (define-values (expanded fired) (expand-close-datum operand inv rr-rows))
          (for ([entry (in-list fired)]) (note! entry))
          expanded]
         [`(Assert ,content)
          (if (member (datum-head content) '(Close CloseClause))
              walked
              (begin
                (note! "force-boundary clause shorthand (§2)")
                `(Assert (CloseClause (ActualClause (StateClause ,content))))))]
         [else
          (define property
            (and parent (member parent pure-position-heads)
                 (not (and (eq? parent 'Refer)
                           (reference-level-lambda? walked)))
                 (lexical-property-lambda? walked inv)))
          (if property
              (match walked
                [`(λ ,binder ,body)
                 (note! "bare lexical property (L0.1)")
                 (define-values (expanded fired)
                   (expand-close-datum body inv rr-rows))
                 (for ([entry (in-list fired)]) (note! entry))
                 `(λ ,binder ,expanded)])
              walked)])))]))
  (values (walk datum) (reverse expansions)))

(define (redex-alpha-equivalent? left right)
  (define left-adapter (core->redex-adapter (datum->core left 'alpha-left)))
  (define right-adapter (core->redex-adapter (datum->core right 'alpha-right)))
  (alpha-equivalent? SmusniCore
                     (core-redex-adapter-term left-adapter)
                     (core-redex-adapter-term right-adapter)))

(define (binder-variables binder)
  (define flat
    (if (and (= (length binder) 1) (list? (first binder)))
        (first binder)
        binder))
  (define separator (index-of flat '::))
  (if separator
      (filter symbol? (take flat separator))
      '()))

;; A location-independent but binding-sensitive retrieval-site certificate.
;; Each entry fixes traversal order, Context/Vague kind, and the enclosing
;; binders on which the site's computation depends. Binder ids are structural,
;; so alpha-renaming cannot change the certificate and cannot disguise a
;; changed dependency.
(define (site-signatures datum)
  (define binder-ordinal 0)
  (define site-ordinal 0)
  (define signatures '())
  (define (extend env variables [track? #t])
    (for/fold ([result env]) ([variable (in-list variables)])
      (if track?
          (begin
            (set! binder-ordinal (add1 binder-ordinal))
            (hash-set result variable binder-ordinal))
          (hash-set result variable #f))))
  (define (dependencies node env)
    (define found (mutable-set))
    (define (scan value scope)
      (cond
        [(symbol? value)
         (define id (hash-ref scope value #f))
         (when id (set-add! found id))]
        [(not (list? value)) (void)]
        [else
         (match value
           [`(λ ,binder ,body)
            (scan body (extend scope (binder-variables binder) #f))]
           [`(Let ,binder ,rhs ,body)
            (scan rhs scope)
            (scan body (extend scope (binder-variables binder) #f))]
           [`(Bind . ,pieces)
            (define body (last pieces))
            (define alternating (drop-right pieces 1))
            (define current scope)
            (for ([index (in-range 0 (length alternating) 2)])
              (scan (list-ref alternating (add1 index)) current)
              (set! current
                    (extend current
                            (binder-variables (list-ref alternating index))
                            #f)))
            (scan body current)]
           [_ (for ([child (in-list value)]) (scan child scope))])]))
    (scan node env)
    (sort (set->list found) <))
  (define (walk node env)
    (when (list? node)
      (define head (datum-head node))
      (when (member head '(Context Vague))
        (set! site-ordinal (add1 site-ordinal))
        (set! signatures
              (cons `(site ,site-ordinal ,head ,(dependencies node env))
                    signatures)))
      (match node
        [`(λ ,binder ,body)
         (walk body (extend env (binder-variables binder)))]
        [`(Let ,binder ,rhs ,body)
         (walk rhs env)
         (walk body (extend env (binder-variables binder)))]
        [`(Bind . ,pieces)
         (define body (last pieces))
         (define alternating (drop-right pieces 1))
         (define current env)
         (for ([index (in-range 0 (length alternating) 2)])
           (walk (list-ref alternating (add1 index)) current)
           (set! current
                 (extend current
                         (binder-variables (list-ref alternating index)))))
         (walk body current)]
        [_ (for ([child (in-list node)]) (walk child env))])))
  (walk datum (hash))
  (reverse signatures))

(define (normalize-core core-term rr [inv (load-inventory)])
  (define datum (if (or (core-list? core-term) (core-atom? core-term))
                    (core->plain core-term)
                    core-term))
  (define fields (rr-fields-value rr))
  (define rows
    (if fields (hash-ref fields 'rows (lambda () '())) '()))
  (match (term (display-normalize ,rows ,datum))
    [`(normalized ,expanded ,expansions)
     (normalization expanded expansions)]
    [other (error 'normalize-core "Redex normalizer returned ~e" other)]))

(define (candidate-fence-map)
  (for/hash ([item (in-list
                    (classify-fences (read-all-fences) (load-manifest)))])
    (values (cons (fence-source item) (fence-ordinal item)) item)))

(define (missing-fixture-rows fields inv)
  (for/list ([row (in-list (hash-ref fields 'rows '()))]
             #:unless (inventory-row inv row))
    row))

(define (case-key source ordinal index)
  (format "~a#~a.~a" source ordinal index))

(define (expected-parse-reference candidate candidate-case)
  (list (format "parses/~a.json"
                (fixture-base-name (lowering-candidate-source candidate)
                                   (lowering-candidate-ordinal candidate)))
        (lowering-case-index candidate-case)))

(define (no-lowering-fails? cause detail promised-rows)
  (case cause
    [(rr-missing implementation) #t]
    [(row-missing)
     (for/or ([row (in-list (if (list? detail) detail '()))])
       (and (member row promised-rows) #t))]
    [else #f]))

(define (case-failure? report candidate-case)
  (case (case-report-disposition report)
    [(in-fragment/mismatch) #t]
    [(in-fragment/no-lowering)
     (no-lowering-fails? (case-report-cause report)
                         (case-report-message report)
                         (lowering-case-promised-rows candidate-case))]
    [else #f]))

(define disposition-rank
  (hash 'in-fragment/mismatch 100
        'in-fragment/no-lowering 80
        'unresolved 60
        'out-of-fragment 40
        'in-fragment/matched 0))

(define (aggregate-fence-disposition reports)
  (case-report-disposition
   (argmax (lambda (report)
             (+ (hash-ref disposition-rank (case-report-disposition report))
                (if (member (case-report-cause report)
                            '(rr-missing implementation))
                    10 0)))
           reports)))

(define (run-candidate-case candidate candidate-case parse-case rr-case target inv)
  (define source (lowering-candidate-source candidate))
  (define ordinal (lowering-candidate-ordinal candidate))
  (define index (lowering-case-index candidate-case))
  (define unresolved (lowering-case-unresolved candidate-case))
  (cond
    [unresolved
     (case-report source ordinal index 'unresolved #f '() '()
                  unresolved #f (core->plain target))]
    [else
     (define fields (rr-case-fields rr-case))
     (define promised-but-absent
       (filter (lambda (row)
                 (not (member row (hash-ref fields 'rows (lambda () '())))))
               (lowering-case-promised-rows candidate-case)))
     (define bad-parse-reference?
       (not (equal? (hash-ref fields 'parse (lambda () #f))
                    (expected-parse-reference candidate candidate-case))))
     (define missing-rows (missing-fixture-rows fields inv))
     (define result
       (cond
         [(or bad-parse-reference? (pair? promised-but-absent))
          (no-lowering
           "M3" 'rr-missing
           "RR parse reference or promised rows are incomplete"
           (append (if bad-parse-reference? '(parse) '()) promised-but-absent))]
         [(pair? missing-rows)
          (no-lowering "M3" 'row-missing
                       "RR references rows absent from fixture lexicon"
                       missing-rows)]
         [else (lower parse-case rr-case)]))
     (cond
       [(lowered? result)
        (define produced-normal
          (normalize-core (lowered-term result) (rr-case-fields rr-case) inv))
        (define expected-normal
          (normalize-core target (rr-case-fields rr-case) inv))
        (define expansions
          (remove-duplicates
           (append (normalization-expansions produced-normal)
                   (normalization-expansions expected-normal))))
        (define produced-datum (normalization-datum produced-normal))
        (define expected-datum (normalization-datum expected-normal))
        (define alpha-match?
          (redex-alpha-equivalent? produced-datum expected-datum))
        (define site-match?
          (equal? (site-signatures produced-datum)
                  (site-signatures expected-datum)))
        (if (and alpha-match? site-match?)
            (case-report source ordinal index 'in-fragment/matched #f
                         (lowered-rules result) expansions "matched"
                         produced-datum expected-datum)
            (case-report source ordinal index 'in-fragment/mismatch #f
                         (lowered-rules result) expansions
                         (cond [(not alpha-match?) "normalized terms differ"]
                               [else
                                "retrieval-site kind/order/dependencies differ"])
                         produced-datum expected-datum))]
       [else
        (define disposition
          (if (eq? (no-lowering-cause result) 'out-of-fragment)
              'out-of-fragment
              'in-fragment/no-lowering))
        (case-report source ordinal index disposition
                     (no-lowering-cause result) '() '()
                     (no-lowering-detail result) #f (core->plain target))])]))

(define (print-case-report report)
  (printf "  ~a: ~a" (case-key (case-report-source report)
                               (case-report-ordinal report)
                               (case-report-index report))
          (case-report-disposition report))
  (when (case-report-cause report) (printf "/~a" (case-report-cause report)))
  (when (pair? (case-report-rules report))
    (printf " rules=~a" (string-join (case-report-rules report) ",")))
  (when (pair? (case-report-expansions report))
    (printf " expansions=~s" (case-report-expansions report)))
  (newline)
  (when (eq? (case-report-disposition report) 'in-fragment/mismatch)
    (printf "    produced: ~a\n" (pretty-format (case-report-produced report)))
    (printf "    expected: ~a\n" (pretty-format (case-report-expected report))))
  (when (member (case-report-disposition report)
                '(unresolved out-of-fragment in-fragment/no-lowering))
    (printf "    reason: ~e\n" (case-report-message report))))

(define (run-lowering-gate #:print? [print? #t])
  (define manifest (load-lowering-manifest))
  (validate-lowering-fixtures! manifest)
  (define inv (load-inventory))
  (define mutation-sweep (run-parse-mutation-sweeps manifest inv))
  (define fences (candidate-fence-map))
  (define reports '())
  (define fence-reports '())
  (define fixture-property-total 0)
  (define structural-eligible-total 0)
  (define global-branch-total 0)
  (define fixture-property-failures '())
  (for ([candidate (in-list (lowering-manifest-candidates manifest))])
    (define key (cons (lowering-candidate-source candidate)
                      (lowering-candidate-ordinal candidate)))
    (define item (hash-ref fences key))
    (define targets (read-core-forms (fence-content item)))
    (define parse-cases (hash-ref (load-parse-fixture candidate) 'cases))
    (define rr-cases (rr-fixture-cases (load-rr-fixture candidate inv)))
    (define current
      (for/list ([candidate-case (in-list (lowering-candidate-cases candidate))]
                 [parse-case (in-list parse-cases)]
                 [rr-case (in-list rr-cases)]
                 [target (in-list targets)])
        (define report
          (run-candidate-case candidate candidate-case parse-case rr-case target inv))
        (unless (lowering-case-unresolved candidate-case)
          (set! structural-eligible-total (add1 structural-eligible-total))
          (define sigma (parse-case->sigma parse-case (rr-case-fields rr-case) inv))
          (unless (no-lowering? sigma)
            (when (match sigma
                    [`(cardinal global . ,_) #t]
                    [_ #f])
              (set! global-branch-total (add1 global-branch-total)))
            (set! fixture-property-total (add1 fixture-property-total))
            (unless (fixture-derivation-check rr-case sigma)
              (set! fixture-property-failures
                    (cons (case-key (lowering-candidate-source candidate)
                                    (lowering-candidate-ordinal candidate)
                                    (lowering-case-index candidate-case))
                          fixture-property-failures)))))
        report))
    (set! reports (append reports current))
    (set! fence-reports
          (append fence-reports
                  (list (fence-report (lowering-candidate-source candidate)
                                      (lowering-candidate-ordinal candidate)
                                      (aggregate-fence-disposition current)
                                      current)))))
  (define matched-rules
    (for*/set ([report (in-list reports)]
               #:when (eq? (case-report-disposition report)
                           'in-fragment/matched)
               [rule (in-list (case-report-rules report))]
               #:when (member rule (fragment-rule-ids manifest)))
      rule))
  (define unformed
    (for/list ([rule (in-list (fragment-rule-ids manifest))]
               #:unless (set-member? matched-rules rule))
      rule))
  (define-values (generated-status generated-attempts generated-detail)
    (generated-redex-check))
  (define failures?
    (for/or ([candidate (in-list (lowering-manifest-candidates manifest))]
             [fence-report (in-list fence-reports)])
      (for/or ([candidate-case (in-list (lowering-candidate-cases candidate))]
               [report (in-list (fence-report-cases fence-report))])
        (case-failure? report candidate-case))))
  (set! failures?
        (or failures?
            (pair? fixture-property-failures)
            (pair? (mutation-sweep-result-failures mutation-sweep))
            (eq? generated-status 'counterexample)))
  (when print?
    (printf "F₀-M3: live L1, L3, L5 (+ L0.1) — ~a lowering judgments; fixtures are not exhaustive\n"
            (length (fragment-rule-ids manifest)))
    (for ([fence-report (in-list fence-reports)])
      (for ([report (in-list (fence-report-cases fence-report))])
        (print-case-report report))
      (printf "  fence ~a#~a: ~a\n"
              (fence-report-source fence-report)
              (fence-report-ordinal fence-report)
              (fence-report-disposition fence-report)))
    (for ([disposition (in-list
                        '(in-fragment/matched in-fragment/mismatch
                          in-fragment/no-lowering unresolved out-of-fragment))])
      (printf "lowering ~a: ~a cases\n" disposition
              (count (lambda (report)
                       (eq? (case-report-disposition report) disposition))
                     reports)))
    (printf "lowering formed coverage: ~a/~a rules; unformed=~a\n"
            (set-count matched-rules) (length (fragment-rule-ids manifest))
            (string-join unformed ","))
    (printf "structurally lowered from gentufa/RR: ~a/~a eligible cases\n"
            fixture-property-total structural-eligible-total)
    (printf "GlobalExactly branch: ~a candidate case~a lowered\n"
            global-branch-total (if (= global-branch-total 1) "" "s"))
    (printf
     "parse mutation sweeps: wrapper-renames=~a refused=~a allowlisted-unchanged=~a; subtree-deletions=~a refused-or-changed=~a; failures=~a\n"
     (mutation-sweep-result-wrapper-attempts mutation-sweep)
     (- (mutation-sweep-result-wrapper-attempts mutation-sweep)
        (mutation-sweep-result-wrapper-allowlisted mutation-sweep)
        (count (lambda (failure) (eq? (second failure) 'rename))
               (mutation-sweep-result-failures mutation-sweep)))
     (mutation-sweep-result-wrapper-allowlisted mutation-sweep)
     (mutation-sweep-result-deletion-attempts mutation-sweep)
     (- (mutation-sweep-result-deletion-attempts mutation-sweep)
        (count (lambda (failure) (eq? (second failure) 'delete))
               (mutation-sweep-result-failures mutation-sweep)))
     (length (mutation-sweep-result-failures mutation-sweep)))
    (when (pair? (mutation-sweep-result-failures mutation-sweep))
      (printf "  mutation failures: ~e\n"
              (mutation-sweep-result-failures mutation-sweep)))
    (printf "deterministic fixture derivations: ~a/~a outputs type-check~a\n"
            (- fixture-property-total (length fixture-property-failures))
            fixture-property-total
            (if (null? fixture-property-failures)
                ""
                (format "; failed=~a"
                        (string-join (reverse fixture-property-failures) ","))))
    (case generated-status
      [(passed)
       (printf "redex-check satisfying generation: passed ~a attempts\n"
               generated-attempts)]
      [(counterexample)
       (printf "redex-check satisfying generation: COUNTEREXAMPLE after ~a attempts: ~e\n"
               generated-attempts generated-detail)]
      [else
       (printf "redex-check satisfying generation: unavailable; seed=n/a attempts=0 size-profile=n/a (fixture-only deterministic coverage): ~a\n"
               generated-detail)]))
  (values (not failures?) reports fence-reports))

(module+ main
  (define action 'check)
  (command-line
   #:program "lower.rkt"
   #:once-each
   [("--refresh-parses") "regenerate tracked gentufa parse fixtures"
    (set! action 'refresh)]
   [("--check") "validate tracked lowering fixtures (default)"
    (set! action 'check)])
  (define manifest (load-lowering-manifest))
  (case action
    [(refresh) (refresh-parses! manifest)]
    [(check)
     (define-values (ok? _case-reports _fence-reports)
       (run-lowering-gate))
     (unless ok? (exit 1))]))
