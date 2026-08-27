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
         normalize-core
         redex-alpha-equivalent?
         fixture-derivation-check
         generated-redex-check
         no-lowering-fails?
         aggregate-fence-disposition
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
  [(pure-out lexical x_P) (λ ($x :: Entity) (x_P $x))]
  [(pure-out described x_P)
   (λ ($x :: Entity)
     (SpeakerDescribes
      $x (λ ($y :: Referents Entity) (x_P $y))))])

(define-metafunction SmusniM3
  apply* : e (e ...) -> e
  [(apply* e_R (e_arg ...)) (e_R e_arg ...)])

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
   (λ ($new1 $new2 :: Referents Entity) (x_R $new2 $new1))])

(define-metafunction SmusniM3
  connective-out : e e e -> e
  [(connective-out not e_left none) (ClauseNot (DirectClause e_left))]
  [(connective-out and e_left e_right)
   (ClauseAnd (DirectClause e_left) (DirectClause e_right))]
  [(connective-out or e_left e_right)
   (ClauseOr (DirectClause e_left) (DirectClause e_right))])

(define-metafunction SmusniM3
  cohe-out : e e e -> e
  [(cohe-out e_row e_left e_right)
   (Bind ($r :: PredTerm e_row) (Context)
     (Assert (Close ($r e_left e_right))))])

(define-metafunction SmusniM3
  termset-out : e x e x x -> e
  [(termset-out e_n1 e_P1 e_n2 e_P2 x_Q)
   (Bind ($left :: Referents Entity)
         (SelectExactly e_n1 (λ ($x :: Entity) (e_P1 $x)))
         ($right :: Referents Entity)
         (SelectExactly e_n2 (λ ($x :: Entity) (e_P2 $x)))
     (Assert
      (Distrib
       (λ ($l :: Entity)
         (Distrib (λ ($r :: Entity) (Close (x_Q $l $r))) $right))
       $left)))])

(define-metafunction SmusniM3
  grade-out : x e -> e
  [(grade-out x_R e_arg)
   (Bind ($s :: Scale) (Context)
         ($reg :: Region Scale)
         (Vague (λ ($r :: Region Scale) (AdmissibleCutoff $s $r)))
     (Assert (Close ((Grade x_R $s $reg) e_arg))))])

(define-metafunction SmusniM3
  scalar-out : e x e -> e
  [(scalar-out e_kind x_R e_arg)
   (Bind ($d :: ContrastDomain (RowOf x_R)) (Context)
     (Assert (Close ((Scalar e_kind $d x_R) e_arg))))])

(define-metafunction SmusniM3
  zip-out : x (e ...) (e ...) -> e
  [(zip-out x_R (e_left ...) (e_right ...))
   (ZipWith
    (λ ($left $right :: Referents Entity) (Close (x_R $left $right)))
    (List e_left ...)
    (List e_right ...))])

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
  [(le-cont-source (pure described x_P) x_ref) (pure described x_P)]
  [(le-cont-source (description x_Q e_polarity e_force) x_ref)
   (description-source e_force x_Q e_polarity x_ref)])

(define-metafunction SmusniM3
  le-out : x e x e -> e
  [(le-out x_P (pure described x_P) x_ref e_property) e_property]
  [(le-out x_P e_continuation x_ref e_body)
   (Bind (x_ref :: Referents Entity)
         (Refer
          (λ ($described :: Referents Entity)
            (SpeakerDescribes
             $described (λ ($unit :: Referents Entity) (x_P $unit)))))
     e_body)])

(define-metafunction SmusniM3
  threshold-out : e e e -> e
  [(threshold-out many e_P e_Q)
   (Bind ($n :: Natural)
         (Vague (AdmissibleThreshold ManyK e_P))
     (Assert (AtLeast $n e_P e_Q)))]
  [(threshold-out too-many e_P e_Q)
   (Bind ($purpose :: Referents Entity) (Context)
         ($n :: Natural)
         (Vague (AdmissibleThreshold TooManyK e_P $purpose))
     (Assert (MoreThan $n e_P e_Q)))])

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

  [(where e_out (pure-out e_kind x_P))
   --------------------------------------------- "L0.1"
   (m3-lower e_RR (gentufa e_parse (pure e_kind x_P)) e_out)]

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

  [(where e_relation (DropPlace x_R e_label))
   (where e_out (apply* e_relation (e_arg ...)))
   --------------------------------------------- "L1.5"
   (m3-lower e_RR (gentufa e_parse (drop x_R e_label e_arg ...)) e_out)]

  [(m3-lower e_RR (gentufa e_parse e_source) e_out)
   --------------------------------------------- "L1.6"
   (m3-lower e_RR (gentufa e_parse (omit e_source)) e_out)]

  [(where e_out (cohe-out e_row e_left e_right))
   --------------------------------------------- "L1.8"
   (m3-lower e_RR (gentufa e_parse (cohe e_row e_left e_right)) e_out)]

  [(where e_relation (Tanru x_M x_H))
   (where e_out (apply* e_relation (e_arg ...)))
   --------------------------------------------- "L1.10"
   (m3-lower e_RR (gentufa e_parse (tanru x_M x_H e_arg ...)) e_out)]

  [(where x_ref ,(variable-not-in (term (e_RR e_parse x_P x_Q)) '$r))
   (where e_continuation
          (description-source e_force x_Q e_polarity x_ref))
   (m3-lower e_RR (gentufa e_parse e_continuation) e_body)
   --------------------------------------------- "L3.1"
   (m3-lower e_RR (gentufa e_parse (lo x_P x_Q e_polarity e_force))
             (Bind (x_ref :: Referents Entity)
                   (Refer (λ ($unit :: Referents Entity) (x_P $unit)))
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
   (where e_continuation
          (description-source e_force x_Q positive-omit x_ref))
   (m3-lower e_RR (gentufa e_parse e_continuation) e_body)
   --------------------------------------------- "L3.3"
   (m3-lower e_RR (gentufa e_parse (la e_name x_Q e_force))
             (Bind (x_ref :: Referents Entity)
                   (Refer (λ ($named :: Referents Entity)
                            (Named e_name $named)))
               e_body))]

  [(m3-lower e_RR (gentufa e_parse (pure lexical x_P)) e_P)
   (m3-lower e_RR (gentufa e_parse (close shorthand (pred x_Q $x))) e_Q_body)
   --------------------------------------------- "L3.4"
   (m3-lower e_RR (gentufa e_parse (generic x_P x_Q))
             (Generic Typical e_P (λ ($x :: Entity) e_Q_body)))]

  [--------------------------------------------- "L3.5"
   (m3-lower e_RR (gentufa e_parse (collection-base x_P))
             (Local (Refer (λ ($x :: Entity) (x_P $x)))))]

  [(m3-lower e_RR (gentufa e_parse (collection-base x_P)) e_base)
   --------------------------------------------- "L3.6"
   (m3-lower e_RR (gentufa e_parse (collection-set x_P))
             (Bind ($base :: Referents Entity) e_base
               (Bind ($sets :: Referents (Set Entity))
                     (Refer (λ ($s :: Set Entity) (Close (selcmi $s $base))))
                 (Mention $sets))))]

  [(m3-lower e_RR (gentufa e_parse (le-unit x_P)) e_P)
   --------------------------------------------- "L3.9"
   (m3-lower e_RR (gentufa e_parse (inner-pa e_n x_P))
             (SelectExactly e_n e_P))]

  [(m3-lower e_RR (gentufa e_parse (inner-pa e_n x_P)) e_selection)
   --------------------------------------------- "L3.14"
   (m3-lower e_RR (gentufa e_parse (luho e_n x_P))
             (Bind ($people :: Referents Entity) (Local e_selection)
               (Bind ($κ :: DecompositionBasis (Group Entity) Entity)
                     (Context (GroupBasisConstraint |lu'o| Entity) deps…)
                 (Bind ($aggregate :: Referents (Group Entity))
                       (Massify $κ $people)
                   (Mention $aggregate)))))]

  [(m3-lower e_RR
             (gentufa e_parse (le x_P (pure described x_P))) e_property)
   --------------------------------------------- "L3.15"
   (m3-lower e_RR (gentufa e_parse (le-unit x_P)) e_property)]

  [(m3-lower e_RR (gentufa e_parse (pure lexical x_P)) e_P)
   (m3-lower e_RR (gentufa e_parse (close shorthand (pred x_Q $x))) e_Q_body)
   --------------------------------------------- "L5.1"
   (m3-lower e_RR (gentufa e_parse (every x_P x_Q))
             (Every e_P (λ ($x :: Entity) e_Q_body)))]

  [(m3-lower e_RR (gentufa e_parse (pure lexical x_P)) e_P)
   (m3-lower e_RR (gentufa e_parse (close shorthand (pred x_Q $w))) e_Q_body)
   --------------------------------------------- "L5.2"
   (m3-lower e_RR (gentufa e_parse (cardinal e_n x_P x_Q))
             (Bind ($w :: Referents Entity)
                   (SelectExactly e_n e_P)
               e_Q_body))]

  [(where e_out (termset-out e_n1 x_P1 e_n2 x_P2 x_Q))
   --------------------------------------------- "L5.3"
   (m3-lower e_RR
             (gentufa e_parse (termset e_n1 x_P1 e_n2 x_P2 x_Q)) e_out)]

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

  [(where e_out (scalar-out e_kind x_P e_arg))
   --------------------------------------------- "L5.11"
   (m3-lower e_RR (gentufa e_parse (scalar e_kind x_P e_arg)) e_out)]

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

  [(m3-lower e_RR (gentufa e_parse (pure lexical x_P)) e_P)
   (m3-lower e_RR (gentufa e_parse
                            (nuclear $w (Referents Entity) x_Q)) e_Q)
   (where e_out (threshold-out e_kind e_P e_Q))
   --------------------------------------------- "L5.28"
   (m3-lower e_RR (gentufa e_parse (threshold e_kind x_P x_Q)) e_out)]

  [(where e_out (grade-out x_R e_arg))
   --------------------------------------------- "L5.29"
   (m3-lower e_RR (gentufa e_parse (grade x_R e_arg)) e_out)] )

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
    (define comment
      (for/first ([index (in-range (sub1 line-index) -1 -1)]
                  #:do [(define match
                           (regexp-match #px"^;[ ]?(.*)$"
                                         (list-ref lines index)))]
                  #:when match)
        (second match)))
    (unless comment
      (error 'candidate-source-comments
             "~a#~a form at line ~a has no leading comment"
             (fence-source item) (fence-ordinal item) (core-list-line form)))
    comment))

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

(define (first-terminal value kind)
  (define found (terminal-texts value kind))
  (and (pair? found) (first found)))

(define number-values
  (hash "no" 0 "pa" 1 "re" 2 "ci" 3 "vo" 4 "mu" 5
        "xa" 6 "ze" 7 "bi" 8 "so" 9))

(define reference-values
  (hash "mi" 'Speaker "do" 'Audience "ti" 'This "ta" 'That "tu" 'Yonder))

(define (rr-value fields name)
  (hash-ref fields name (lambda () '())))

(define (rr-has? fields name value)
  (member value (rr-value fields name)))

(define (require-row fields relation)
  (if (member relation (rr-value fields 'rows))
      #t
      (no-lowering "L1.1" 'rr-missing
                   "RR.rows does not select the parsed lexical relation"
                   relation)))

(define (parsed-relation subtree)
  (define gismu (remove-duplicates (terminal-texts subtree 'Gismu)))
  (cond [(pair? gismu) (string->symbol (last gismu))]
        [(member "co'e" (terminal-texts subtree 'Cmavo)) '|co'e|]
        [else #f]))

(define (sumti-view subtree)
  (cond
    [(first-tag subtree 'ProSumti)
     => (lambda (node)
          (define word (first-terminal node 'Cmavo))
          (cond [(hash-ref reference-values word #f) => (lambda (value) `(value ,value))]
                [(equal? word "zi'o") '(deleted)]
                [else (no-lowering "L1.4" 'rule-underspecified
                                   "unsupported parsed pro-sumti" word)]))]
    [(first-tag subtree 'NameSumti)
     => (lambda (node)
          (define name (first-terminal node 'Cmevla))
          (if name `(name ,name)
              (no-lowering "L3.3" 'rule-underspecified
                           "name parse has no cmevla" #f)))]
    [(first-tag subtree 'LaheSumti)
     => (lambda (node)
          (define op (first-terminal (hash-ref node 'lahe) 'Cmavo))
          (define inner (sumti-view (hash-ref node 'inner_sumti)))
          (if (no-lowering? inner) inner `(lahe ,op ,inner)))]
    [(first-tag subtree 'DescriptorWithGadriSumti)
     => (lambda (node)
          (define gadri (first-terminal (hash-ref node 'description) 'Cmavo))
          (define tail (hash-ref node 'tail))
          (define relation (parsed-relation tail))
          (define quantifier-node (first-tag tail 'PaRunQuantifier))
          (define count
            (and quantifier-node
                 (hash-ref number-values
                           (first-terminal quantifier-node 'Cmavo) #f)))
          (if (and gadri relation)
              `(description ,gadri ,relation ,count)
              (no-lowering "L3.1" 'rule-underspecified
                           "descriptor parse lacks gadri or relation" node)))]
    [(first-tag subtree 'DescriptorWithoutGadriSumti)
     => (lambda (node)
          (define quantifier-node (hash-ref node 'quantifier))
          (define q-word (first-terminal quantifier-node 'Cmavo))
          (define relation (parsed-relation (hash-ref node 'selbri)))
          (define quantity (hash-ref number-values q-word q-word))
          (if relation `(quantifier ,quantity ,relation)
              (no-lowering "L5.2" 'rule-underspecified
                           "quantifier parse lacks relation" node)))]
    [else
     (no-lowering "M3" 'out-of-fragment
                  "unsupported gentufa sumti construct"
                  (sort (set->list (parse-case-variants
                                    (hasheq 'parse subtree 'surface "")))
                        symbol<?))]))

(define (term-view connected-term)
  (cond
    [(and (has-tag? connected-term 'JoiConnective)
          (member "fa'u" (terminal-texts connected-term 'Cmavo)))
     (define values
       (for/list ([word (in-list (terminal-texts connected-term 'Cmavo))]
                  #:when (hash-has-key? reference-values word))
         (hash-ref reference-values word)))
     (if (pair? values)
         `(zip-values ,values)
         (no-lowering "L5.21" 'rule-underspecified
                      "fa'u connectee has no referential values" connected-term))]
    [(first-tag connected-term 'PlaceTaggedSumtiTerm)
     => (lambda (node)
          (define fa (first-terminal (hash-ref node 'fa) 'Cmavo))
          (define label (hash "fa" 1 "fe" 2 "fi" 3 "fo" 4 "fu" 5))
          (define sumti (sumti-view (hash-ref node 'sumti)))
          (if (no-lowering? sumti) sumti
              `(label ,(hash-ref label fa) ,sumti)))]
    [else (sumti-view connected-term)]))

(define (selbri-view subtree)
  (define relation (parsed-relation subtree))
  (define gismu (remove-duplicates (terminal-texts subtree 'Gismu)))
  (define cmavo (terminal-texts subtree 'Cmavo))
  (cond
    [(not relation)
     (no-lowering "L1.1" 'rule-underspecified
                  "selbri parse has no supported lexical relation" cmavo)]
    [else
     (hasheq 'relation relation
             'tanru (and (>= (length gismu) 2)
                         (map string->symbol (take-right gismu 2)))
             'conversion (and (member "se" cmavo) 'se)
             'scalar (and (has-tag? subtree 'ScalarNegatedTanruUnit)
                          (cond [(member "na'e" cmavo) 'OtherThan]
                                [(member "to'e" cmavo) 'Opposite]
                                [(member "no'e" cmavo) 'Neutral]
                                [else #f]))
             'negated (has-tag? subtree 'NegatedSelbri))]))

(define (collect-bridi-terms bridi)
  (define leading (hash-ref bridi 'leading_terms (lambda () '())))
  (define tail (first-tag bridi 'SelbriSimpleBridiTail))
  (define trailing (if tail (hash-ref tail 'terms (lambda () '())) '()))
  (append leading trailing))

(define (termset-views term-node)
  (for/list ([descriptor (in-list
                          (tag-values term-node 'DescriptorWithoutGadriSumti))])
    (sumti-view (hasheq 'DescriptorWithoutGadriSumti descriptor))))

(define (bridi-view statement)
  (define bridi
    (or (first-tag statement 'BridiWithLeadingTerms)
        (first-tag statement 'RelationOnlyBridi)))
  (if (not bridi)
      (no-lowering "L1.1" 'out-of-fragment
                   "gentufa statement has no supported bridi node" #f)
      (let* ([tail (first-tag bridi 'SelbriSimpleBridiTail)]
             [selbri (and tail (selbri-view (hash-ref tail 'selbri)))])
        (if (or (not selbri) (no-lowering? selbri))
            (or selbri (no-lowering "L1.1" 'rule-underspecified
                                    "bridi tail has no simple selbri" #f))
            (let ([term-nodes (collect-bridi-terms bridi)])
              (if (and (= (length term-nodes) 1)
                       (has-tag? (first term-nodes) 'CeheConnective))
                  (hasheq 'selbri selbri
                          'terms (termset-views (first term-nodes))
                          'termset #t)
                  (let ([terms (map term-view term-nodes)])
                    (if (ormap no-lowering? terms)
                        (findf no-lowering? terms)
                        (hasheq 'selbri selbri 'terms terms
                                'termset #f)))))))))

(define (force-from-rr fields)
  (define force (rr-value fields 'force))
  (cond [(member 'assert force) 'assert]
        [(member 'mention force) 'mention]
        [(null? force) #f]
        [else (no-lowering "L1.2" 'rr-missing
                           "RR.force has no supported consumer" force)]))

(define (close-mode-from-rr fields [negated? #f] [connected? #f])
  (define readings (rr-value fields 'readings))
  (cond [(or negated? connected?)
         (if (member 'actual readings) 'actual
             (no-lowering "L1.3" 'rr-missing
                          "RR.readings lacks actual mode" readings))]
        [else 'shorthand]))

(define (ordinary-fills terms)
  (define next 1)
  (define fills (make-hash))
  (define deleted '())
  (for ([term (in-list terms)])
    (match term
      [`(label ,label (value ,value))
       (hash-set! fills label value)
       (set! next (max next (add1 label)))]
      [`(value ,value)
       (hash-set! fills next value)
       (set! next (add1 next))]
      [`(deleted)
       (set! deleted (cons next deleted))
       (set! next (add1 next))]
      [_ (void)]))
  (values fills (reverse deleted)))

(define (application-source view fields inv)
  (define selbri (hash-ref view 'selbri))
  (define relation (hash-ref selbri 'relation))
  (define row-check (require-row fields relation))
  (if (no-lowering? row-check)
      row-check
      (let-values ([(fills deleted) (ordinary-fills (hash-ref view 'terms))])
        (define row (inventory-row inv relation))
        (if (not row)
            (no-lowering "L1.1" 'row-missing
                         "selected lexical row is absent" relation)
            (let* ([total (row-decl-total row)]
                   [ordered
                    (for/list ([label (in-range 1 (add1 total))]
                               #:when (hash-has-key? fills label))
                      (hash-ref fills label))]
                   [base
                    (cond
                      [(pair? deleted)
                       `(drop ,relation ,(first deleted) ,@ordered)]
                      [(hash-ref selbri 'conversion #f)
                       (define routed
                         (if (>= (length ordered) 2)
                             (list (second ordered) (first ordered))
                             ordered))
                       `(route (application ,relation ,@routed))]
                      [(not (equal? (sort (hash-keys fills) <)
                                    (range 1 (add1 (hash-count fills)))))
                       (define labels (sort (hash-keys fills) <))
                       (if (and (pair? labels)
                                (equal? labels
                                        (range (first labels)
                                               (+ (first labels)
                                                  (length labels)))))
                           `(route
                             (application
                              ,relation
                              ,(string->symbol (format ":~a" (first labels)))
                              ,@(map (lambda (label) (hash-ref fills label)) labels)))
                           `(route
                             (application
                              ,relation
                              ,@(append*
                                 (for/list ([label (in-list labels)])
                                   (list
                                    (string->symbol (format ":~a" label))
                                    (hash-ref fills label)))))))]
                      [(hash-ref selbri 'tanru #f)
                       (match-define (list modifier head)
                         (hash-ref selbri 'tanru))
                       `(tanru ,modifier ,head ,@ordered)]
                      [else `(pred ,relation ,@ordered)])]
                   [provided (+ (hash-count fills) (length deleted))])
              (if (< provided total) `(omit ,base) base))))))

(define (view->sigma view category fields inv)
  (define selbri (hash-ref view 'selbri))
  (define relation (hash-ref selbri 'relation))
  (define negated? (hash-ref selbri 'negated))
  (define terms (hash-ref view 'terms))
  (cond
    [(and (= (length terms) 2)
          (andmap (lambda (term)
                    (match term [`(zip-values ,(? list?)) #t] [_ #f]))
                  terms))
     (match* ((first terms) (second terms))
       [(`(zip-values ,left) `(zip-values ,right))
        `(zip ,relation ,left ,right)])]
    [(hash-ref view 'termset)
     (if (and (= (length terms) 2)
              (andmap (lambda (term)
                        (match term [`(quantifier ,(? number?) ,_) #t] [_ #f]))
                      terms))
         (match* ((first terms) (second terms))
           [(`(quantifier ,n1 ,p1) `(quantifier ,n2 ,p2))
            `(termset ,n1 ,p1 ,n2 ,p2 ,relation)])
         (no-lowering "L5.3" 'rule-underspecified
                      "termset shape is not mechanically supported" terms))]
    [(and (= (length terms) 1)
          (match (first terms) [`(description ,_ ,_ ,_) #t] [_ #f]))
     (match (first terms)
       [`(description ,gadri ,predicate ,count)
        (case (string->symbol gadri)
          [(lo)
           (define row-check (require-row fields relation))
           (define force (force-from-rr fields))
           (cond [(no-lowering? row-check) row-check]
                 [(no-lowering? force) force]
                 [else `(lo ,predicate ,relation
                            ,(if negated? 'negative 'positive) ,force)])]
          [(le)
           (define row-check (require-row fields relation))
           (define force (force-from-rr fields))
           (cond [(no-lowering? row-check) row-check]
                 [(no-lowering? force) force]
                 [else `(le ,predicate
                            (description ,relation
                                         ,(if negated? 'negative 'positive)
                                         ,force))])]
          [(|lo'i|) `(collection-set ,predicate)]
          [(|lo'e|)
           (if (rr-has? fields 'readings 'typical)
               `(force ,(force-from-rr fields) (generic ,predicate ,relation))
               (no-lowering "L3.4" 'rr-missing
                            "lo'e needs the selected typical reading" #f))]
          [else (no-lowering "L3.1" 'rule-underspecified
                             "unsupported parsed gadri" gadri)])])]
    [(and (= (length terms) 1)
          (match (first terms) [`(name ,_) #t] [_ #f]))
     (match-define `(name ,name) (first terms))
     (define force (force-from-rr fields))
     (if (no-lowering? force) force
         `(la ,name ,relation ,force))]
    [(and (= (length terms) 1)
          (match (first terms) [`(lahe ,_ ,_) #t] [_ #f]))
     (match (first terms)
       [`(lahe "lu'o" (description "le" ,predicate ,(? number? count)))
        `(luho ,count ,predicate)]
       [_ (no-lowering "L3.14" 'rule-underspecified
                       "unsupported LAhE parse" (first terms))])]
    [(and (= (length terms) 1)
          (match (first terms) [`(quantifier ,_ ,_) #t] [_ #f]))
     (match (first terms)
       [`(quantifier ,quantity ,predicate)
        (cond
          [(equal? quantity "ro")
           (if (rr-has? fields 'readings 'importing)
               `(force ,(force-from-rr fields) (every ,predicate ,relation))
               (no-lowering "L5.1" 'rr-missing
                            "ro description needs importing reading" #f))]
          [(number? quantity)
           (if (rr-has? fields 'readings 'witness-set)
               `(cardinal ,quantity ,predicate ,relation)
               (no-lowering "L5.2" 'rr-missing
                            "numeric quantifier needs witness-set reading" #f))]
          [(equal? quantity "so'i")
           (if (and (rr-has? fields 'readings 'many)
                    (pair? (rr-value fields 'sites)))
               `(threshold many ,predicate ,relation)
               (no-lowering "L5.28" 'rr-missing
                            "so'i needs many reading and threshold site" #f))]
          [(equal? quantity "du'e")
           (if (and (rr-has? fields 'readings 'too-many)
                    (pair? (rr-value fields 'sites)))
               `(threshold too-many ,predicate ,relation)
               (no-lowering "L5.28" 'rr-missing
                            "du'e needs too-many reading and sites" #f))]
          [else (no-lowering "L5.2" 'rule-underspecified
                             "unsupported parsed quantity" quantity)])])]
    [else
     (cond
       [(and (hash-ref selbri 'tanru #f) (null? terms))
        (no-lowering "L1.10" 'rule-underspecified
                     "tanru parse has no resolved head-place fill" selbri)]
       [(hash-ref selbri 'scalar #f)
        (if (not (and (rr-has? fields 'readings 'other-than)
                      (pair? (rr-value fields 'sites))))
            (no-lowering "L5.11" 'rr-missing
                         "scalar reading needs kind and contrast-domain site" #f)
            (if (not (pair? terms))
            (no-lowering "L5.11" 'rr-missing
                         "scalar bridi lacks its argument" #f)
            (match (first terms)
              [`(value ,argument)
               `(scalar ,(hash-ref selbri 'scalar) ,relation ,argument)]
              [_ (no-lowering "L5.11" 'rule-underspecified
                              "unsupported scalar argument" (first terms))])))]
       [(equal? relation '|co'e|)
        (if (and (rr-has? fields 'readings 'ellipsis)
                 (pair? (rr-value fields 'sites))
                 (= (length terms) 2))
            `(cohe (Row (1 (Referents Entity)) (2 (Referents Entity)))
                   ,@(for/list ([term (in-list terms)])
                       (match term [`(value ,value) value])))
            (no-lowering "L1.8" 'rr-missing
                         "co'e needs two arguments plus RR.readings/sites" terms))]
       [(rr-has? fields 'readings 'gradable)
        (if (and (pair? (rr-value fields 'sites)) (= (length terms) 1))
            (match (first terms)
              [`(value ,argument) `(grade ,relation ,argument)]
              [_ (no-lowering "L5.29" 'rule-underspecified
                              "unsupported gradable argument" (first terms))])
            (no-lowering "L5.29" 'rr-missing
                         "gradable reading needs scale/cutoff sites" #f))]
       [else
        (define app (application-source view fields inv))
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
               (define force (force-from-rr fields))
               (if (no-lowering? force) force
                   (let ([mode (close-mode-from-rr fields negated?)])
                     (if (no-lowering? mode) mode
                         `(force ,force
                                 (close ,mode
                                        ,(if negated? `(na ,app) app))))))]))])]))

(define (statement->sigma statement category fields inv)
  (define connection (first-tag statement 'IStatementConnection))
  (if connection
      (let* ([leading (hash-ref connection 'leading_statement)]
             [continuations (hash-ref connection 'continuations)]
             [tail (and (= (length continuations) 1)
                        (first-tag (first continuations)
                                   'SimpleIConnectiveStatementTail))])
        (if (not tail)
            (no-lowering "L5.12" 'rule-underspecified
                         "unsupported statement connection shape" connection)
            (let* ([left-view (bridi-view leading)]
                   [right-view (bridi-view (hash-ref tail 'trailing_statement))]
                   [jek (first-terminal (hash-ref tail 'connective) 'Cmavo)]
                   [kind (cond [(equal? jek "je") 'and]
                               [(equal? jek "ja") 'or]
                               [else #f])])
              (if (or (no-lowering? left-view) (no-lowering? right-view)
                      (not kind))
                  (or (and (no-lowering? left-view) left-view)
                      (and (no-lowering? right-view) right-view)
                      (no-lowering "L5.12" 'rule-underspecified
                                   "unsupported parsed connective" jek))
                  (let ([left (application-source left-view fields inv)]
                        [right (application-source right-view fields inv)]
                        [force (force-from-rr fields)])
                    (if (or (no-lowering? left) (no-lowering? right)
                            (no-lowering? force))
                        (or (and (no-lowering? left) left)
                            (and (no-lowering? right) right)
                            force)
                        `(force ,force
                                (close actual
                                       (sentence-connect ,kind ,left ,right)))))))))
      (let ([view (bridi-view statement)])
        (if (no-lowering? view) view (view->sigma view category fields inv)))))

(define (fragment->sigma raw fields inv)
  (define fragment (first-tag raw 'TermsFragment))
  (if (not fragment)
      (no-lowering "M3" 'out-of-fragment
                   "parse is neither a supported statement nor terms fragment" #f)
      (let* ([terms (tag-values fragment 'ConnectedTerm)]
             [view (and (= (length terms) 1) (term-view (first terms)))])
        (cond
          [(no-lowering? view) view]
          [(match view [`(description "lo'i" ,predicate ,_) #t] [_ #f])
           (match view [`(description ,_ ,predicate ,_) `(collection-set ,predicate)])]
          [(match view [`(lahe "lu'o" (description "le" ,predicate ,count)) #t]
                       [_ #f])
           (match view
             [`(lahe ,_ (description ,_ ,predicate ,count))
              `(luho ,count ,predicate)])]
          [else (no-lowering "M3" 'out-of-fragment
                             "unsupported parsed terms fragment" view)]))))

(define (parse-case->sigma parse-case fields [inv (load-inventory)])
  (define raw (hash-ref parse-case 'parse))
  (define category (string->symbol (hash-ref parse-case 'category)))
  (cond
    [(first-tag raw 'TermsFragment) (fragment->sigma raw fields inv)]
    [(first-tag raw 'IStatementConnection)
     (statement->sigma raw category fields inv)]
    [(first-tag raw 'BridiStatement)
     => (lambda (statement) (statement->sigma statement category fields inv))]
    [(first-tag raw 'FragmentStatement)
     => (lambda (fragment) (fragment->sigma fragment fields inv))]
    [else
     (no-lowering "M3" 'out-of-fragment
                  "gentufa parse has no supported statement root"
                  (sort (set->list (parse-case-variants parse-case)) symbol<?))]))

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
          (for/list ([label (in-range 1 (add1 total))]
                     #:unless (hash-has-key? fills label))
            (cons label (string->symbol (format "$ctx~a" label)))))
        (for ([entry (in-list missing)])
          (hash-set! fills (car entry) (cdr entry)))
        (define event-variable '$event)
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
       (define walked (for/list ([item (in-list value)] [index (in-naturals)])
                        (walk item (datum-head value) index)))
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
              walked)])]))
  (values (walk datum) (reverse expansions)))

(define (redex-alpha-equivalent? left right)
  (define left-adapter (core->redex-adapter (datum->core left 'alpha-left)))
  (define right-adapter (core->redex-adapter (datum->core right 'alpha-right)))
  (alpha-equivalent? SmusniCore
                     (core-redex-adapter-term left-adapter)
                     (core-redex-adapter-term right-adapter)))

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
        (if (redex-alpha-equivalent?
             (normalization-datum produced-normal)
             (normalization-datum expected-normal))
            (case-report source ordinal index 'in-fragment/matched #f
                         (lowered-rules result) expansions "matched"
                         (normalization-datum produced-normal)
                         (normalization-datum expected-normal))
            (case-report source ordinal index 'in-fragment/mismatch #f
                         (lowered-rules result) expansions "normalized terms differ"
                         (normalization-datum produced-normal)
                         (normalization-datum expected-normal)))]
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
  (define fences (candidate-fence-map))
  (define reports '())
  (define fence-reports '())
  (define fixture-property-total 0)
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
          (define sigma (parse-case->sigma parse-case (rr-case-fields rr-case) inv))
          (unless (no-lowering? sigma)
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
