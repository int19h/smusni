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
  [(route-out (se-lambda tavla))
   (λ ($new1 $new2 :: Referents Entity) (tavla $new2 $new1))])

(define-metafunction SmusniM3
  connective-out : e e e -> e
  [(connective-out not (pred x_R e_arg ...) none)
   (ClauseNot (DirectClause (x_R e_arg ...)))]
  [(connective-out and (pred x_R e_arg ...) (pred x_S e_arg_2 ...))
   (ClauseAnd (DirectClause (x_R e_arg ...))
              (DirectClause (x_S e_arg_2 ...)))]
  [(connective-out or (pred x_R e_arg ...) (pred x_S e_arg_2 ...))
   (ClauseOr (DirectClause (x_R e_arg ...))
             (DirectClause (x_S e_arg_2 ...)))])

(define-metafunction SmusniM3
  nuclear-out : e e e -> e
  [(nuclear-out e_var Entity e_body)
   (λ (e_var :: Entity) e_body)]
  [(nuclear-out e_var (Referents Entity) e_body)
   (λ (e_var :: Referents Entity) e_body)])

(define-metafunction SmusniM3
  le-out : x e e -> e
  [(le-out x_P (pure described x_P) e_property) e_property]
  [(le-out x_P e_continuation e_body)
   (Bind ($it :: Referents Entity)
         (Refer
          (λ ($x :: Referents Entity)
            (SpeakerDescribes
             $x (λ ($y :: Referents Entity) (x_P $y)))))
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

  [--------------------------------------------- "L1.8"
   (m3-lower e_RR (gentufa e_parse cohe)
             (Bind ($r :: PredTerm
                         (Row (1 (Referents Entity)) (2 (Referents Entity))))
                   (Context)
               (Assert (Close ($r Speaker Audience)))))]

  [(where e_relation (Tanru x_M x_H))
   (where e_out (apply* e_relation (e_arg ...)))
   --------------------------------------------- "L1.10"
   (m3-lower e_RR (gentufa e_parse (tanru x_M x_H e_arg ...)) e_out)]

  [(m3-lower e_RR (gentufa e_parse e_continuation) e_body)
   --------------------------------------------- "L3.1"
   (m3-lower e_RR (gentufa e_parse (lo x_P e_continuation))
             (Bind ($cat :: Referents Entity)
                   (Refer (λ ($x :: Referents Entity) (x_P $x)))
               e_body))]

  [(m3-lower e_RR (gentufa e_parse e_continuation) e_body)
   (where e_out (le-out x_P e_continuation e_body))
   --------------------------------------------- "L3.2"
   (m3-lower e_RR (gentufa e_parse (le x_P e_continuation))
             e_out)]

  [(m3-lower e_RR (gentufa e_parse e_continuation) e_body)
   --------------------------------------------- "L3.3"
   (m3-lower e_RR (gentufa e_parse (la e_name e_continuation))
             (Bind ($alis :: Referents Entity)
                   (Refer (λ ($x :: Referents Entity) (Named e_name $x)))
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

  [--------------------------------------------- "L5.3"
   (m3-lower e_RR (gentufa e_parse (termset))
             (Bind ($dogs :: Referents Entity)
                   (SelectExactly 3 (λ ($x :: Entity) (gerku $x)))
                   ($people :: Referents Entity)
                   (SelectExactly 2 (λ ($x :: Entity) (prenu $x)))
               (Assert
                (Distrib
                 (λ ($d :: Entity)
                   (Distrib
                    (λ ($p :: Entity) (Close (nelci $d $p)))
                    $people))
                 $dogs))))]

  [(m3-lower e_RR (gentufa e_parse (close shorthand (pred x_Q e_var))) e_body)
   (where e_out (nuclear-out e_var e_type e_body))
   --------------------------------------------- "L5.7"
  (m3-lower e_RR (gentufa e_parse (nuclear e_var e_type x_Q))
             e_out)]

  [(where e_out (connective-out e_kind e_left e_right))
   --------------------------------------------- "L5.8"
   (m3-lower e_RR (gentufa e_parse
                            (clause-connect e_kind e_left e_right))
             e_out)]

  [(m3-lower e_RR (gentufa e_parse
                            (clause-connect not e_source none)) e_out)
   --------------------------------------------- "L5.9"
   (m3-lower e_RR (gentufa e_parse (na e_source)) e_out)]

  [--------------------------------------------- "L5.11"
   (m3-lower e_RR (gentufa e_parse (scalar x_P e_arg))
             (Bind ($d :: ContrastDomain (RowOf x_P)) (Context)
               (Assert (Close ((Scalar OtherThan $d x_P) e_arg)))))]

  [(m3-lower e_RR (gentufa e_parse
                            (clause-connect e_kind e_left e_right)) e_clause)
   --------------------------------------------- "L5.12"
   (m3-lower e_RR (gentufa e_parse
                            (sentence-connect e_kind e_left e_right))
             e_clause)]

  [--------------------------------------------- "L5.21"
   (m3-lower e_RR (gentufa e_parse zip)
             (ZipWith
              (λ ($s $l :: Referents Entity) (Close (tavla $s $l)))
              (List Speaker Audience)
              (List Audience Speaker)))]

  [(m3-lower e_RR (gentufa e_parse (pure lexical x_P)) e_P)
   (m3-lower e_RR (gentufa e_parse
                            (nuclear $w (Referents Entity) x_Q)) e_Q)
   (where e_out (threshold-out e_kind e_P e_Q))
   --------------------------------------------- "L5.28"
   (m3-lower e_RR (gentufa e_parse (threshold e_kind x_P x_Q)) e_out)]

  [--------------------------------------------- "L5.29"
   (m3-lower e_RR (gentufa e_parse grade)
             (Bind ($s :: Scale) (Context)
                   ($reg :: Region Scale)
                   (Vague (λ ($r :: Region Scale)
                            (AdmissibleCutoff $s $r)))
               (Assert (Close ((Grade barda $s $reg) That)))))] )

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

(define (parse-case->sigma parse-case)
  (define tokens (parse-case-tokens parse-case))
  (define category (string->symbol (hash-ref parse-case 'category)))
  (match* (tokens category)
    [((list "mi" "klama") 'sentence)
     '(force assert (close shorthand (omit (pred klama Speaker))))]
    [((list "mi" "klama" "ti") 'predication)
     '(pred klama Speaker This)]
    [((list "klama" "fe" "ti" "tu") 'predication)
     '(route (application klama :2 This Yonder))]
    [((list "klama" "fe" "ti" "tu") 'sentence)
     '(force assert
             (close shorthand
                    (omit (route (application klama :2 This Yonder)))))]
    [((list "mi" "klama" "ti" "zi'o" "ti" "ti") 'sentence)
     '(force assert
             (close shorthand (drop klama 3 Speaker This This This)))]
    [((list "ti" "se" "klama" "mi") 'sentence)
     '(force assert
             (close shorthand (route (application klama Speaker This))))]
    [((list "se" "tavla") 'selbri) '(route (se-lambda tavla))]
    [((list "sutra" "klama") 'sentence)
     '(force assert (close shorthand (tanru sutra klama Speaker)))]
    [((list "mi" "co'e" "do") 'sentence) 'cohe]

    [((list "lo" "mlatu" "cu" "blabi") 'sentence)
     '(lo mlatu (force assert (close shorthand (pred blabi $cat))))]
    [((list "lo" "mlatu" "na" "jbena") 'sentence)
     '(lo mlatu (force assert (close clause (na (pred jbena $cat)))))]
    [((list "le" "mlatu" "cu" "blabi") 'sentence)
     '(le mlatu (force assert (close shorthand (pred blabi $it))))]
    [((list "la" ".alis." "klama") 'sentence)
     '(la "alis" (force assert (close shorthand (omit (pred klama $alis)))))]
    [((list "lo'i" "gerku") 'utterance) '(collection-set gerku)]
    [((list "lu'o" "le" "ci" "prenu") 'utterance) '(luho 3 prenu)]
    [((list "lo'e" "mlatu" "cu" "cinri") 'sentence)
     '(force assert (generic mlatu cinri))]

    [((list "mi" "na" "klama") 'sentence)
     '(force assert (close actual (na (pred klama Speaker))))]
    [((list "mi" "klama" ".ije" "do" "stali") 'sentence)
     '(force assert
             (close actual
                    (sentence-connect and
                                      (pred klama Speaker)
                                      (pred stali Audience))))]
    [((list "mi" "klama" ".ija" "do" "stali") 'sentence)
     '(force assert
             (close actual
                    (sentence-connect or
                                      (pred klama Speaker)
                                      (pred stali Audience))))]
    [((list "ro" "gerku" "cu" "blabi") 'sentence)
     '(force assert (every gerku blabi))]
    [((list "ci" "gerku" "ce'e" "re" "prenu" "cu" "nelci") 'sentence)
     '(termset)]
    [((list "so'i" "prenu" "cu" "klama") 'sentence)
     '(threshold many prenu klama)]
    [((list "ta" "na'e" "melbi") 'sentence) '(scalar melbi That)]
    [((list "ta" "barda") 'sentence) 'grade]
    [((list "du'e" "gerku" "cu" "klama") 'sentence)
     '(threshold too-many gerku klama)]
    [((list "ci" "gerku" "cu" "bajra") 'content)
     '(cardinal 3 gerku bajra)]
    [((list "mi" "fa'u" "do" "tavla" "do" "fa'u" "mi") 'content)
     'zip]
    [(_ _)
     (no-lowering "M3" 'out-of-fragment
                  "no Redex source view for the whole parse"
                  (list tokens category))]))

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
  (define sigma (parse-case->sigma parse-case))
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
          (define sigma (parse-case->sigma parse-case))
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
