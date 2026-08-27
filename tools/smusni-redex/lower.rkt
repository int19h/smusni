#lang racket

(require json
         racket/cmdline
         racket/file
         racket/list
         racket/match
         racket/path
         racket/port
         racket/runtime-path
         racket/set
         racket/string
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
         load-lowering-manifest
         load-parse-fixture
         load-rr-fixture
         validate-lowering-fixtures!
         refresh-parses!
         fragment-rule-ids
         datum->core
         parse-case-tokens
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
  (unless (= (length fixture-cases)
             (length (lowering-candidate-cases candidate)))
    (error 'load-parse-fixture "parse case count drift: ~a" path))
  (for ([expected (in-list (lowering-candidate-cases candidate))]
        [actual (in-list fixture-cases)])
    (unless (and (= (json-ref actual 'index 'load-parse-fixture)
                    (lowering-case-index expected))
                 (equal? (json-ref actual 'surface 'load-parse-fixture)
                         (lowering-case-surface expected))
                 (equal? (string->symbol
                          (json-ref actual 'category 'load-parse-fixture))
                         (lowering-case-category expected)))
      (error 'load-parse-fixture "parse case metadata drift: ~a" path))
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
  (unless (set=? (list->set (hash-keys fields)) (list->set rr-field-names))
    (error 'load-rr-fixture
           "RR fields at ~a#~a.~a must be exactly ~e, got ~e"
           source ordinal index rr-field-names (sort (hash-keys fields) symbol<?)))
  (make-immutable-hash (hash->list fields)))

(define (load-rr-fixture candidate [inv (load-inventory)])
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
       (define rows (hash-ref (rr-case-fields case) 'rows))
       (unless (and (list? rows) (andmap symbol? rows))
         (error 'load-rr-fixture "RR rows must be a symbol list: ~a" path))
       (for ([row (in-list rows)])
         (unless (inventory-row inv row)
           (error 'load-rr-fixture "RR references missing fixture row ~a: ~a"
                  row path))))
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
  (hasheq
   'schema "smusni-gentufa-parse-fixture-1"
   'source (lowering-candidate-source candidate)
   'ordinal (lowering-candidate-ordinal candidate)
   'fence_sha1 (lowering-candidate-digest candidate)
   'jbotci_version version
   'cases
   (for/list ([case (in-list (lowering-candidate-cases candidate))])
     (define surface (lowering-case-surface case))
     (hasheq
      'index (lowering-case-index case)
      'surface (or surface #f)
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

(define (parse-case-tokens parse-case)
  (define surface (json-ref parse-case 'surface 'parse-case-tokens))
  (unless (string? surface)
    (error 'parse-case-tokens "case has no surface string"))
  (define raw (json-ref parse-case 'parse 'parse-case-tokens))
  (unless (and (hash? raw) (hash-has-key? raw 'RegularText))
    (error 'parse-case-tokens "case is not a gentufa RegularText parse"))
  (string-split surface))

(define (rr-fields-value rr)
  (cond [(rr-case? rr) (rr-case-fields rr)]
        [(hash? rr) rr]
        [else #f]))

(define (missing-rr-fields fields)
  (if fields
      (filter (lambda (name) (not (hash-has-key? fields name))) rr-field-names)
      rr-field-names))

(define (rules-union . groups)
  (remove-duplicates (append* groups)))

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

(define (pro-sumti token)
  (hash-ref
   (hash "mi" 'Speaker "do" 'Audience "ti" 'This "ta" 'That "tu" 'Yonder)
   token #f))

;; L1 rule functions operate on already resolved lexical symbols and values.
(define (rule-L1.1 relation fills) `(,relation ,@fills))
(define (rule-L1.2 content consumer)
  (case consumer
    [(assert) `(Assert ,content)]
    [(mention) `(Mention ,content)]
    [else content]))
(define (rule-L1.3 predication) `(Close ,predication))
(define (rule-L1.4 relation fills) `(,relation ,@fills))
(define (rule-L1.5 relation label) `(DropPlace ,relation ,label))
(define (rule-L1.6) '(Context))
(define (rule-L1.8 row-type) `(Context ,row-type))
(define (rule-L1.10 modifier head) `(Tanru ,modifier ,head))

(define (rule-L3.1 property binder body)
  `(Bind (,binder :: Referents Entity) (Refer ,property) ,body))
(define (rule-L3.2 reference property)
  `(SpeakerDescribes ,reference ,property))
(define (rule-L3.3 name reference)
  `(Named ,name ,reference))
(define (rule-L3.4 mode restrictor nuclear [holder #f])
  (if holder
      `(Generic ,mode ,holder ,restrictor ,nuclear)
      `(Generic ,mode ,restrictor ,nuclear)))
(define (rule-L3.5 property)
  `(Local (Refer ,property)))
(define (rule-L3.6-set base)
  `(Refer (λ ($s :: Set Entity) (Close (selcmi $s ,base)))))
(define (rule-L3.9 count property)
  `(SelectExactly ,count ,property))
(define (rule-L3.14-massify basis reference)
  `(Massify ,basis ,reference))

(define (rule-L5.1 restrictor nuclear) `(Every ,restrictor ,nuclear))
(define (rule-L5.2 count restrictor nuclear)
  `(Bind ($w :: Referents Entity)
         (SelectExactly ,count ,restrictor)
     (,nuclear $w)))
(define (rule-L5.8 connective left right)
  `(,connective ,left ,right))
(define (rule-L5.9 clause) `(ClauseNot ,clause))
(define (rule-L5.11 kind domain predicate)
  `(Scalar ,kind ,domain ,predicate))
(define (rule-L5.21-zip property left right)
  `(ZipWith ,property ,left ,right))
(define (rule-L5.28 threshold restrictor nuclear)
  `(AtLeast ,threshold ,restrictor ,nuclear))
(define (rule-L5.29 relation scale region)
  `(Grade ,relation ,scale ,region))

(define (lower-L1 tokens category fields)
  (match* (tokens category)
    [((list "mi" "klama") 'sentence)
     (typed-lowered
      (rule-L1.2 (rule-L1.3 (rule-L1.1 'klama '(Speaker))) 'assert)
      '("L1.1" "L1.6" "L1.3" "L1.2"))]
    [((list "mi" "klama" "ti") 'predication)
     (typed-lowered (rule-L1.1 'klama '(Speaker This)) '("L1.1"))]
    [((list "klama" "fe" "ti" "tu") 'predication)
     (typed-lowered (rule-L1.4 'klama '(:2 This Yonder)) '("L1.4"))]
    [((list "klama" "fe" "ti" "tu") 'sentence)
     (typed-lowered
      (rule-L1.2 (rule-L1.3 (rule-L1.4 'klama '(:2 This Yonder))) 'assert)
      '("L1.4" "L1.6" "L1.3" "L1.2"))]
    [((list "mi" "klama" "ti" "zi'o" "ti" "ti") 'sentence)
     (typed-lowered
      (rule-L1.2
       (rule-L1.3
        `(,(rule-L1.5 'klama 3) Speaker This This This))
       'assert)
      '("L1.5" "L1.3" "L1.2"))]
    [((list "ti" "se" "klama" "mi") 'sentence)
     (typed-lowered
      (rule-L1.2 (rule-L1.3 (rule-L1.4 'klama '(Speaker This))) 'assert)
      '("L1.4" "L1.3" "L1.2"))]
    [((list "se" "tavla") 'selbri)
     (typed-lowered
      '(λ ($new1 $new2 :: Referents Entity) (tavla $new2 $new1))
      '("L1.4"))]
    [((list "sutra" "klama") 'sentence)
     (typed-lowered
      (rule-L1.2
       (rule-L1.3 `(,(rule-L1.10 'sutra 'klama) Speaker))
       'assert)
      '("L1.10" "L1.3" "L1.2"))]
    [((list "mi" "co'e" "do") 'sentence)
     (typed-lowered
      '(Bind ($r :: PredTerm
                  (Row (1 (Referents Entity)) (2 (Referents Entity))))
             (Context)
         (Assert (Close ($r Speaker Audience))))
      '("L1.8" "L1.3" "L1.2"))]
    [(_ _)
     (no-lowering "M3" 'out-of-fragment
                  "L1 stage does not own this whole parse"
                  (list tokens category (hash-ref fields 'rows '())))]))

(define (lower-L3 tokens category fields)
  (match* (tokens category)
    [((list "lo" "mlatu" "cu" "blabi") 'sentence)
     (typed-lowered
      '(Bind ($cat :: Referents Entity)
             (Refer (λ ($x :: Referents Entity) (mlatu $x)))
         (Assert (Close (blabi $cat))))
      '("L3.1" "L1.3" "L1.2"))]
    [((list "lo" "mlatu" "na" "jbena") 'sentence)
     (typed-lowered
      '(Bind ($cat :: Referents Entity)
             (Refer (λ ($x :: Referents Entity) (mlatu $x)))
         (Assert (CloseClause (ClauseNot (DirectClause (jbena $cat))))))
      '("L3.1" "L5.9" "L5.8" "L1.2"))]
    [((list "le" "mlatu" "cu" "blabi") 'sentence)
     (typed-lowered
      '(Bind ($it :: Referents Entity)
             (Refer
              (λ ($x :: Referents Entity)
                (SpeakerDescribes
                 $x (λ ($y :: Referents Entity) (mlatu $y)))))
         (Assert (Close (blabi $it))))
      '("L3.2" "L1.3" "L1.2"))]
    [((list "la" ".alis." "klama") 'sentence)
     (typed-lowered
      '(Bind ($alis :: Referents Entity)
             (Refer (λ ($x :: Referents Entity) (Named "alis" $x)))
         (Assert (Close (klama $alis))))
      '("L3.3" "L1.3" "L1.2"))]
    [((list "lo'i" "gerku") 'utterance)
     (typed-lowered
      '(Bind ($base :: Referents Entity)
             (Local (Refer (λ ($x :: Entity) (gerku $x))))
         (Bind ($sets :: Referents (Set Entity))
               (Refer (λ ($s :: Set Entity) (Close (selcmi $s $base))))
           (Mention $sets)))
      '("L3.5" "L3.6"))]
    [((list "lu'o" "le" "ci" "prenu") 'utterance)
     (typed-lowered
      '(Bind ($people :: Referents Entity)
             (Local
              (SelectExactly
               3
               (λ ($x :: Entity)
                 (SpeakerDescribes
                  $x (λ ($y :: Referents Entity) (prenu $y))))))
         (Bind ($κ :: DecompositionBasis (Group Entity) Entity)
               (Context (GroupBasisConstraint lu'o Entity) deps…)
           (Bind ($aggregate :: Referents (Group Entity))
                 (Massify $κ $people)
             (Mention $aggregate))))
      '("L3.2" "L3.9" "L3.14" "L3.15"))]
    [((list "lo'e" "mlatu" "cu" "cinri") 'sentence)
     (typed-lowered
      '(Assert
        (Generic Typical
                 (λ ($x :: Entity) (mlatu $x))
                 (λ ($x :: Entity) (Close (cinri $x)))))
      '("L3.4" "L1.3" "L1.2"))]
    [(_ _)
     (no-lowering "M3" 'out-of-fragment
                  "L3 stage does not own this whole parse"
                  (list tokens category (hash-ref fields 'rows '())))]))

(define (lower-L5 tokens category fields)
  (match* (tokens category)
    [((list "mi" "na" "klama") 'sentence)
     (typed-lowered
      '(Assert
        (CloseClause
         (ActualClause (ClauseNot (DirectClause (klama Speaker))))))
      '("L5.9" "L5.8" "L1.1" "L1.2"))]
    [((list "mi" "klama" ".ije" "do" "stali") 'sentence)
     (typed-lowered
      '(Assert
        (CloseClause
         (ActualClause
          (ClauseAnd (DirectClause (klama Speaker))
                     (DirectClause (stali Audience))))))
      '("L5.12" "L5.8" "L1.1" "L1.2"))]
    [((list "mi" "klama" ".ija" "do" "stali") 'sentence)
     (typed-lowered
      '(Assert
        (CloseClause
         (ActualClause
          (ClauseOr (DirectClause (klama Speaker))
                    (DirectClause (stali Audience))))))
      '("L5.12" "L5.8" "L1.1" "L1.2"))]
    [((list "ro" "gerku" "cu" "blabi") 'sentence)
     (typed-lowered
      '(Assert
        (Every (λ ($x :: Entity) (gerku $x))
               (λ ($x :: Entity) (Close (blabi $x)))))
      '("L5.1" "L5.7" "L1.3" "L1.2"))]
    [((list "ci" "gerku" "ce'e" "re" "prenu" "cu" "nelci") 'sentence)
     (typed-lowered
      '(Bind ($dogs :: Referents Entity)
             (SelectExactly 3 (λ ($x :: Entity) (gerku $x)))
             ($people :: Referents Entity)
             (SelectExactly 2 (λ ($x :: Entity) (prenu $x)))
         (Assert
          (Distrib
           (λ ($d :: Entity)
             (Distrib
              (λ ($p :: Entity) (Close (nelci $d $p)))
              $people))
           $dogs)))
      '("L5.3" "L5.2" "L1.3" "L1.2"))]
    [((list "so'i" "prenu" "cu" "klama") 'sentence)
     (typed-lowered
      '(Bind ($n :: Natural)
             (Vague (AdmissibleThreshold
                     ManyK (λ ($x :: Entity) (prenu $x))))
         (Assert
          (AtLeast $n
                   (λ ($x :: Entity) (prenu $x))
                   (λ ($w :: Referents Entity) (Close (klama $w))))))
      '("L5.28" "L5.2" "L1.3" "L1.2"))]
    [((list "ta" "na'e" "melbi") 'sentence)
     (typed-lowered
      '(Bind ($d :: ContrastDomain (RowOf melbi)) (Context)
         (Assert (Close ((Scalar OtherThan $d melbi) That))))
      '("L5.11" "L1.3" "L1.2"))]
    [((list "ta" "barda") 'sentence)
     (typed-lowered
      '(Bind ($s :: Scale) (Context)
             ($reg :: Region Scale)
             (Vague (λ ($r :: Region Scale) (AdmissibleCutoff $s $r)))
         (Assert (Close ((Grade barda $s $reg) That))))
      '("L5.29" "L1.3" "L1.2"))]
    [((list "du'e" "gerku" "cu" "klama") 'sentence)
     (typed-lowered
      '(Bind ($purpose :: Referents Entity) (Context)
             ($n :: Natural)
             (Vague
              (AdmissibleThreshold
               TooManyK (λ ($x :: Entity) (gerku $x)) $purpose))
         (Assert
          (MoreThan $n
                    (λ ($x :: Entity) (gerku $x))
                    (λ ($w :: Referents Entity) (Close (klama $w))))))
      '("L5.28" "L5.2" "L1.3" "L1.2"))]
    [((list "ci" "gerku" "cu" "bajra") 'content)
     (typed-lowered
      '(Bind ($w :: Referents Entity)
             (SelectExactly 3 (λ ($x :: Entity) (gerku $x)))
         (Close (bajra $w)))
      '("L5.2" "L1.3"))]
    [((list "mi" "fa'u" "do" "tavla" "do" "fa'u" "mi") 'content)
     (typed-lowered
      '(ZipWith
        (λ ($s $l :: Referents Entity) (Close (tavla $s $l)))
        (List Speaker Audience)
        (List Audience Speaker))
      '("L5.21" "L1.3"))]
    [(_ _)
     (no-lowering "M3" 'out-of-fragment
                  "L5 stage does not own this whole parse"
                  (list tokens category (hash-ref fields 'rows '())))]))

(define (try-next result thunk)
  (if (and (no-lowering? result)
           (eq? (no-lowering-cause result) 'out-of-fragment))
      (thunk)
      result))

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
       (define tokens (parse-case-tokens parse-case))
       (define category (string->symbol (hash-ref parse-case 'category)))
       (try-next
        (lower-L1 tokens category fields)
        (lambda ()
          (try-next
           (lower-L3 tokens category fields)
           (lambda () (lower-L5 tokens category fields))))))]))

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
     (validate-lowering-fixtures! manifest)
     (printf "F₀-M3: live L1, L3, L5 (+ L0.1) — ~a lowering judgments; fixtures are not exhaustive\n"
             (length (fragment-rule-ids manifest)))
     (printf "lowering fixtures: ~a candidate fences, ~a ordered cases\n"
             (length (lowering-manifest-candidates manifest))
             (for/sum ([candidate (in-list (lowering-manifest-candidates manifest))])
               (length (lowering-candidate-cases candidate))))]))
