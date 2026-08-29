#lang racket

(require file/sha1
         racket/cmdline
         racket/file
         racket/format
         racket/list
         racket/match
         racket/path
         racket/port
         racket/pretty
         racket/runtime-path
         racket/set
         racket/string
         racket/system
         redex/reduction-semantics
         "extract.rkt"
         "inventory.rkt"
         "lower.rkt"
         "port-a0.rkt"
         "syntax.rkt"
         "types.rkt")

(provide (struct-out definition-observation)
         (struct-out definition-entry)
         (struct-out definition-domain)
         (struct-out case-registration)
         (struct-out branch-observation)
         (struct-out branch-entry)
         (struct-out helper-observation)
         (struct-out helper-entry)
         (struct-out decision-observation)
         (struct-out decision-entry)
         (struct-out value-helper-observation)
         (struct-out value-helper-entry)
         (struct-out diagnostic-taxonomy)
         (struct-out port-case)
         (struct-out port-record)
         (struct-out benchmark-mode)
         (struct-out target-migration)
         extract-definition-observations
         definition-observation-source-digest
         definition-ranges-source-digest
         load-definition-ledger
         definition-ledger-findings
         definition-implementation-index
         implementation-defined?
         extract-infer-branches
         load-infer-branches
         extract-infer-helpers
         load-infer-helpers
         extract-infer-decisions
         load-infer-decisions
         extract-infer-value-helpers
         load-infer-value-helpers
         refresh-infer-branch-metadata!
         infer-branch-findings
         load-diagnostic-taxonomy
         diagnostic-taxonomy-findings
         load-port-corpus
         collect-port-cases
         refresh-port-corpus!
         validate-port-case-inventories!
         run-differential
         run-a0-differential
         legacy-datum->a0
         a0-port-record
         a0-corpus-eligible?
         a0-mechanism-cases
         a0-differential-cases
         load-b1-lowering-manifest
         refresh-b1-lowering-manifest!
         b1-lowering-manifest-findings
         load-a0-waivers
         load-port-waivers
         load-target-migrations
         target-migration-findings
         load-b1-growth-profile
         run-benchmarks
         run-benchmark-mode
         specimen-benchmark-cases
         a0-specimen-benchmark-cases
         benchmark-mode->datum
         datum->benchmark-mode
         load-port-baseline
         refresh-port-baseline!
         report-full-gate-trigger
         run-phase0-gate)

(define-runtime-path tool-dir ".")
(define repo-root (simplify-path (build-path tool-dir ".." "..")))
(define spec-path (build-path repo-root "spec.md"))
(define types-path (build-path tool-dir "types.rkt"))
(define lower-path (build-path tool-dir "lower.rkt"))
(define tests-dir (build-path tool-dir "tests"))
(define trace-runner-path (build-path tool-dir "port-trace-runner.rkt"))
(define benchmark-worker-path (build-path tool-dir "port-benchmark-worker.rkt"))
(define inventory-dir (build-path tool-dir "inventory"))
(define definitions-path (build-path inventory-dir "definitions.sexp"))
(define infer-branches-path (build-path inventory-dir "infer-core-branches.sexp"))
(define diagnostics-path (build-path inventory-dir "diagnostics.sexp"))
(define port-corpus-path (build-path inventory-dir "port-corpus.sexp"))
(define port-waivers-path (build-path inventory-dir "port-waivers.sexp"))
(define a0-waivers-path (build-path inventory-dir "a0-waivers.sexp"))
(define port-baseline-path (build-path inventory-dir "port-baseline.sexp"))
(define production-modules-path
  (build-path inventory-dir "port-production-modules.sexp"))
(define target-migrations-path
  (build-path inventory-dir "target-migrations.sexp"))
(define b1-lowering-manifest-path
  (build-path inventory-dir "b1-lowering-subterms.sexp"))
(define b1-growth-profile-path
  (build-path inventory-dir "b1-growth-profile.sexp"))

(define definition-statuses
  '(executable primitive-or-partial-operator mapping-schema
    metatheory-or-model-law prose-only-gap blocked not-a-definition))
(define branch-classes
  '(semantic-clause auxiliary external-gap-or-diagnostic blocked
    obsolete-or-bug))

(define (file-digest path)
  (call-with-input-file path sha1))

(define (datum-digest value)
  (sha1 (open-input-string (format "~s" value))))

(define (sentence? text)
  (and (string? text)
       (regexp-match? #px"[.!?]$" (string-trim text))))

;; --------------------------------------------------------------------------
;; P0.1: live definition extraction and classified ledger

(struct definition-observation (head section lines lhs) #:transparent)
(struct definition-entry
  (id head section spec-source-sha1 spec-source-ranges
      equation-source-sha1 equation-ranges
      status issue port-state dependencies implementations
      legacy-implementations domains reason)
  #:transparent)
(struct definition-domain (name status issue port-state reason) #:transparent)
(struct target-migration (family source targets extent reason) #:transparent)

(define port-states '(none legacy-hybrid a0 ported))

(define (heading-section line current)
  (match (regexp-match #px"^#{2,4} +([0-9]+(?:[.][0-9]+)*)[.]? +" line)
    [(list _ section) section]
    [_ current]))

(define (backtick-count text)
  (count (lambda (character) (char=? character #\`))
         (string->list text)))

(define (last-index text character)
  (for/fold ([found #f]) ([candidate (in-string text)] [index (in-naturals)])
    (if (char=? candidate character) index found)))

(define (definition-context lines index stop)
  (define start (max 0 (- index 2)))
  (define prior (take (drop lines start) (- index start)))
  (define prefix (substring (list-ref lines index) 0 stop))
  (define context (string-join (append prior (list prefix)) "\n"))
  (define trimmed-prefix (string-trim prefix))
  (define direct-prefix?
    (and (not (string-contains? trimmed-prefix "`"))
         (or (regexp-match? #px"^[({]" trimmed-prefix)
             (regexp-match? #px"^[^[:space:]()]+[[:space:]]*[(]" trimmed-prefix)
             (regexp-match? #px"^SelectSome[[:space:]]" trimmed-prefix))))
  (define ticks (backtick-count context))
  (define tick (last-index context #\`))
  (define inline
    (cond
      [direct-prefix? prefix]
      [(and tick (odd? ticks)) (substring context (add1 tick))]
      [(and tick (positive? tick)
            (string-suffix? (string-trim context) "`"))
       (define previous
         (for/fold ([found #f]) ([character (in-string context)]
                                 [position (in-naturals)]
                                 #:when (and (< position tick)
                                             (char=? character #\`)))
           position))
       (and previous (substring context (add1 previous) tick))]
      [else prefix]))
  (define candidate
    (string-trim
     (regexp-replace #px"^(?:lisp|text)[[:space:]]*\n" (or inline prefix) "")))
  (if (or (string=? candidate "")
          (regexp-match? #px"^[=:;,-]*$" candidate))
      (let ([previous
             (for/first ([line (in-list (reverse prior))]
                         #:unless (string=? (string-trim line) ""))
               (string-trim line))])
        (or previous candidate))
      candidate))

(define (clean-head token)
  (define cleaned
    (regexp-replace* #px"^[`'{]+|[`'},;:.]+$" (string-trim token) ""))
  (and (not (string=? cleaned "")) (string->symbol cleaned)))

(define (head-from-definition-context lhs full-line)
  (cond
    [(regexp-match? #px"`na'i` +objection" full-line)
     '|na'i-objection-prose|]
    [(or (regexp-match? #px"COI +schemas" full-line)
         (string=? (string-trim lhs) "schemas"))
     'COI-schemas-prose]
    [(regexp-match #px"^\\s*`*\\s*\\(\\(?\\s*([^\\s()]+)" lhs)
     => (lambda (match) (clean-head (second match)))]
    [(regexp-match #px"^\\s*`*\\s*\\{\\s*([^\\s\\[]+)" lhs)
     => (lambda (match) (clean-head (second match)))]
    [(regexp-match #px"^\\s*([^\\s(]+)\\s*\\(" lhs)
     => (lambda (match) (clean-head (second match)))]
    [(regexp-match #px"(?:^|\\s)([><≤≥])(?:\\s|$)" lhs)
     => (lambda (match) (clean-head (second match)))]
    [(regexp-match #px"^\\s*([^\\s]+)" lhs)
     => (lambda (match) (clean-head (second match)))]
    [else #f]))

(define (extract-definition-observations [path spec-path])
  (define lines (file->lines path))
  (define current-section "preamble")
  (define found (make-hash))
  (for ([line (in-list lines)] [index (in-naturals)])
    (set! current-section (heading-section line current-section))
    (for ([position (in-list (regexp-match-positions* #px"≝" line))])
      (define lhs (definition-context lines index (car position)))
      (define head (head-from-definition-context lhs line))
      (unless head
        (error 'extract-definition-observations
               "cannot extract definition head at ~a:~a: ~s"
               path (add1 index) line))
      (define key (cons head current-section))
      (define prior (hash-ref found key #f))
      (hash-set!
       found key
       (if prior
           (definition-observation
            head current-section
            (append (definition-observation-lines prior) (list (add1 index)))
            (append (definition-observation-lhs prior) (list lhs)))
           (definition-observation head current-section (list (add1 index))
                                   (list lhs))))))
  (sort (hash-values found)
        string<?
        #:key (lambda (observation)
                (format "~a:~a" (definition-observation-section observation)
                        (definition-observation-head observation)))))

(define (parse-status raw)
  (match raw
    [(? symbol? status)
     (unless (member status definition-statuses)
       (error 'load-definition-ledger "unknown definition status: ~e" status))
     (values status #f)]
    [`(blocked ,(? string? issue))
     (unless (regexp-match? #px"^#[1-9][0-9]*$" issue)
       (error 'load-definition-ledger "blocked status needs issue, got ~e" issue))
     (values 'blocked issue)]
    [_ (error 'load-definition-ledger "invalid definition status: ~e" raw)]))

(define (parse-definition-ranges id label raw-ranges)
  (for/list ([range (in-list raw-ranges)])
    (match range
      [`(,(? exact-positive-integer? start)
         ,(? exact-positive-integer? end))
       #:when (<= start end) (list start end)]
      [_ (error 'load-definition-ledger
                "definition ~a has invalid ~a range ~e" id label range)])))

(define (load-definition-ledger [path definitions-path])
  (match (call-with-input-file path read)
    [`(smusni-definition-ledger 1 ,raw-entries ...)
     (for/list ([raw (in-list raw-entries)])
       (match raw
         [`(definition (id ,(? string? id)) (head ,(? symbol? head))
                       (section ,(? string? section))
                       (spec-source-sha1 ,spec-source-sha1)
                       (spec-source-ranges ,raw-ranges ...)
                       ,tail ...)
          (define-values
            (equation-source-sha1 raw-equation-ranges remainder)
            (match tail
              [`((equation-source-sha1 ,digest)
                 (equation-ranges ,equation-ranges ...) ,rest ...)
               (values digest equation-ranges rest)]
              [_ (values 'none '() tail)]))
          (match remainder
            [`((status ,raw-status)
               (port-state ,(? symbol? port-state))
               (dependencies ,(? symbol? dependencies) ...)
               (legacy-implementations ,legacy ...)
               (implementations ,implementations ...)
               (domains ,raw-domains ...)
               (reason ,(? string? reason)))
             (define-values (status issue) (parse-status raw-status))
             (unless (member port-state port-states)
               (error 'load-definition-ledger "invalid port state in ~a: ~e"
                      id port-state))
             (unless (or (eq? status 'executable) (sentence? reason))
               (error 'load-definition-ledger
                      "non-executable ~a needs a one-sentence reason" id))
             (define domains
               (for/list ([raw-domain (in-list raw-domains)])
                 (match raw-domain
                   [`(domain ,(? symbol? name) (status ,domain-status)
                             (port-state ,(? symbol? domain-port-state))
                             (reason ,(? string? domain-reason)))
                    (define-values (parsed-status parsed-issue)
                      (parse-status domain-status))
                    (unless (sentence? domain-reason)
                      (error 'load-definition-ledger
                             "definition ~a domain ~a needs one sentence" id))
                    (unless (member domain-port-state port-states)
                      (error 'load-definition-ledger
                             "definition ~a domain ~a has invalid port state ~e"
                             id name domain-port-state))
                    (definition-domain name parsed-status parsed-issue
                                       domain-port-state domain-reason)]
                   [_ (error 'load-definition-ledger
                             "invalid definition domain in ~a: ~e"
                             id raw-domain)])))
             (for ([digest (in-list (list spec-source-sha1
                                          equation-source-sha1))]
                   [label (in-list '(spec-source equation-source))])
               (unless (or (eq? digest 'none) (string? digest))
                 (error 'load-definition-ledger
                        "definition ~a has invalid ~a sha1" id label)))
             (define spec-source-ranges
               (parse-definition-ranges id 'source raw-ranges))
             (define equation-ranges
               (parse-definition-ranges id 'equation raw-equation-ranges))
             (unless (eq? (eq? equation-source-sha1 'none)
                          (null? equation-ranges))
               (error 'load-definition-ledger
                      "definition ~a equation digest/ranges disagree" id))
             (definition-entry
              id head section spec-source-sha1 spec-source-ranges
              equation-source-sha1 equation-ranges
              status issue port-state dependencies implementations legacy
              domains reason)]
            [_ (error 'load-definition-ledger
                      "invalid definition tail in ~a: ~e" id remainder)])]
         [_ (error 'load-definition-ledger
                   "invalid definition entry: ~e" raw)]))]
    [_ (error 'load-definition-ledger "unsupported definitions ledger")]))

(define (definition-key item)
  (cons (if (definition-entry? item)
            (definition-entry-head item)
            (definition-observation-head item))
        (if (definition-entry? item)
            (definition-entry-section item)
            (definition-observation-section item))))

(define (definition-observation-source-digest observation [path spec-path])
  (define lines (file->lines path))
  (datum-digest
   (for/list ([line-number (in-list (definition-observation-lines observation))])
     (list line-number (list-ref lines (sub1 line-number))))))

(define (definition-ranges-source-digest ranges [path spec-path])
  (define lines (file->lines path))
  (datum-digest
   (for*/list ([range (in-list ranges)]
               [line-number (in-range (first range) (add1 (second range)))])
     (list line-number (list-ref lines (sub1 line-number))))))

(define (equation-range-rhs range [path spec-path])
  (define lines (file->lines path))
  (define source
    (string-join
     (for/list ([line-number (in-range (first range) (add1 (second range)))])
       (first (string-split (list-ref lines (sub1 line-number)) ";")))
     "\n"))
  (define marker
    (match (regexp-match-positions #px"≝" source)
      [(list (cons _ end)) end]
      [_ #f]))
  (unless marker
    (error 'equation-range-rhs "equation range ~e contains no ≝" range))
  (define raw-rhs (string-trim (substring source marker)))
  (define rhs-fragment
    (match (regexp-match #px"^`([^`]*)`" raw-rhs)
      [(list _ inline) inline]
      [_
       (match (regexp-match #px"^([^`]*)`" raw-rhs)
         [(list _ inline) inline]
         [_ raw-rhs])]))
  (define rhs
    (string-trim
     (regexp-replace*
      #px"n[+]1"
      (string-replace rhs-fragment "`" "")
      "(+ n 1)")))
  (define forms (map core->plain-datum (read-core-forms rhs 'definition-rhs)))
  (cond
    [(null? forms)
     (error 'equation-range-rhs "equation range ~e has an empty RHS" range)]
    [(null? (rest forms)) (first forms)]
    [else forms]))

(define (definition-semantic-head-universe entries [inv (load-inventory)])
  (set-union (list->set (hash-keys (inventory-forms inv)))
             (list->set (map definition-entry-head entries))))

(define (rhs-semantic-heads datum universe subject)
  (define (head-set head)
    (if (and (symbol? head)
             (not (eq? head subject))
             (set-member? universe head))
        (set head)
        (set)))
  (cond
    [(not (list? datum)) (set)]
    [(null? datum) (set)]
    [else
     (match datum
       [`(λ ,_ ,body)
        (set-union (head-set 'λ)
                   (rhs-semantic-heads body universe subject))]
       [`(Let ,_ ,active ,body)
        (set-union
         (head-set 'Let)
         (rhs-semantic-heads active universe subject)
         (rhs-semantic-heads body universe subject))]
       [`(Bind ,pieces ...)
        (define body (last pieces))
        (define alternating (drop-right pieces 1))
        (set-union
         (head-set 'Bind)
         (for/fold ([heads (set)])
                   ([index (in-range 1 (length alternating) 2)])
           (set-union
            heads
            (rhs-semantic-heads (list-ref alternating index)
                                universe subject)))
       (rhs-semantic-heads body universe subject))]
       [`(,head ,arguments ...)
        (for/fold ([heads (set-union
                           (head-set head)
                           (if (list? head)
                               (rhs-semantic-heads head universe subject)
                               (set)))])
                  ([argument (in-list arguments)])
          (set-union heads
                     (rhs-semantic-heads argument universe subject)))]
       [_ (set)])]))

(define (definition-equation-dependencies entry entries)
  (define universe (definition-semantic-head-universe entries))
  (for/fold ([heads (set)])
            ([range (in-list (definition-entry-equation-ranges entry))])
    (set-union
     heads
     (rhs-semantic-heads (equation-range-rhs range) universe
                         (definition-entry-head entry)))))

(define (racket-sources)
  (for/list ([path (in-directory tool-dir)]
             #:when (regexp-match? #px"[.]rkt$" (path->string path)))
    path))

(define (load-production-modules [path production-modules-path])
  (match (call-with-input-file path read)
    [`(smusni-port-production-modules 1 ,(? string? modules) ...)
     (unless (= (length modules) (set-count (list->set modules)))
       (error 'load-production-modules "duplicate production module"))
     (for ([module-path (in-list modules)])
       (unless (and (string-prefix? module-path "tools/smusni-redex/")
                    (not (string-contains? module-path "/tests/"))
                    (not (regexp-match? #px"-test[.]rkt$" module-path))
                    (file-exists? (build-path repo-root module-path)))
         (error 'load-production-modules
                "non-production or missing module in allowlist: ~a" module-path)))
     modules]
    [_ (error 'load-production-modules "unsupported production module list")]))

(define production-modules (delay (load-production-modules)))

(define (production-module-path? module-path
                                 [allowed-modules (force production-modules)])
  (and (member module-path allowed-modules) #t))

(struct case-registration (cases duplicate-binding?) #:transparent)

(define (source-relative-string path)
  (path->string (find-relative-path repo-root (simplify-path path))))

(define (definition-implementation-index #:include-tests? [include-tests? #f])
  (define index (make-hash))
  (define (record! key cases)
    (define prior (hash-ref index key #f))
    (hash-set! index key
               (case-registration
                (if prior (append (case-registration-cases prior) cases) cases)
                (and prior #t))))
  (define (walk node module-path root?)
    (when (syntax? node)
      (define parts (syntax-list node))
      (when parts
        (define head (and (pair? parts) (syntax-e (first parts))))
        (when (and (>= (length parts) 3)
                   (member (syntax-e (first parts))
                           '(define-definition-metafunction
                             define-definition-relation)))
          (define kind
            (if (eq? (syntax-e (first parts))
                     'define-definition-metafunction)
                'metafunction 'relation))
          (define name-position (if (eq? kind 'metafunction) 2 1))
          (define name (syntax-e (list-ref parts name-position)))
          (define cases
            (for*/list ([part (in-list parts)]
                        [case-parts (in-value (syntax-list part))]
                       #:when (and case-parts (= (length case-parts) 3)
                                   (eq? (syntax-e (first case-parts))
                                        'definition-case)))
              (syntax-e (second case-parts))))
          (record! (list module-path kind name) cases))
        (unless (and (not root?) (member head '(module module* module+)))
          (for ([part (in-list parts)]) (walk part module-path #f))))))
  (for* ([path (in-list (racket-sources))]
         [module-path (in-value (source-relative-string path))]
         #:when (or include-tests? (production-module-path? module-path)))
    (walk (read-module-syntax path) module-path #t))
  index)

(define (module-binding-index)
  (define index (make-hash))
  (define (record! module-path name)
    (hash-update! index module-path (lambda (names) (set-add names name)) (set)))
  (define (walk node module-path root?)
    (when (syntax? node)
      (define parts (syntax-list node))
      (when parts
        (define head (and (pair? parts) (syntax-e (first parts))))
        (cond
          [(eq? head 'define)
           (define target (and (>= (length parts) 2) (syntax->datum (second parts))))
           (cond [(symbol? target) (record! module-path target)]
                 [(pair? target) (record! module-path (car target))])]
          [(member head '(define-metafunction define-judgment-form))
           (when (>= (length parts) 3)
             (record! module-path (syntax-e (third parts))))]
          [(member head '(define-definition-metafunction))
           (when (>= (length parts) 3)
             (record! module-path (syntax-e (third parts))))]
          [(member head '(define-definition-relation))
           (when (>= (length parts) 2)
             (record! module-path (syntax-e (second parts))))])
        (unless (or (eq? head 'define)
                    (and (not root?) (member head '(module module* module+))))
          (for ([part (in-list parts)]) (walk part module-path #f))))))
  (for* ([path (in-list (racket-sources))]
         [module-path (in-value (source-relative-string path))]
        #:when (production-module-path? module-path))
    (walk (read-module-syntax path) module-path #t))
  index)

(define (implementation-defined? implementation index
                                 #:allowed-modules
                                 [allowed-modules (force production-modules)])
  (match implementation
    [`(metafunction ,(? string? module-path) ,(? symbol? name)
                    (cases ,(? symbol? cases) ...))
     (define registration
       (and (production-module-path? module-path allowed-modules)
            (hash-ref index (list module-path 'metafunction name) #f)))
     (and registration
          (not (case-registration-duplicate-binding? registration))
          (pair? cases)
          (pair? (case-registration-cases registration))
          (= (length cases) (set-count (list->set cases)))
          (= (length (case-registration-cases registration))
             (set-count (list->set (case-registration-cases registration))))
          (set=? (list->set cases)
                 (list->set (case-registration-cases registration))))]
    [`(relation ,(? string? module-path) ,(? symbol? name)
                (cases ,(? symbol? cases) ...))
     (define registration
       (and (production-module-path? module-path allowed-modules)
            (hash-ref index (list module-path 'relation name) #f)))
     (and registration
          (not (case-registration-duplicate-binding? registration))
          (pair? cases)
          (pair? (case-registration-cases registration))
          (= (length cases) (set-count (list->set cases)))
          (= (length (case-registration-cases registration))
             (set-count (list->set (case-registration-cases registration))))
          (set=? (list->set cases)
                 (list->set (case-registration-cases registration))))]
    [_ #f]))

(define (definition-ledger-findings
         [observed (extract-definition-observations)]
         [entries (load-definition-ledger)])
  (define findings '())
  (define (note! format-string . arguments)
    (set! findings (cons (apply format format-string arguments) findings)))
  (define observed-by-key
    (for/hash ([item (in-list observed)]) (values (definition-key item) item)))
  (define entries-by-key (make-hash))
  (define ids (mutable-set))
  (for ([entry (in-list entries)])
    (when (set-member? ids (definition-entry-id entry))
      (note! "duplicate definition id ~a" (definition-entry-id entry)))
    (set-add! ids (definition-entry-id entry))
    (when (hash-has-key? entries-by-key (definition-key entry))
      (note! "duplicate definition head/section ~e" (definition-key entry)))
    (hash-set! entries-by-key (definition-key entry) entry))
  (for ([(key observation) (in-hash observed-by-key)])
    (unless (hash-has-key? entries-by-key key)
      (note! "live definition head ~a in §~a at lines ~a has no ledger entry"
             (definition-observation-head observation)
             (definition-observation-section observation)
             (definition-observation-lines observation))))
  (for ([(key entry) (in-hash entries-by-key)])
    (unless (hash-has-key? observed-by-key key)
      (note! "definition ledger entry ~a is stale; ~a no longer occurs in §~a"
             (definition-entry-id entry) (definition-entry-head entry)
             (definition-entry-section entry)))
    (case (definition-entry-port-state entry)
      [(none)
       (when (or (pair? (definition-entry-implementations entry))
                 (pair? (definition-entry-legacy-implementations entry)))
         (note! "definition ~a is port-state none but names implementations"
                (definition-entry-id entry)))]
      [(legacy-hybrid)
       (when (null? (definition-entry-legacy-implementations entry))
         (note! "legacy-hybrid definition ~a names no legacy implementation"
                (definition-entry-id entry)))
       (when (pair? (definition-entry-implementations entry))
         (note! "legacy-hybrid definition ~a prematurely names target cases"
                (definition-entry-id entry)))]
      [(a0 ported)
       (unless (eq? (definition-entry-status entry) 'executable)
         (note! "ported definition ~a is not normatively executable"
                (definition-entry-id entry)))
       (when (null? (definition-entry-implementations entry))
         (note! "ported definition ~a names no implementing cases"
                (definition-entry-id entry)))
       (define observation (hash-ref observed-by-key key #f))
       (define ranges (definition-entry-spec-source-ranges entry))
       (define occurrence-lines
         (and observation (definition-observation-lines observation)))
       (define ranges-cover-occurrences?
         (and occurrence-lines (pair? ranges)
              (for/and ([line (in-list occurrence-lines)])
                (for/or ([range (in-list ranges)])
                  (<= (first range) line (second range))))))
       (when (not (and ranges-cover-occurrences?
                       (string? (definition-entry-spec-source-sha1 entry))
                       (string=?
                        (definition-entry-spec-source-sha1 entry)
                        (definition-ranges-source-digest ranges))))
         (note! "ported definition ~a has a stale or missing spec source digest"
                (definition-entry-id entry)))]))
  (for ([entry (in-list entries)])
    (define names (map definition-domain-name (definition-entry-domains entry)))
    (unless (= (length names) (set-count (list->set names)))
      (note! "definition ~a has duplicate domain entries"
             (definition-entry-id entry))))
  (for ([entry (in-list entries)]
        #:when (pair? (definition-entry-equation-ranges entry)))
    (define ranges (definition-entry-equation-ranges entry))
    (unless (and (string? (definition-entry-equation-source-sha1 entry))
                 (string=? (definition-entry-equation-source-sha1 entry)
                           (definition-ranges-source-digest ranges)))
      (note! "definition ~a has a stale equation source digest"
             (definition-entry-id entry)))
    (with-handlers ([exn:fail?
                     (lambda (exception)
                       (note! "definition ~a equation parse failed: ~a"
                              (definition-entry-id entry)
                              (exn-message exception)))])
      (define derived (definition-equation-dependencies entry entries))
      (define recorded (list->set (definition-entry-dependencies entry)))
      (unless (= (length (definition-entry-dependencies entry))
                 (set-count recorded))
        (note! "definition ~a has duplicate dependencies"
               (definition-entry-id entry)))
      (define missing (set-subtract derived recorded))
      (define extra (set-subtract recorded derived))
      (unless (and (set-empty? missing) (set-empty? extra))
        (note! "definition ~a dependency mismatch: missing=~s extra=~s"
               (definition-entry-id entry)
               (sort (set->list missing) symbol<?)
               (sort (set->list extra) symbol<?)))))
  (define bindings (module-binding-index))
  (for ([entry (in-list entries)]
        #:when (eq? (definition-entry-port-state entry) 'legacy-hybrid))
    (for ([binding (in-list (definition-entry-legacy-implementations entry))])
      (match binding
        [`(binding ,(? string? module-path) ,(? symbol? name))
         (unless (set-member? (hash-ref bindings module-path (set)) name)
           (note! "legacy-hybrid definition ~a names missing binding ~a in ~a"
                  (definition-entry-id entry) name module-path))]
        [_ (note! "legacy-hybrid definition ~a has invalid binding reference ~e"
                  (definition-entry-id entry) binding)])))
  (define implementation-index (definition-implementation-index))
  (for ([entry (in-list entries)]
        #:when (member (definition-entry-port-state entry) '(a0 ported)))
    (for ([implementation (in-list (definition-entry-implementations entry))])
      (unless (implementation-defined? implementation implementation-index)
        (note! "definition ~a names missing implementation ~e"
               (definition-entry-id entry) implementation))))
  (reverse findings))

;; --------------------------------------------------------------------------
;; P0.2: infer-core branch inventory and diagnostic taxonomy

(struct branch-observation (function pattern start-line end-line source-sha1)
  #:transparent)
(struct branch-entry
  (id function pattern start-line end-line source-sha1 class reason)
  #:transparent)
(struct helper-observation (function start-line end-line source-sha1)
  #:transparent)
(struct helper-entry (id function start-line end-line source-sha1 class reason)
  #:transparent)
(struct decision-observation
  (function kind pattern ordinal start-line end-line source-sha1)
  #:transparent)
(struct decision-entry
  (id function kind pattern ordinal start-line end-line source-sha1 class reason)
  #:transparent)
(struct value-helper-observation (name start-line end-line source-sha1)
  #:transparent)
(struct value-helper-entry (id name start-line end-line source-sha1 class reason)
  #:transparent)

(define dispatch-functions
  (hash 'infer-atom 'cond
        'infer-with-expected 'cond
        'infer-predterm-application 'match
        'infer-application 'cond
        'infer-core 'cond))
(define entry-functions
  '(infer-body infer-lambda infer-let infer-bind infer-lexical-application
               infer-logical infer-quantifier))

(define (read-module-syntax path)
  (parameterize ([read-accept-reader #t])
    (call-with-input-file path
      (lambda (in)
        (port-count-lines! in)
        (read-syntax (path->string path) in)))))

(define (syntax-list value)
  (and (syntax? value) (syntax->list value)))

(define (find-function root wanted)
  (define found #f)
  (define (walk node)
    (when (and (syntax? node) (not found))
      (define parts (syntax-list node))
      (when parts
        (when (and (>= (length parts) 3)
                   (eq? (syntax-e (first parts)) 'define)
                   (let ([signature (syntax-list (second parts))])
                     (and signature (pair? signature)
                          (eq? (syntax-e (first signature)) wanted))))
          (set! found node))
        (for ([part (in-list parts)]) (walk part)))))
  (walk root)
  found)

(define (find-dispatch root keyword)
  (define found #f)
  (define (walk node)
    (when (and (syntax? node) (not found))
      (define parts (syntax-list node))
      (when parts
        (if (and (pair? parts) (eq? (syntax-e (first parts)) keyword))
            (set! found node)
            (for ([part (in-list parts)]) (walk part))))))
  (walk root)
  found)

(define (syntax-end-line stx source-text)
  (define start-line (or (syntax-line stx) 0))
  (define position (syntax-position stx))
  (define span (syntax-span stx))
  (if (and position span (positive? position))
      (+ start-line
         (count (lambda (character) (char=? character #\newline))
                (string->list
                 (substring source-text
                            (sub1 position)
                            (min (string-length source-text)
                                 (+ (sub1 position) span))))))
      start-line))

(define (syntax-source-digest stx source-text)
  (define position (syntax-position stx))
  (define span (syntax-span stx))
  (if (and position span (positive? position))
      (sha1
       (open-input-string
        (substring source-text
                   (sub1 position)
                   (min (string-length source-text)
                        (+ (sub1 position) span)))))
      (error 'syntax-source-digest "syntax object has no source span")))

(define (defined-infer-functions module)
  (define found (make-hash))
  (define (walk node)
    (when (syntax? node)
      (define parts (syntax-list node))
      (when parts
        (when (and (>= (length parts) 3)
                   (eq? (syntax-e (first parts)) 'define))
          (define signature (syntax-list (second parts)))
          (when (and signature (pair? signature)
                     (symbol? (syntax-e (first signature)))
                     (string-prefix? (symbol->string (syntax-e (first signature)))
                                     "infer-"))
            (hash-set! found (syntax-e (first signature)) node)))
        (for ([part (in-list parts)]) (walk part)))))
  (walk module)
  found)

(define (defined-top-level-functions module)
  (define found (make-hash))
  (define (walk node)
    (when (syntax? node)
      (define parts (syntax-list node))
      (when parts
        (define signature-datum
          (and (>= (length parts) 2) (syntax->datum (second parts))))
        (define function-definition?
          (and (>= (length parts) 3)
               (eq? (syntax-e (first parts)) 'define)
               (pair? signature-datum)
               (symbol? (car signature-datum))))
        (if function-definition?
            (hash-set! found (car signature-datum) node)
            (for ([part (in-list parts)]) (walk part))))))
  (walk module)
  found)

(define (defined-top-level-values module)
  (define found (make-hash))
  (define (walk node)
    (when (syntax? node)
      (define parts (syntax-list node))
      (when parts
        (define any-definition?
          (and (>= (length parts) 3)
               (eq? (syntax-e (first parts)) 'define)))
        (define value-definition?
          (and any-definition?
               (symbol? (syntax-e (second parts)))))
        (if any-definition?
            (when value-definition?
              (hash-set! found (syntax-e (second parts)) node))
            (for ([part (in-list parts)]) (walk part))))))
  (walk module)
  found)

(define (syntax-symbols stx)
  (define found (mutable-set))
  (define (walk node)
    (when (syntax? node)
      (define parts (syntax-list node))
      (if parts
          (for ([part (in-list parts)]) (walk part))
          (when (symbol? (syntax-e node)) (set-add! found (syntax-e node))))))
  (walk stx)
  (set->list found))

(define (reachable-infer-functions module)
  (define definitions (defined-infer-functions module))
  (let loop ([todo '(infer-core)] [seen (set)])
    (cond
      [(null? todo) seen]
      [(set-member? seen (first todo)) (loop (rest todo) seen)]
      [else
       (define function (first todo))
       (define definition
         (hash-ref definitions function
                   (lambda ()
                     (error 'reachable-infer-functions
                            "reachable function ~a has no definition" function))))
       (define callees
         (filter (lambda (symbol) (hash-has-key? definitions symbol))
                 (syntax-symbols definition)))
       (loop (append (rest todo) callees) (set-add seen function))])))

(define (reachable-top-level-functions module)
  (define definitions (defined-top-level-functions module))
  (let loop ([todo '(infer-core)] [seen (set)])
    (cond
      [(null? todo) seen]
      [(set-member? seen (first todo)) (loop (rest todo) seen)]
      [else
       (define function (first todo))
       (define definition
         (hash-ref definitions function
                   (lambda ()
                     (error 'reachable-top-level-functions
                            "reachable function ~a has no definition" function))))
       (define callees
         (filter (lambda (symbol) (hash-has-key? definitions symbol))
                 (syntax-symbols definition)))
       (loop (append (rest todo) callees) (set-add seen function))])))

(define (reachable-top-level-values module)
  (define functions (defined-top-level-functions module))
  (define values (defined-top-level-values module))
  (define all-names
    (set-union (list->set (hash-keys functions))
               (list->set (hash-keys values))))
  (let loop ([todo '(infer-core)] [seen (set)])
    (cond
      [(null? todo)
       (set-intersect seen (list->set (hash-keys values)))]
      [(set-member? seen (first todo)) (loop (rest todo) seen)]
      [else
       (define name (first todo))
       (define definition
         (or (hash-ref functions name #f) (hash-ref values name #f)
             (error 'reachable-top-level-values
                    "reachable binding ~a has no definition" name)))
       (define references
         (filter (lambda (symbol) (set-member? all-names symbol))
                 (syntax-symbols definition)))
       (loop (append (rest todo) references) (set-add seen name))])))

(define (canonical-branch-id function pattern)
  (define digest
    (sha1 (open-input-string (format "~a|~s" function pattern))))
  (format "B.~a.~a" function (substring digest 0 10)))

(define (canonical-helper-id function)
  (define digest
    (sha1 (open-input-string (symbol->string function))))
  (format "H.~a.~a" function (substring digest 0 10)))

(define (canonical-decision-id function kind pattern ordinal)
  (define digest
    (sha1 (open-input-string
           (format "~a|~a|~s|~a" function kind pattern ordinal))))
  (format "D.~a.~a" function (substring digest 0 10)))

(define (canonical-value-helper-id name)
  (define digest (sha1 (open-input-string (symbol->string name))))
  (format "V.~a.~a" name (substring digest 0 10)))

(define (extract-infer-branches [path types-path])
  (define module (read-module-syntax path))
  (define source-text (file->string path))
  (define observations '())
  (for ([(function keyword) (in-hash dispatch-functions)])
    (define definition (find-function module function))
    (unless definition
      (error 'extract-infer-branches "missing function ~a" function))
    (define dispatch (find-dispatch definition keyword))
    (unless dispatch
      (error 'extract-infer-branches "missing ~a dispatch in ~a" keyword function))
    (define clauses
      (drop (syntax-list dispatch) (if (eq? keyword 'match) 2 1)))
    (for ([clause (in-list clauses)])
      (define clause-parts (syntax-list clause))
      (unless (and clause-parts (pair? clause-parts))
        (error 'extract-infer-branches "malformed branch in ~a" function))
      (set! observations
            (cons (branch-observation
                   function (syntax->datum (first clause-parts))
                   (syntax-line clause) (syntax-end-line clause source-text)
                   (syntax-source-digest clause source-text))
                  observations))))
  (for ([function (in-list entry-functions)])
    (define definition (find-function module function))
    (unless definition
      (error 'extract-infer-branches "missing function ~a" function))
    (set! observations
          (cons (branch-observation function 'entry
                                    (syntax-line definition)
                                    (syntax-end-line definition source-text)
                                    (syntax-source-digest definition source-text))
                observations)))
  (define registered
    (for/set ([observation (in-list observations)])
      (branch-observation-function observation)))
  (define reachable (reachable-infer-functions module))
  (unless (set=? registered reachable)
    (error 'extract-infer-branches
           "reachable infer call graph and registered handlers differ: reachable=~e registered=~e"
           (sort (set->list reachable) symbol<?)
           (sort (set->list registered) symbol<?)))
  (sort observations string<?
        #:key (lambda (item)
                (format "~a:~a:~s" (branch-observation-function item)
                        (~r (branch-observation-start-line item)
                            #:min-width 6 #:pad-string "0")
                        (branch-observation-pattern item)))))

(define (extract-infer-helpers [path types-path]
                               [branches (extract-infer-branches path)])
  (define module (read-module-syntax path))
  (define source-text (file->string path))
  (define definitions (defined-top-level-functions module))
  (define branch-functions
    (for/set ([branch (in-list branches)])
      (branch-observation-function branch)))
  (sort
   (for/list ([function (in-set (reachable-top-level-functions module))]
              #:unless (set-member? branch-functions function))
     (define definition (hash-ref definitions function))
     (helper-observation function (syntax-line definition)
                         (syntax-end-line definition source-text)
                         (syntax-source-digest definition source-text)))
   symbol<? #:key helper-observation-function))

(define (extract-infer-decisions [path types-path])
  (define module (read-module-syntax path))
  (define source-text (file->string path))
  (define found '())
  (define ordinals (make-hash))
  (define (record! function kind pattern stx)
    (define ordinal-key (list function kind pattern))
    (define ordinal (add1 (hash-ref ordinals ordinal-key 0)))
    (hash-set! ordinals ordinal-key ordinal)
    (set! found
          (cons (decision-observation
                 function kind pattern ordinal (syntax-line stx)
                 (syntax-end-line stx source-text)
                 (syntax-source-digest stx source-text))
                found)))
  (define (walk function node)
    (when (syntax? node)
      (define parts (syntax-list node))
      (when parts
        (define head (and (pair? parts) (syntax-e (first parts))))
        (case head
          [(cond)
           (for ([clause (in-list (rest parts))])
             (define clause-parts (syntax-list clause))
             (when (and clause-parts (pair? clause-parts))
               (record! function 'cond (syntax->datum (first clause-parts))
                        clause)))]
          [(match match* case)
           (for ([clause (in-list (drop parts 2))])
             (define clause-parts (syntax-list clause))
             (when (and clause-parts (pair? clause-parts))
               (record! function head (syntax->datum (first clause-parts))
                        clause)))]
          [(if)
           (when (= (length parts) 4)
             (define condition (syntax->datum (second parts)))
             (record! function 'if `(,condition then) (third parts))
             (record! function 'if `(,condition else) (fourth parts)))]
          [else (void)])
        (for ([part (in-list parts)]) (walk function part)))))
  (for ([function (in-list entry-functions)])
    (walk function (find-function module function)))
  (sort found string<?
        #:key (lambda (item)
                (format "~a:~a:~a:~s"
                        (decision-observation-function item)
                        (~r (decision-observation-start-line item)
                            #:min-width 6 #:pad-string "0")
                        (decision-observation-kind item)
                        (decision-observation-pattern item)))))

(define (extract-infer-value-helpers [path types-path])
  (define module (read-module-syntax path))
  (define source-text (file->string path))
  (define values (defined-top-level-values module))
  (sort
   (for/list ([name (in-set (reachable-top-level-values module))])
     (define definition (hash-ref values name))
     (value-helper-observation
      name (syntax-line definition) (syntax-end-line definition source-text)
      (syntax-source-digest definition source-text)))
   symbol<? #:key value-helper-observation-name))

(define (load-infer-branches [path infer-branches-path])
  (match (call-with-input-file path read)
    [`(smusni-infer-core-branches 1 ,raw-entries ...)
     (for/list ([raw (in-list raw-entries)]
                #:when (and (pair? raw) (eq? (first raw) 'branch)))
       (match raw
         [`(branch (id ,(? string? id)) (function ,(? symbol? function))
                   (pattern ,pattern) (source-lines ,(? exact-positive-integer? start)
                                                   ,(? exact-positive-integer? end))
                   (source-sha1 ,(? string? source-sha1))
                   (class ,(? symbol? class)) (reason ,(? string? reason)))
          (unless (member class branch-classes)
            (error 'load-infer-branches "unknown branch class ~e" class))
          (unless (sentence? reason)
            (error 'load-infer-branches "branch ~a needs one-sentence reason" id))
          (branch-entry id function pattern start end source-sha1 class reason)]
         [_ (error 'load-infer-branches "invalid branch entry: ~e" raw)]))]
    [_ (error 'load-infer-branches "unsupported infer-core branch inventory")]))

(define (load-infer-helpers [path infer-branches-path])
  (match (call-with-input-file path read)
    [`(smusni-infer-core-branches 1 ,raw-entries ...)
     (for/list ([raw (in-list raw-entries)]
                #:when (and (pair? raw) (eq? (first raw) 'helper)))
       (match raw
         [`(helper (id ,(? string? id)) (function ,(? symbol? function))
                   (source-lines ,(? exact-positive-integer? start)
                                 ,(? exact-positive-integer? end))
                   (source-sha1 ,(? string? source-sha1))
                   (class ,(? symbol? class)) (reason ,(? string? reason)))
          (unless (member class branch-classes)
            (error 'load-infer-helpers "unknown helper class ~e" class))
          (unless (sentence? reason)
            (error 'load-infer-helpers "helper ~a needs one-sentence reason" id))
          (helper-entry id function start end source-sha1 class reason)]
         [_ (error 'load-infer-helpers "invalid helper entry: ~e" raw)]))]
    [_ (error 'load-infer-helpers "unsupported infer-core helper inventory")]))

(define (load-infer-decisions [path infer-branches-path])
  (match (call-with-input-file path read)
    [`(smusni-infer-core-branches 1 ,raw-entries ...)
     (for/list ([raw (in-list raw-entries)]
                #:when (and (pair? raw) (eq? (first raw) 'decision)))
       (match raw
         [`(decision (id ,(? string? id)) (function ,(? symbol? function))
                    (kind ,(? symbol? kind)) (pattern ,pattern)
                    (ordinal ,(? exact-positive-integer? ordinal))
                    (source-lines ,(? exact-positive-integer? start)
                                  ,(? exact-positive-integer? end))
                    (source-sha1 ,(? string? source-sha1))
                    (class ,(? symbol? class)) (reason ,(? string? reason)))
          (unless (member class branch-classes)
            (error 'load-infer-decisions "unknown decision class ~e" class))
          (unless (sentence? reason)
            (error 'load-infer-decisions "decision ~a needs one-sentence reason"
                   id))
          (decision-entry id function kind pattern ordinal start end source-sha1
                          class reason)]
         [_ (error 'load-infer-decisions "invalid decision entry: ~e" raw)]))]
    [_ (error 'load-infer-decisions "unsupported infer decision inventory")]))

(define (load-infer-value-helpers [path infer-branches-path])
  (match (call-with-input-file path read)
    [`(smusni-infer-core-branches 1 ,raw-entries ...)
     (for/list ([raw (in-list raw-entries)]
                #:when (and (pair? raw) (eq? (first raw) 'value-helper)))
       (match raw
         [`(value-helper (id ,(? string? id)) (name ,(? symbol? name))
                        (source-lines ,(? exact-positive-integer? start)
                                      ,(? exact-positive-integer? end))
                        (source-sha1 ,(? string? source-sha1))
                        (class ,(? symbol? class)) (reason ,(? string? reason)))
          (unless (member class branch-classes)
            (error 'load-infer-value-helpers "unknown value class ~e" class))
          (unless (sentence? reason)
            (error 'load-infer-value-helpers
                   "value helper ~a needs one-sentence reason" id))
          (value-helper-entry id name start end source-sha1 class reason)]
         [_ (error 'load-infer-value-helpers "invalid value helper: ~e" raw)]))]
    [_ (error 'load-infer-value-helpers "unsupported value helper inventory")]))

(define (refresh-infer-branch-metadata! [path infer-branches-path])
  (define raw (call-with-input-file path read))
  (define observed
    (for/hash ([item (in-list (extract-infer-branches))])
      (values (cons (branch-observation-function item)
                    (branch-observation-pattern item))
              item)))
  (define helper-observed
    (for/hash ([item (in-list (extract-infer-helpers))])
      (values (helper-observation-function item) item)))
  (define decision-observed
    (for/hash ([item (in-list (extract-infer-decisions))])
      (values (list (decision-observation-function item)
                    (decision-observation-kind item)
                    (decision-observation-pattern item)
                    (decision-observation-ordinal item))
              item)))
  (define value-observed
    (for/hash ([item (in-list (extract-infer-value-helpers))])
      (values (value-helper-observation-name item) item)))
  (match-define `(smusni-infer-core-branches 1 ,raw-entries ...) raw)
  (define recorded-branch-keys
    (for/set ([entry (in-list raw-entries)]
              #:when (and (pair? entry) (eq? (first entry) 'branch)))
      (match entry
        [`(branch (id ,_) (function ,function) (pattern ,pattern) . ,_)
         (cons function pattern)])))
  (define recorded-helper-names
    (for/set ([entry (in-list raw-entries)]
              #:when (and (pair? entry) (eq? (first entry) 'helper)))
      (match entry
        [`(helper (id ,_) (function ,function) . ,_) function])))
  (define recorded-decision-keys
    (for/set ([entry (in-list raw-entries)]
              #:when (and (pair? entry) (eq? (first entry) 'decision)))
      (match entry
        [`(decision (id ,_) (function ,function) (kind ,kind)
                    (pattern ,pattern) (ordinal ,ordinal) . ,_)
         (list function kind pattern ordinal)])))
  (define recorded-value-names
    (for/set ([entry (in-list raw-entries)]
              #:when (and (pair? entry) (eq? (first entry) 'value-helper)))
      (match entry
        [`(value-helper (id ,_) (name ,name) . ,_) name])))
  (unless (and (set=? recorded-branch-keys (list->set (hash-keys observed)))
               (set=? recorded-helper-names
                      (list->set (hash-keys helper-observed)))
               (set=? recorded-decision-keys
                      (list->set (hash-keys decision-observed)))
               (set=? recorded-value-names
                      (list->set (hash-keys value-observed))))
    (error 'refresh-infer-branch-metadata!
           "branch/helper denominator changed; classify new or removed handlers before refreshing metadata"))
  (define refreshed
    (for/list ([entry (in-list raw-entries)])
      (match entry
        [`(branch (id ,id) (function ,function) (pattern ,pattern)
                  (source-lines ,_ ,_) (source-sha1 ,_)
                  (class ,class) (reason ,reason))
         (define live (hash-ref observed (cons function pattern)))
         `(branch (id ,id) (function ,function) (pattern ,pattern)
                  (source-lines ,(branch-observation-start-line live)
                                ,(branch-observation-end-line live))
                  (source-sha1 ,(branch-observation-source-sha1 live))
                  (class ,class) (reason ,reason))]
        [`(helper (id ,id) (function ,function)
                  (source-lines ,_ ,_) (source-sha1 ,_)
                  (class ,class) (reason ,reason))
         (define live (hash-ref helper-observed function))
         `(helper (id ,id) (function ,function)
                  (source-lines ,(helper-observation-start-line live)
                                ,(helper-observation-end-line live))
                  (source-sha1 ,(helper-observation-source-sha1 live))
                  (class ,class) (reason ,reason))]
        [`(decision (id ,id) (function ,function) (kind ,kind)
                    (pattern ,pattern) (ordinal ,ordinal)
                    (source-lines ,_ ,_) (source-sha1 ,_)
                    (class ,class) (reason ,reason))
         (define key (list function kind pattern ordinal))
         (define live (hash-ref decision-observed key))
         `(decision (id ,id) (function ,function) (kind ,kind)
                    (pattern ,pattern) (ordinal ,ordinal)
                    (source-lines ,(decision-observation-start-line live)
                                  ,(decision-observation-end-line live))
                    (source-sha1 ,(decision-observation-source-sha1 live))
                    (class ,class) (reason ,reason))]
        [`(value-helper (id ,id) (name ,name)
                       (source-lines ,_ ,_) (source-sha1 ,_)
                       (class ,class) (reason ,reason))
         (define live (hash-ref value-observed name))
         `(value-helper (id ,id) (name ,name)
                        (source-lines ,(value-helper-observation-start-line live)
                                      ,(value-helper-observation-end-line live))
                        (source-sha1 ,(value-helper-observation-source-sha1 live))
                        (class ,class) (reason ,reason))]
        [`(branch (id ,id) (function ,function) (pattern ,pattern)
                  (source-lines ,_ ,_) (class ,class) (reason ,reason))
         (define live (hash-ref observed (cons function pattern)))
         `(branch (id ,id) (function ,function) (pattern ,pattern)
                  (source-lines ,(branch-observation-start-line live)
                                ,(branch-observation-end-line live))
                  (source-sha1 ,(branch-observation-source-sha1 live))
                  (class ,class) (reason ,reason))]
        [_ (error 'refresh-infer-branch-metadata!
                  "invalid branch entry: ~e" entry)])))
  (call-with-output-file path
    (lambda (out)
      (pretty-write `(smusni-infer-core-branches 1 ,@refreshed) out))
    #:exists 'truncate/replace)
  refreshed)

(define (branch-key item)
  (cons (if (branch-entry? item) (branch-entry-function item)
            (branch-observation-function item))
        (if (branch-entry? item) (branch-entry-pattern item)
            (branch-observation-pattern item))))

(define (infer-branch-findings [observed (extract-infer-branches)]
                               [entries (load-infer-branches)]
                               [helper-observed (extract-infer-helpers)]
                               [helper-entries (load-infer-helpers)]
                               [decision-observed (extract-infer-decisions)]
                               [decision-entries (load-infer-decisions)]
                               [value-observed (extract-infer-value-helpers)]
                               [value-entries (load-infer-value-helpers)])
  (define findings '())
  (define (note! format-string . arguments)
    (set! findings (cons (apply format format-string arguments) findings)))
  (define observed-by-key
    (for/hash ([item (in-list observed)]) (values (branch-key item) item)))
  (define entries-by-key (make-hash))
  (define ids (mutable-set))
  (for ([entry (in-list entries)])
    (when (set-member? ids (branch-entry-id entry))
      (note! "duplicate infer-core branch id ~a" (branch-entry-id entry)))
    (set-add! ids (branch-entry-id entry))
    (define expected-id
      (canonical-branch-id (branch-entry-function entry)
                           (branch-entry-pattern entry)))
    (unless (string=? (branch-entry-id entry) expected-id)
      (note! "infer-core branch id ~a is not its canonical stable id ~a"
             (branch-entry-id entry) expected-id))
    (when (hash-has-key? entries-by-key (branch-key entry))
      (note! "duplicate infer-core branch key ~e" (branch-key entry)))
    (hash-set! entries-by-key (branch-key entry) entry))
  (for ([(key observation) (in-hash observed-by-key)])
    (define entry (hash-ref entries-by-key key #f))
    (cond
      [(not entry)
       (note! "unclassified infer-core branch ~a ~s at ~a-~a"
              (branch-observation-function observation)
              (branch-observation-pattern observation)
              (branch-observation-start-line observation)
              (branch-observation-end-line observation))]
      [(not (and (= (branch-entry-start-line entry)
                    (branch-observation-start-line observation))
                 (= (branch-entry-end-line entry)
                    (branch-observation-end-line observation))))
       (note! "infer-core branch ~a source range is stale: ledger ~a-~a, live ~a-~a"
              (branch-entry-id entry)
              (branch-entry-start-line entry) (branch-entry-end-line entry)
              (branch-observation-start-line observation)
              (branch-observation-end-line observation))]
      [(not (string=? (branch-entry-source-sha1 entry)
                      (branch-observation-source-sha1 observation)))
       (note! "infer-core branch ~a source digest is stale"
              (branch-entry-id entry))]))
  (for ([(key entry) (in-hash entries-by-key)])
    (unless (hash-has-key? observed-by-key key)
      (note! "infer-core branch entry ~a is stale" (branch-entry-id entry))))
  (define helper-observed-by-name
    (for/hash ([item (in-list helper-observed)])
      (values (helper-observation-function item) item)))
  (define helper-entries-by-name (make-hash))
  (for ([entry (in-list helper-entries)])
    (when (hash-has-key? helper-entries-by-name (helper-entry-function entry))
      (note! "duplicate reachable helper ~a" (helper-entry-function entry)))
    (hash-set! helper-entries-by-name (helper-entry-function entry) entry)
    (define expected-id (canonical-helper-id (helper-entry-function entry)))
    (unless (string=? (helper-entry-id entry) expected-id)
      (note! "reachable helper id ~a is not its canonical stable id ~a"
             (helper-entry-id entry) expected-id)))
  (for ([(function observation) (in-hash helper-observed-by-name)])
    (define entry (hash-ref helper-entries-by-name function #f))
    (cond
      [(not entry)
       (note! "unclassified reachable helper ~a at ~a-~a"
              function (helper-observation-start-line observation)
              (helper-observation-end-line observation))]
      [(not (and (= (helper-entry-start-line entry)
                    (helper-observation-start-line observation))
                 (= (helper-entry-end-line entry)
                    (helper-observation-end-line observation))))
       (note! "reachable helper ~a source range is stale" function)]
      [(not (string=? (helper-entry-source-sha1 entry)
                      (helper-observation-source-sha1 observation)))
       (note! "reachable helper ~a source digest is stale" function)]))
  (for ([(function entry) (in-hash helper-entries-by-name)])
    (unless (hash-has-key? helper-observed-by-name function)
      (note! "reachable helper entry ~a is stale" (helper-entry-id entry))))
  (define (decision-key item)
    (list (if (decision-entry? item) (decision-entry-function item)
              (decision-observation-function item))
          (if (decision-entry? item) (decision-entry-kind item)
              (decision-observation-kind item))
          (if (decision-entry? item) (decision-entry-pattern item)
              (decision-observation-pattern item))
          (if (decision-entry? item) (decision-entry-ordinal item)
              (decision-observation-ordinal item))))
  (define decision-observed-by-key
    (for/hash ([item (in-list decision-observed)])
      (values (decision-key item) item)))
  (define decision-entries-by-key (make-hash))
  (for ([entry (in-list decision-entries)])
    (define key (decision-key entry))
    (when (hash-has-key? decision-entries-by-key key)
      (note! "duplicate internal decision key ~e" key))
    (hash-set! decision-entries-by-key key entry)
    (define expected-id
      (canonical-decision-id (decision-entry-function entry)
                             (decision-entry-kind entry)
                             (decision-entry-pattern entry)
                             (decision-entry-ordinal entry)))
    (unless (string=? (decision-entry-id entry) expected-id)
      (note! "internal decision id ~a is not its canonical stable id ~a"
             (decision-entry-id entry) expected-id)))
  (for ([(key observation) (in-hash decision-observed-by-key)])
    (define entry (hash-ref decision-entries-by-key key #f))
    (cond
      [(not entry)
       (note! "unclassified internal decision ~e at ~a-~a"
              key (decision-observation-start-line observation)
              (decision-observation-end-line observation))]
      [(not (and (= (decision-entry-start-line entry)
                    (decision-observation-start-line observation))
                 (= (decision-entry-end-line entry)
                    (decision-observation-end-line observation))))
       (note! "internal decision ~a source range is stale"
              (decision-entry-id entry))]
      [(not (string=? (decision-entry-source-sha1 entry)
                      (decision-observation-source-sha1 observation)))
       (note! "internal decision ~a source digest is stale"
              (decision-entry-id entry))]))
  (for ([(key entry) (in-hash decision-entries-by-key)])
    (unless (hash-has-key? decision-observed-by-key key)
      (note! "internal decision entry ~a is stale" (decision-entry-id entry))))
  (define value-observed-by-name
    (for/hash ([item (in-list value-observed)])
      (values (value-helper-observation-name item) item)))
  (define value-entries-by-name (make-hash))
  (for ([entry (in-list value-entries)])
    (hash-set! value-entries-by-name (value-helper-entry-name entry) entry)
    (define expected-id (canonical-value-helper-id (value-helper-entry-name entry)))
    (unless (string=? (value-helper-entry-id entry) expected-id)
      (note! "value helper id ~a is not its canonical stable id ~a"
             (value-helper-entry-id entry) expected-id)))
  (for ([(name observation) (in-hash value-observed-by-name)])
    (define entry (hash-ref value-entries-by-name name #f))
    (cond
      [(not entry) (note! "unclassified reachable value helper ~a" name)]
      [(not (and (= (value-helper-entry-start-line entry)
                    (value-helper-observation-start-line observation))
                 (= (value-helper-entry-end-line entry)
                    (value-helper-observation-end-line observation))))
       (note! "value helper ~a source range is stale" name)]
      [(not (string=? (value-helper-entry-source-sha1 entry)
                      (value-helper-observation-source-sha1 observation)))
       (note! "value helper ~a source digest is stale" name)]))
  (for ([(name entry) (in-hash value-entries-by-name)])
    (unless (hash-has-key? value-observed-by-name name)
      (note! "reachable value helper entry ~a is stale"
             (value-helper-entry-id entry))))
  (reverse findings))

;; B1 target migration is a separate axis from the immutable Phase 0 source
;; classification. One source mechanism may map to several target rules, and
;; grouped legacy branches may be only partially consumed by this family.
(define b1-source-heads
  '(+ ¬ Among Presuppose Distrib CoveredBy Exactly AtLeast MoreThan AtMost
      FewerThan Some No Every SelectExactly SelectAtLeast SelectSome
      SelectAllBut ∀ ∃ →))

(define b1-helper-functions
  '(effectful-property? ensure-same-property-domain gq-result-effects
    literal-zero? merge-results property-domain pure-property-domain
    quantifier-domain-type? pure-typing?))

(define (pattern-mentions-b1-head? pattern)
  (define (symbols datum)
    (cond
      [(symbol? datum) (set datum)]
      [(list? datum)
       (for/fold ([found (set)]) ([item (in-list datum)])
         (set-union found (symbols item)))]
      [else (set)]))
  (not (set-empty?
        (set-intersect (symbols pattern) (list->set b1-source-heads)))))

(define (b1-migration-source-ids branches helpers decisions)
  (sort
   (append
    (for/list ([entry (in-list branches)]
               #:when
               (and (eq? (branch-entry-class entry) 'semantic-clause)
                    (or (member (branch-entry-function entry)
                                '(infer-logical infer-quantifier))
                        (and (member (branch-entry-function entry)
                                     '(infer-application infer-with-expected))
                             (pattern-mentions-b1-head?
                              (branch-entry-pattern entry))))))
      (branch-entry-id entry))
    (for/list ([entry (in-list helpers)]
               #:when
               (and (eq? (helper-entry-class entry) 'semantic-clause)
                    (member (helper-entry-function entry)
                            b1-helper-functions)))
      (helper-entry-id entry))
    (for/list ([entry (in-list decisions)]
               #:when
               (and (eq? (decision-entry-class entry) 'semantic-clause)
                    (eq? (decision-entry-function entry) 'infer-quantifier)))
      (decision-entry-id entry)))
   string<?))

(define (load-target-migrations [path target-migrations-path])
  (match (call-with-input-file path read)
    [`(smusni-target-migrations 1 ,raw ...)
     (for/list ([item (in-list raw)])
       (match item
         [`(migration (family ,(? symbol? family))
                      (source ,(? string? source))
                      (targets ,(? string? targets) ...)
                      (extent ,(? symbol? extent))
                      (reason ,(? string? reason)))
          (unless (member extent '(full partial))
            (error 'load-target-migrations "invalid extent in ~e" item))
          (unless (and (pair? targets)
                       (= (length targets)
                          (set-count (list->set targets))))
            (error 'load-target-migrations "invalid target set in ~e" item))
          (unless (sentence? reason)
            (error 'load-target-migrations "migration needs a sentence: ~e"
                   item))
          (target-migration family source targets extent reason)]
         [_ (error 'load-target-migrations "invalid migration: ~e" item)]))]
    [_ (error 'load-target-migrations "unsupported target migrations")]))

(define (target-migration-findings
         [migrations (load-target-migrations)]
         [branches (load-infer-branches)]
         [helpers (load-infer-helpers)]
         [decisions (load-infer-decisions)])
  (define findings '())
  (define (note! format-string . arguments)
    (set! findings (cons (apply format format-string arguments) findings)))
  (define b1 (filter (lambda (entry)
                       (eq? (target-migration-family entry) 'B1))
                     migrations))
  (define sources (map target-migration-source b1))
  (unless (= (length sources) (set-count (list->set sources)))
    (note! "B1 target migrations contain duplicate sources"))
  (define expected (b1-migration-source-ids branches helpers decisions))
  (define missing (set-subtract (list->set expected) (list->set sources)))
  (define extra (set-subtract (list->set sources) (list->set expected)))
  (unless (and (set-empty? missing) (set-empty? extra))
    (note! "B1 target migration sources differ: missing=~s extra=~s"
           (sort (set->list missing) string<?)
           (sort (set->list extra) string<?)))
  (define rules (list->set a0-required-rules))
  (for ([migration (in-list b1)])
    (for ([target (in-list (target-migration-targets migration))])
      (unless (set-member? rules target)
        (note! "B1 migration ~a names absent target rule ~a"
               (target-migration-source migration) target))))
  (reverse findings))

(struct diagnostic-taxonomy
  (typing-causes no-lowering-causes allowed-evidence forbidden-evidence)
  #:transparent)

(define (load-diagnostic-taxonomy [path diagnostics-path])
  (match (call-with-input-file path read)
    [`(smusni-diagnostic-taxonomy 1
       (typing-causes ,(? symbol? typing) ...)
       (no-lowering-causes ,(? symbol? lowering) ...)
       (allowed-evidence ,(? symbol? allowed) ...)
       (forbidden-evidence ,(? symbol? forbidden) ...))
     (diagnostic-taxonomy typing lowering allowed forbidden)]
    [_ (error 'load-diagnostic-taxonomy "unsupported diagnostic taxonomy")]))

(define (live-no-lowering-causes [path lower-path])
  (define text (file->string path))
  (match (regexp-match
          #px"(?s:[(]define no-lowering-causes[[:space:]]*'[(]([^)]*)[)])"
          text)
    [(list _ body)
     (map string->symbol (regexp-match* #px"[A-Za-z][A-Za-z0-9-]*" body))]
    [_ (error 'live-no-lowering-causes "cannot read lower.rkt cause list")]))

(define (diagnostic-taxonomy-findings
         [taxonomy (load-diagnostic-taxonomy)])
  (define findings '())
  (define live (live-no-lowering-causes))
  (unless (set=? (list->set live)
                 (list->set (diagnostic-taxonomy-no-lowering-causes taxonomy)))
    (set! findings
          (cons (format "diagnostic no-lowering causes differ: live ~e ledger ~e"
                        live (diagnostic-taxonomy-no-lowering-causes taxonomy))
                findings)))
  (unless (member 'no-derivation
                  (diagnostic-taxonomy-typing-causes taxonomy))
    (set! findings (cons "diagnostic taxonomy omits no-derivation" findings)))
  (unless (member 'semantic-fallback
                  (diagnostic-taxonomy-forbidden-evidence taxonomy))
    (set! findings
          (cons "diagnostic taxonomy does not forbid semantic-fallback"
                findings)))
  (reverse findings))

;; --------------------------------------------------------------------------
;; P0.3: frozen differential corpus and identity oracle

(struct port-case (id provenance term env inventory) #:transparent)
(struct port-record
  (status type effects obligations gaps failure-class source-rule message
          derivations)
  #:transparent)

(define (test-files)
  ;; The harness self-test reads this frozen corpus and is intentionally not a
  ;; semantic input to itself. Every pre-port checker test is traced.
  (sort
   (for/list ([path (in-directory tests-dir)]
              #:when (regexp-match? #px"-test[.]rkt$" (path->string path))
              #:unless (string=? (path->string (file-name-from-path path))
                                  "phase0-test.rkt"))
     path)
   path<?))

(define (source-digests paths)
  (for/list ([path (in-list paths)])
    (list (path->string (find-relative-path repo-root (simplify-path path)))
          (file-digest path))))

(define (live-fence-source-digests)
  (for/list ([item (in-list
                    (classify-fences (read-all-fences) (load-manifest)))])
    (list (fence-source item) (fence-ordinal item) (fence-digest item))))

(define (live-definition-source-digests)
  (define observations
    (for/hash ([item (in-list (extract-definition-observations))])
      (values (definition-key item) item)))
  (for/list ([entry (in-list (load-definition-ledger))])
    (define observation (hash-ref observations (definition-key entry)))
    (list (definition-entry-head entry)
          (definition-entry-section entry)
          (if (pair? (definition-entry-spec-source-ranges entry))
              (definition-ranges-source-digest
               (definition-entry-spec-source-ranges entry))
              (definition-observation-source-digest observation)))))

(define (plain->core value [source 'phase0])
  (cond
    [(list? value)
     (core-list (map (lambda (child) (plain->core child source)) value)
                source #f #f #f #f)]
    [else (core-atom value source #f #f #f #f)]))

(define (env->hash entries)
  (for/hash ([entry (in-list entries)])
    (values (car entry) (cdr entry))))

(define (canonical-provenance values)
  (sort (remove-duplicates values) string<? #:key (lambda (value) (format "~s" value))))

(define (case-key term env inventory-digests)
  (list term env inventory-digests))

(define (merge-raw-cases raw)
  (define merged (make-hash))
  (for ([item (in-list raw)])
    (match-define `(raw ,provenance ,term ,env ,inventory-digests) item)
    (define key (case-key term env inventory-digests))
    (hash-update! merged key (lambda (provenances) (cons provenance provenances)) '()))
  (for/list ([(key provenances) (in-hash merged)])
    (match-define (list term env inventory-digests) key)
    (port-case (datum-digest key) (canonical-provenance provenances)
               term env inventory-digests)))

(define (collect-fence-cases [inv (load-inventory)])
  (append-map
   (lambda (fence)
     (for/list ([form (in-list (read-core-forms
                                (fence-content fence)
                                (format "~a#~a" (fence-source fence)
                                        (fence-ordinal fence))))]
                [index (in-naturals 1)])
       `(raw (fence ,(fence-source fence) ,(fence-ordinal fence)
                    ,(fence-kind fence) ,index)
             ,(core->plain-datum form) ()
             (,(inventory-core-digest inv) ,(inventory-fixture-digest inv)))))
   (classify-fences (read-all-fences) (load-manifest))))

(define (read-trace path)
  (match (call-with-input-file path read)
    [`(smusni-port-trace 1 ,entries ...) entries]
    [_ (error 'read-trace "invalid trace file ~a" path)]))

(define (collect-test-cases)
  (define racket (or (find-executable-path "racket")
                     (error 'collect-test-cases "racket executable not found")))
  (append-map
   (lambda (test-path)
     (define trace-path (make-temporary-file "smusni-port-trace-~a.sexp"))
     (dynamic-wind
       void
       (lambda ()
         (unless (system* racket trace-runner-path test-path trace-path)
           (error 'collect-test-cases "test trace failed: ~a" test-path))
         (for/list ([entry (in-list (read-trace trace-path))])
           (match entry
             [`(trace (test ,test) (term ,term) (env ,env)
                      (inventory ,core-digest ,fixture-digest))
              `(raw (test ,test) ,term ,env (,core-digest ,fixture-digest))]
             [_ (error 'collect-test-cases "invalid trace entry: ~e" entry)])))
       (lambda () (when (file-exists? trace-path) (delete-file trace-path)))))
   (test-files)))

(define (collect-port-cases)
  (sort (merge-raw-cases (append (collect-fence-cases) (collect-test-cases)))
        string<? #:key port-case-id))

(define (port-case->datum item)
  `(case (id ,(port-case-id item))
         (provenance ,@(port-case-provenance item))
         (term ,(port-case-term item))
         (env ,(port-case-env item))
         (inventory ,@(port-case-inventory item))))

(define (corpus-cases-digest cases)
  (datum-digest (map port-case->datum cases)))

(define (refresh-port-corpus! [path port-corpus-path])
  (define cases (collect-port-cases))
  (define datum
    `(smusni-port-corpus 1
       (count ,(length cases))
       (cases-sha1 ,(corpus-cases-digest cases))
       (fence-sources ,@(live-fence-source-digests))
       (definition-sources ,@(live-definition-source-digests))
       (test-sources ,@(source-digests (test-files)))
       (cases ,@(map port-case->datum cases))))
  (call-with-output-file path
    (lambda (out) (pretty-write datum out))
    #:exists 'truncate/replace)
  cases)

(define (load-port-corpus [path port-corpus-path])
  (match (call-with-input-file path read)
    [`(smusni-port-corpus 1
       (count ,(? exact-nonnegative-integer? count))
       (cases-sha1 ,(? string? digest))
       (fence-sources ,fence-sources ...)
       (definition-sources ,definition-sources ...)
       (test-sources ,test-sources ...)
       (cases ,raw-cases ...))
     (define cases
       (for/list ([raw (in-list raw-cases)])
         (match raw
           [`(case (id ,(? string? id)) (provenance ,provenance ...)
                   (term ,term) (env ,env) (inventory ,inventory ...))
            (port-case id provenance term env inventory)]
           [_ (error 'load-port-corpus "invalid port case: ~e" raw)])))
     (unless (= count (length cases))
       (error 'load-port-corpus "recorded count ~a, actual ~a" count (length cases)))
     (unless (string=? digest (corpus-cases-digest cases))
       (error 'load-port-corpus "frozen case digest is stale"))
     (unless (equal? fence-sources (live-fence-source-digests))
       (error 'load-port-corpus
              "fence sources changed; refresh the frozen corpus deliberately"))
     (unless (equal? definition-sources (live-definition-source-digests))
       (error 'load-port-corpus
              "definition sources changed; refresh the frozen corpus deliberately"))
     (unless (equal? test-sources (source-digests (test-files)))
       (error 'load-port-corpus "test sources changed; refresh the frozen corpus deliberately"))
     (validate-port-case-inventories! cases)
     cases]
    [_ (error 'load-port-corpus "unsupported port corpus")]))

(define (validate-port-case-inventories! cases [inv (load-inventory)])
  (define expected
    (list (inventory-core-digest inv) (inventory-fixture-digest inv)))
  (for ([item (in-list cases)])
    (unless (equal? (port-case-inventory item) expected)
      (error 'load-port-corpus
             "case ~a inventory digest is stale; refresh deliberately: recorded ~e live ~e"
             (port-case-id item) (port-case-inventory item) expected)))
  (void))

(define (canonical-set values)
  (sort (remove-duplicates values) string<? #:key (lambda (value) (format "~s" value))))

(define (term-constructor term)
  (cond [(and (list? term) (pair? term)) (first term)]
        [(number? term) 'number]
        [(string? term) 'string]
        [(symbol? term) term]
        [else 'atom]))

(define (legacy-record item [inv (load-inventory)])
  (define term (port-case-term item))
  (define constructor (term-constructor term))
  (with-handlers
      ([exn:fail:smusni?
        (lambda (exception)
          (port-record 'rejection #f '() '() '() 'typing-failure constructor
                       (exn-message exception) 0))]
       [exn:fail?
        (lambda (exception)
          (port-record 'rejection #f '() '() '() 'checker-error constructor
                       (exn-message exception) 0))])
    (define result
      (infer-core (plain->core term (port-case-id item))
                  (env->hash (port-case-env item)) inv))
    (define gaps (canonical-set (typing-gaps result)))
    (port-record (if (null? gaps) 'success 'gap)
                 (typing-type result)
                 (canonical-set (set->list (typing-effects result)))
                 (canonical-set (typing-obligations result))
                 gaps #f #f #f 1)))

(define (port-record-key record)
  (list (port-record-status record) (port-record-type record)
        (port-record-effects record) (port-record-obligations record)
        (port-record-gaps record) (port-record-failure-class record)
        (port-record-source-rule record) (port-record-derivations record)))

(define port-record-field-accessors
  (list (cons 'status port-record-status)
        (cons 'type port-record-type)
        (cons 'effects port-record-effects)
        (cons 'obligations port-record-obligations)
        (cons 'gaps port-record-gaps)
        (cons 'failure-class port-record-failure-class)
        (cons 'source-rule port-record-source-rule)
        (cons 'derivations port-record-derivations)))

(define (port-record-difference-fields old new)
  (for/list ([entry (in-list port-record-field-accessors)]
             #:unless (equal? ((cdr entry) old) ((cdr entry) new)))
    (car entry)))

(define (load-port-waivers [path port-waivers-path])
  (match (call-with-input-file path read)
    [`(smusni-port-waivers 1 ,waivers ...)
     (for ([waiver (in-list waivers)])
       (match waiver
         [`(waiver (case ,(? string? _))
                   (fields ,(? symbol? fields) ...)
                   (finding ,(? string? finding))
                   (reason ,(? string? reason)))
          (unless (and (pair? fields)
                       (andmap (lambda (field)
                                 (member field
                                         (map car port-record-field-accessors)))
                               fields))
            (error 'load-port-waivers "waiver has invalid field scope: ~e" waiver))
          (unless (and (not (string=? finding "")) (sentence? reason))
            (error 'load-port-waivers "waiver needs finding and sentence: ~e"
                   waiver))]
         [_ (error 'load-port-waivers "invalid waiver: ~e" waiver)]))
     waivers]
    [_ (error 'load-port-waivers "unsupported port waiver file")]))

(define (waiver-for waivers case-id difference-fields)
  (findf (lambda (waiver)
           (match waiver
             [`(waiver (case ,id) (fields ,fields ...)
                       (finding ,(? string? _))
                       (reason ,(? string? _)))
              (and (string=? id case-id)
                   (subset? (list->set difference-fields)
                            (list->set fields)))]
             [_ (error 'waiver-for "invalid waiver: ~e" waiver)]))
         waivers))

(define (run-differential [cases (load-port-corpus)]
                          [waivers (load-port-waivers)]
                          #:old-engine [old-engine legacy-record]
                          #:new-engine [new-engine legacy-record]
                          #:print? [print? #t])
  (define differences '())
  (define used-waivers (mutable-set))
  (for ([item (in-list cases)])
    (define old (old-engine item))
    ;; Phase 0 intentionally routes the new side through the same engine. A0
    ;; replaces this one function at the bank boundary, leaving the oracle and
    ;; corpus unchanged.
    ;; Phase 0's identity engine is literally the same procedure. Reuse the
    ;; computed immutable record rather than doubling legacy inference work;
    ;; adversarial self-tests and A0 pass distinct procedures and therefore
    ;; exercise the comparison path independently.
    (define new (if (eq? old-engine new-engine) old (new-engine item)))
    (define difference-fields (port-record-difference-fields old new))
    (unless (null? difference-fields)
      (define waiver
        (waiver-for waivers (port-case-id item) difference-fields))
      (if waiver
          (set-add! used-waivers waiver)
          (set! differences
                (cons (list item difference-fields old new) differences)))))
  (define stale-waivers
    (for/list ([waiver (in-list waivers)]
               #:unless (set-member? used-waivers waiver))
      waiver))
  (when print?
    (printf "port differential: ~a cases; differences=~a waivers=~a stale-waivers=~a\n"
            (length cases) (length differences) (set-count used-waivers)
            (length stale-waivers)))
  (values (and (null? differences) (null? stale-waivers))
          (reverse differences) stale-waivers))

(define (legacy-binder-pairs binder)
  (define groups
    (if (and (pair? binder) (list? (first binder))) binder (list binder)))
  (append-map
   (lambda (group)
     (define separator (index-of group '::))
     (unless separator (error 'legacy-datum->a0 "malformed binder: ~e" group))
     (define variables (take group separator))
     (define type-items (drop group (add1 separator)))
     (define type (if (= (length type-items) 1) (first type-items) type-items))
     (for/list ([variable (in-list variables)]) (list variable type)))
   groups))

(define (legacy-close-label value)
  (and (symbol? value)
       (let ([text (symbol->string value)])
         (cond
           [(string=? text ":Eventuality") 'Eventuality]
           [(regexp-match? #rx"^:[1-9][0-9]*$" text)
            (string->number (substring text 1))]
           [else #f]))))

(define (legacy-close-arguments->fills arguments total inv)
  (let loop ([remaining arguments] [used (set)] [fills '()])
    (cond
      [(null? remaining) (reverse fills)]
      [else
       (define explicit-label (legacy-close-label (first remaining)))
       (cond
         [explicit-label
          (unless (pair? (rest remaining))
            (error 'legacy-datum->a0
                   "Close label ~e has no value" (first remaining)))
          (when (set-member? used explicit-label)
            (error 'legacy-datum->a0
                   "Close label ~e is filled twice" explicit-label))
          (when (and (exact-integer? explicit-label)
                     (> explicit-label total))
            (error 'legacy-datum->a0
                   "Close label ~e exceeds row arity ~e"
                   explicit-label total))
          (loop (cddr remaining)
                (set-add used explicit-label)
                (cons (list explicit-label
                            (legacy-datum->a0 (second remaining) inv))
                      fills))]
         [(and (symbol? (first remaining))
               (string-prefix? (symbol->string (first remaining)) ":"))
          (error 'legacy-datum->a0
                 "unsupported Close label ~e" (first remaining))]
         [else
          (define available
            (for/first ([label (in-range 1 (add1 total))]
                        #:unless (set-member? used label))
              label))
          (unless available
            (error 'legacy-datum->a0
                   "Close has more positional fills than row arity ~e" total))
          (loop (rest remaining)
                (set-add used available)
                (cons (list available
                            (legacy-datum->a0 (first remaining) inv))
                      fills))])])))

(define (legacy-row-application->a0 predicate arguments row inv)
  (define fills
    (legacy-close-arguments->fills arguments (row-decl-total row) inv))
  (define ordinary
    (for/list ([label (in-range 1 (add1 (row-decl-total row)))])
      (match (assoc label fills)
        [(list _ value) value]
        [_ #f])))
  (define event
    (match (assoc 'Eventuality fills)
      [(list _ value) value]
      [_ #f]))
  (and (andmap values ordinary)
       (case (row-decl-event-mode row)
         [(holding-state) (and (not event) `(,predicate ,@ordinary))]
         [(direct-event) (and event `(,predicate ,@ordinary ,event))]
         [else #f])))

(define (legacy-datum->a0 datum [inv (load-inventory)])
  (cond
    [(not (list? datum)) datum]
    [else
     (match datum
       [`(λ ,binder ,body)
        `(λ ,(legacy-binder-pairs binder) ,(legacy-datum->a0 body inv))]
       [`(Let ,binder ,value ,body)
        (define pairs (legacy-binder-pairs binder))
        (unless (= (length pairs) 1) (error 'legacy-datum->a0 "Let binder"))
        (match-define (list variable type) (first pairs))
        `(Let (,variable ,type)
           ,(legacy-datum->a0 value inv) ,(legacy-datum->a0 body inv))]
       [`(Bind . ,pieces)
        (define body (last pieces))
        (define alternating (drop-right pieces 1))
        (define bindings
          (for/list ([index (in-range 0 (length alternating) 2)])
            (define pairs (legacy-binder-pairs (list-ref alternating index)))
            (unless (= (length pairs) 1) (error 'legacy-datum->a0 "Bind binder"))
            (match-define (list variable type) (first pairs))
            (list variable type
                  (legacy-datum->a0 (list-ref alternating (add1 index)) inv))))
        `(Bind ,bindings ,(legacy-datum->a0 body inv))]
       [`(Close (,predicate ,arguments ...))
        #:when (and (symbol? predicate) (inventory-row inv predicate))
        (define row (inventory-row inv predicate))
       `(CloseWith
          (row ,predicate ,(row-decl-total row) ,(row-decl-event-mode row)
               ,(range 1 (add1 (row-decl-total row))))
          ,(legacy-close-arguments->fills
            arguments (row-decl-total row) inv))]
       [`(,predicate ,arguments ...)
        #:when (and (symbol? predicate) (inventory-row inv predicate))
        (or (legacy-row-application->a0
             predicate arguments (inventory-row inv predicate) inv)
            (map (lambda (child) (legacy-datum->a0 child inv)) datum))]
       [_ (map (lambda (child) (legacy-datum->a0 child inv)) datum)])]))

(define a0-mechanism-cases
  (list
   (port-case "a0-let" '((a0 Let))
              '(Let ($x :: Entity) $v $x) '(($v . Entity)) '(core fixture))
   (port-case "a0-bind" '((a0 Bind))
              '(Bind ($x :: Referents Entity) (Context) $x)
              '() '(core fixture))
   (port-case "a0-exactly-zero" '((a0 Exactly-zero))
              '(Exactly 0 $P $Q)
              '(($P Fn (Entity) Content)
                ($Q EFn ((Referents Entity)) Content)) '(core fixture))
   (port-case "a0-exactly" '((a0 Exactly))
              '(Exactly 3 $P $Q)
              '(($P Fn (Entity) Content)
                ($Q EFn ((Referents Entity)) Content)) '(core fixture))
   (port-case "a0-global" '((a0 GlobalExactly))
              '(GlobalExactly 3 $P $Q)
              '(($P Fn (Entity) Content) ($Q Fn (Entity) Content))
              '(core fixture))
   (port-case "a0-too-many-expanded" '((a0 TooMany))
              '(Bind ($purpose :: Referents Entity) (Context)
                     ($threshold :: Natural)
                     (Vague (AdmissibleThreshold TooManyK $P $purpose))
                 (MoreThan $threshold $P $Q))
              '(($P Fn (Entity) Content)
                ($Q EFn ((Referents Entity)) Content)) '(core fixture))
   (port-case "a0-massify" '((a0 Massify))
              '(Bind ($g :: Referents (Group Entity))
                     (Massify $basis $cover) $g)
              '(($basis DecompositionBasis (Group Entity) Entity)
                ($cover Referents Entity)) '(core fixture))
   (port-case "a0-zipwith" '((a0 ZipWith))
              '(ZipWith $f (List Speaker) (List Audience))
              '(($f Fn ((Referents Entity) (Referents Entity)) Content))
              '(core fixture))
   (port-case "a0-zipwith-empty-effectful" '((a0 ZipWith empty))
              '(ZipWith $f (List) (List))
              '(($f EFn ((Referents Entity) (Referents Entity)) Content))
              '(core fixture))
   (port-case "a0-close" '((a0 Close))
              '(Close (tavla Speaker Audience)) '() '(core fixture))
   (port-case "a0-close-explicit-event" '((a0 Close explicit-event))
              '(Close (bajra Speaker :Eventuality $event))
              '(($event Referents Eventuality)) '(core fixture))
   (port-case "b1-atleast-zero" '((b1 AtLeast zero))
              '(AtLeast 0 $P $Q)
              '(($P Fn (Entity) Content)
                ($Q EFn ((Referents Entity)) Content)) '(core fixture))
   (port-case "b1-atleast-positive" '((b1 AtLeast positive))
              '(AtLeast 2 $P $Q)
              '(($P Fn (Entity) Content)
                ($Q EFn ((Referents Entity)) Content)) '(core fixture))
   (port-case "b1-atleast-symbolic" '((b1 AtLeast symbolic))
              '(AtLeast $n $P $Q)
              '(($n . Natural) ($P Fn (Entity) Content)
                ($Q EFn ((Referents Entity)) Content)) '(core fixture))
   (port-case "b1-some" '((b1 Some))
              '(Some $P $Q)
              '(($P Fn (Entity) Content)
                ($Q EFn ((Referents Entity)) Content)) '(core fixture))
   (port-case "b1-every" '((b1 Every))
              '(Every $P $Q)
              '(($P Fn (Entity) Content) ($Q EFn (Entity) Content))
              '(core fixture))
   (port-case "b1-atmost" '((b1 AtMost))
              '(AtMost $n $P $Q)
              '(($n . Natural) ($P Fn (Entity) Content)
                ($Q EFn ((Referents Entity)) Content)) '(core fixture))
   (port-case "b1-fewer-zero" '((b1 FewerThan zero))
              '(FewerThan 0 $P $Q)
              '(($P Fn (Entity) Content)
                ($Q EFn ((Referents Entity)) Content)) '(core fixture))
   (port-case "b1-fewer-positive" '((b1 FewerThan positive))
              '(FewerThan 2 $P $Q)
              '(($P Fn (Entity) Content)
                ($Q EFn ((Referents Entity)) Content)) '(core fixture))
   (port-case "b1-fewer-symbolic" '((b1 FewerThan symbolic))
              '(FewerThan $n $P $Q)
              '(($n . Natural) ($P Fn (Entity) Content)
                ($Q EFn ((Referents Entity)) Content)) '(core fixture))
   (port-case "b1-distrib" '((b1 Distrib))
              '(Distrib $Q $r)
              '(($Q EFn (Entity) Content) ($r Referents Entity))
              '(core fixture))
   (port-case "b1-covered-by" '((b1 CoveredBy))
              '(CoveredBy $P $r)
              '(($P Fn (Entity) Content) ($r Referents Entity))
              '(core fixture))
   (port-case "b1-overlap" '((b1 Overlap))
              '(Overlap $left $right)
              '(($left Referents Entity) ($right Referents Entity))
              '(core fixture))
   (port-case "b1-max-refer" '((b1 MaxRefer))
              '(Bind ($r :: Referents Entity) (MaxRefer $P) $r)
              '(($P Fn (Entity) Content)) '(core fixture))
   (port-case "b1-select-atleast" '((b1 SelectAtLeast))
              '(Bind ($r :: Referents Entity) (SelectAtLeast 2 $P) $r)
              '(($P Fn (Entity) Content)) '(core fixture))
   (port-case "b1-select-all-but" '((b1 SelectAllBut))
              '(Bind ($r :: Referents Entity) (SelectAllBut 0 $P) $r)
              '(($P Fn (Entity) Content)) '(core fixture))
   (port-case "b1-presuppose" '((b1 Presuppose))
              '(Presuppose ⊤ ⊤) '() '(core fixture))
   (port-case "b1-negation" '((b1 negation))
              '(¬ (Some $P $Q))
              '(($P Fn (Entity) Content)
                ($Q EFn ((Referents Entity)) Content)) '(core fixture))
   (port-case "b1-addition" '((b1 addition))
              '(+ $n 1) '(($n . Natural)) '(core fixture))))

(define a0-typed-form-heads
  '(λ Let Bind Context Vague Refer
    SelectExactly SelectAtLeast SelectSome SelectAllBut
    Exactly AtLeast Some Every No AtMost GlobalExactly TooMany MoreThan
    FewerThan Distrib MaxRefer CoveredBy Overlap Massify Perform
    CanonicalAggregateAt AdmissibleThreshold SetOf Card = + ∧ → ¬ ∀ ∃ Among
    Presuppose List ZipWith
    CoRef CloseClause ActualClause DirectClause StateClause CloseWith))

(define (a0-environment-names environment)
  (for/set ([entry (in-list environment)]) (car entry)))

(define (a0-type-datum? datum)
  (redex-match? SmusniA0 τ datum))

;; This is a structural bank-membership classifier, separate from a0-type.
;; It must not define eligibility by whether the new engine happens to derive
;; a result: doing that would silently omit precisely the missing clauses the
;; differential is meant to expose.
(define (a0-bank-datum? datum bound environment inv)
  (cond
    [(exact-nonnegative-integer? datum) #t]
    [(symbol? datum)
     (or (member datum '(Speaker Audience TooManyK ⊤))
         (set-member? bound datum)
         (set-member? environment datum))]
    [(not (list? datum)) #f]
    [else
     (match datum
       [`(λ ,binders ,body)
        (and (list? binders)
             (for/and ([binder (in-list binders)])
               (match binder
                 [`(,(? symbol?) ,type) (a0-type-datum? type)]
                 [_ #f]))
             (a0-bank-datum?
              body
              (for/fold ([scope bound]) ([binder (in-list binders)])
                (set-add scope (first binder)))
              environment inv))]
       [`(Let (,(? symbol? variable) ,type) ,value ,body)
        (and (a0-type-datum? type)
             (a0-bank-datum? value bound environment inv)
             (a0-bank-datum? body (set-add bound variable)
                             environment inv))]
       [`(Bind ,bindings ,body)
        (and (list? bindings)
             (let loop ([remaining bindings] [scope bound])
               (cond
                 [(null? remaining)
                  (a0-bank-datum? body scope environment inv)]
                 [else
                  (match (first remaining)
                    [`(,(? symbol? variable) ,type ,computation)
                     (and (a0-type-datum? type)
                          (a0-bank-datum? computation scope environment inv)
                          (loop (rest remaining) (set-add scope variable)))]
                    [_ #f])])))]
       [`(CloseWith (row ,(? symbol?) ,(? exact-nonnegative-integer?)
                         ,(? symbol?) ,labels)
                    ,fills)
        (and (list? labels)
             (list? fills)
             (for/and ([fill (in-list fills)])
               (match fill
                 [`(,_ ,value)
                  (a0-bank-datum? value bound environment inv)]
                 [_ #f])))]
       [`(,(? symbol? head) ,arguments ...)
        (cond
          [(member head a0-typed-form-heads)
           (andmap (lambda (argument)
                     (a0-bank-datum? argument bound environment inv))
                   arguments)]
          [(or (set-member? bound head) (set-member? environment head))
           (andmap (lambda (argument)
                     (a0-bank-datum? argument bound environment inv))
                   arguments)]
          [else
           (define row (inventory-row inv head))
           (and row
                (= (length arguments)
                   (+ (row-decl-total row)
                      (if (eq? (row-decl-event-mode row) 'direct-event)
                          1 0)))
                (andmap (lambda (argument)
                          (a0-bank-datum? argument bound environment inv))
                        arguments))])]
       [`(,operator ,arguments ...)
        (and (a0-bank-datum? operator bound environment inv)
             (andmap (lambda (argument)
                       (a0-bank-datum? argument bound environment inv))
                     arguments))]
       [_ #f])]))

(define (a0-corpus-eligible? item [inv (load-inventory)])
  (with-handlers ([exn:fail? (lambda (_) #f)])
    (define converted (legacy-datum->a0 (port-case-term item) inv))
    (and (redex-match? SmusniA0 t converted)
         (a0-bank-datum? converted (set)
                         (a0-environment-names (port-case-env item)) inv))))

(define (a0-differential-cases)
  (define inv (load-inventory))
  (append
   (filter (lambda (item) (a0-corpus-eligible? item inv))
           (load-port-corpus))
   a0-mechanism-cases
   (b1-lowering-differential-cases)))

(define (load-a0-waivers)
  (load-port-waivers a0-waivers-path))

;; Every deterministic lowering output receives one B1 disposition. Selected
;; subterms are maximal with respect to the extended closed grammar and retain
;; the lexical binder environment needed to replay them independently.
(define b1-lowering-family-heads
  '(AtLeast Some Every No AtMost MoreThan FewerThan Distrib MaxRefer
    CoveredBy Overlap SelectAtLeast SelectSome SelectAllBut ∀ ∃ → ¬
    Presuppose +))

(define (b1-family-heads-in datum)
  (cond
    [(not (list? datum)) (set)]
    [(null? datum) (set)]
    [(and (symbol? (first datum))
          (member (first datum) '(Quote Syntax)))
     (set)]
    [else
     (for/fold ([heads
                 (if (and (symbol? (first datum))
                          (member (first datum) b1-lowering-family-heads))
                     (set (first datum)) (set))])
               ([child (in-list datum)])
       (set-union heads (b1-family-heads-in child)))]))

(define (binder-pair->port-environment pair)
  (match-define (list variable type) pair)
  (if (list? type) `(,variable ,@type) `(,variable . ,type)))

(define (extend-port-environment environment pairs)
  (append (map binder-pair->port-environment pairs) environment))

(define (b1-subterm-id source ordinal index path term environment)
  (substring
   (datum-digest (list source ordinal index path term environment)) 0 16))

(define (b1-selected-subterms source ordinal index rules datum)
  (define inv (load-inventory))
  (define inventory-digests
    (list (inventory-core-digest inv) (inventory-fixture-digest inv)))
  (define (eligible? term environment)
    (a0-corpus-eligible?
     (port-case "candidate" '() term environment inventory-digests) inv))
  (define (selected term environment path)
    `(subterm
      (id ,(b1-subterm-id source ordinal index path term environment))
      (path ,@path)
      (term ,term)
      (env ,environment)))
  (define (walk term environment path)
    (define family-heads (b1-family-heads-in term))
    (cond
      [(and (not (set-empty? family-heads)) (eligible? term environment))
       (list (selected term environment path))]
      [(not (list? term)) '()]
      [else
       (match term
         [`(λ ,binder ,body)
          (define pairs (legacy-binder-pairs binder))
          (walk body (extend-port-environment environment pairs)
                (append path '(2)))]
         [`(Let ,binder ,active ,body)
          (define pairs (legacy-binder-pairs binder))
          (append
           (walk active environment (append path '(2)))
           (walk body (extend-port-environment environment pairs)
                 (append path '(3))))]
         [`(Bind . ,pieces)
          (define body (last pieces))
          (define alternating (drop-right pieces 1))
          (define-values (found scope)
            (for/fold ([found '()] [scope environment])
                      ([position (in-range 0 (length alternating) 2)])
              (define pairs
                (legacy-binder-pairs (list-ref alternating position)))
              (values
               (append found
                       (walk (list-ref alternating (add1 position)) scope
                             (append path (list (+ position 2)))))
               (extend-port-environment scope pairs))))
          (append found
                  (walk body scope
                        (append path (list (add1 (length alternating))))))]
         [_
          (append-map
           (lambda (child position)
             (walk child environment (append path (list position))))
           term (range (length term)))])]))
  (walk datum '() '()))

(define (live-b1-lowering-outputs)
  (define-values (ok? reports _fences) (run-lowering-gate #:print? #f))
  (unless ok? (error 'live-b1-lowering-outputs "lowering gate is not green"))
  (for/list ([report (in-list reports)])
    (define source (case-report-source report))
    (define ordinal (case-report-ordinal report))
    (define index (case-report-index report))
    (define produced (case-report-produced report))
    (define heads (b1-family-heads-in produced))
    (define subterms
      (b1-selected-subterms source ordinal index
                            (case-report-rules report) produced))
    (define disposition
      (cond [(pair? subterms) 'selected]
            [(set-empty? heads) 'no-family-head]
            [else 'unrepresentable]))
    `(output
      (key ,(format "~a#~a.~a" source ordinal index))
      (source ,source ,ordinal ,index)
      (rules ,@(case-report-rules report))
      (disposition ,disposition)
      (offending ,@(if (eq? disposition 'unrepresentable)
                       (sort (set->list heads) symbol<?) '()))
      (subterms ,@subterms))))

(define (b1-lowering-manifest-datum)
  (define outputs (live-b1-lowering-outputs))
  `(smusni-b1-lowering-subterms 1
     (count ,(length outputs))
     (outputs-sha1 ,(datum-digest outputs))
     (outputs ,@outputs)))

(define (refresh-b1-lowering-manifest! [path b1-lowering-manifest-path])
  (define datum (b1-lowering-manifest-datum))
  (call-with-output-file path
    (lambda (out) (pretty-write datum out))
    #:exists 'truncate/replace)
  datum)

(define (load-b1-lowering-manifest [path b1-lowering-manifest-path])
  (define datum (call-with-input-file path read))
  (match datum
    [`(smusni-b1-lowering-subterms 1
       (count ,(? exact-nonnegative-integer? count))
       (outputs-sha1 ,(? string? digest))
       (outputs ,outputs ...))
     (unless (= count (length outputs))
       (error 'load-b1-lowering-manifest "output count is stale"))
     (unless (string=? digest (datum-digest outputs))
       (error 'load-b1-lowering-manifest "output digest is stale"))
     datum]
    [_ (error 'load-b1-lowering-manifest "unsupported B1 lowering manifest")]))

(define (b1-lowering-manifest-findings
         [recorded (load-b1-lowering-manifest)])
  (if (equal? recorded (b1-lowering-manifest-datum))
      '()
      '("B1 lowering subterm manifest is stale")))

(define (b1-lowering-differential-cases
         [manifest (load-b1-lowering-manifest)])
  (define inv (load-inventory))
  (define inventory-digests
    (list (inventory-core-digest inv) (inventory-fixture-digest inv)))
  (match manifest
    [`(smusni-b1-lowering-subterms 1 ,_ ... (outputs ,outputs ...))
     (append-map
      (lambda (output)
        (match output
          [`(output (key ,key) (source ,source ,ordinal ,index)
                    (rules ,rules ...) (disposition ,_)
                    (offending ,_ ...)
                    (subterms ,subterms ...))
           (for/list ([subterm (in-list subterms)])
             (match subterm
               [`(subterm (id ,id) (path ,path ...)
                          (term ,term) (env ,environment))
                (port-case
                 (format "b1-lowering-~a" id)
                 `((lowering ,source ,ordinal ,index
                             (rules ,@rules) (path ,@path) (output ,key)))
                 term environment inventory-digests)]))]))
      outputs)]))

(define (a0-row-environment datum inv)
  (cond
    [(not (list? datum)) '()]
    [else
     (match datum
       [`(CloseWith (row ,predicate ,arity ,event-mode ,_) ,fills)
        (define parameters
          (append (make-list arity '(Referents Entity))
                  (if (eq? event-mode 'direct-event)
                      '((Referents Eventuality)) '())))
        (cons (list predicate `(Fn ,parameters Content))
              (append-map (lambda (fill) (a0-row-environment fill inv))
                          fills))]
       [`(,(? symbol? predicate) ,arguments ...)
        (define row (inventory-row inv predicate))
        (append
             (if (and row
                      (= (length arguments)
                         (+ (row-decl-total row)
                            (if (eq? (row-decl-event-mode row) 'direct-event)
                                1 0))))
                 (list
                  (list predicate
                        `(Fn ,(append
                               (make-list (row-decl-total row)
                                          '(Referents Entity))
                               (if (eq? (row-decl-event-mode row) 'direct-event)
                                   '((Referents Eventuality)) '()))
                             Content)))
             '())
         (append-map (lambda (argument)
                       (a0-row-environment argument inv))
                     arguments))]
       [_ (append-map (lambda (child) (a0-row-environment child inv))
                      datum)])]))

(define (a0-case-input item)
  (define inv (load-inventory))
  (define term (legacy-datum->a0 (port-case-term item) inv))
  (define explicit-environment
    (for/list ([entry (in-list (port-case-env item))])
      (match entry [(cons variable type) (list variable type)])))
  (define environment
    (remove-duplicates
     (append explicit-environment (a0-row-environment term inv))))
  (values term environment))

(define (a0-case-derivations item)
  (define-values (term environment) (a0-case-input item))
  (build-derivations (a0-synth ,environment ,term R)))

(define (a0-port-record item)
  (with-handlers ([exn:fail?
                   (lambda (exception)
                     (port-record 'rejection #f '() '() '()
                                  'a0-error (term-constructor (port-case-term item))
                                  (exn-message exception) 0))])
    (define-values (term environment) (a0-case-input item))
    (define derivations
      (build-derivations (a0-synth ,environment ,term R)))
    (define results (judgment-holds (a0-synth ,environment ,term R) R))
    (cond
      [(and (= (length derivations) 1) (= (length results) 1))
       (match (first results)
          [`(typing ,type ,effects ,obligations)
           (port-record 'success type (canonical-set effects)
                        (canonical-set obligations) '() #f #f #f
                        (length derivations))])]
      [(pair? derivations)
       (port-record 'rejection #f '() '() '() 'multiple-derivations
                    (term-constructor (port-case-term item))
                    (format "A0 derivations: ~a" (length derivations))
                    (length derivations))]
      [else
       (port-record 'rejection #f '() '() '() 'no-derivation
                     (term-constructor (port-case-term item))
                     (format "A0 derivations: ~a" (length results))
                     0)])))

(define (run-a0-differential #:print? [print? #t])
  (define cases (a0-differential-cases))
  (define waivers (load-a0-waivers))
  (define-values (ok? differences stale)
    (run-differential cases waivers
                      #:old-engine legacy-record #:new-engine a0-port-record
                      #:print? #f))
  (when print?
    (define lowering-count (length (b1-lowering-differential-cases)))
    (printf "A0/B1 differential: cases=~a frozen=~a mechanism=~a lowering-subterms=~a differences=~a waivers=~a stale-waivers=~a\n"
            (length cases)
            (- (length cases) (length a0-mechanism-cases) lowering-count)
            (length a0-mechanism-cases)
            lowering-count
            (length differences) (- (length waivers) (length stale))
            (length stale)))
  (values ok? differences stale))

;; --------------------------------------------------------------------------
;; P0.4: in-process benchmark and recorded, report-only triggers

(struct benchmark-mode (name totals term-times peak-rss derivations hotspots)
  #:transparent)

(define (percentile values fraction)
  (define sorted (sort values <))
  (if (null? sorted) 0.0
      (list-ref sorted
                (min (sub1 (length sorted))
                     (inexact->exact
                      (floor (* fraction (sub1 (length sorted)))))))))

(define (median values) (percentile values 0.5))

(define (peak-rss-bytes)
  (with-handlers ([exn:fail? (lambda (_) (current-memory-use))])
    (define line
      (findf (lambda (candidate) (string-prefix? candidate "VmHWM:"))
             (file->lines "/proc/self/status")))
    (match (and line (regexp-match #px"VmHWM:[[:space:]]*([0-9]+)[[:space:]]+kB" line))
      [(list _ kilobytes) (* 1024 (string->number kilobytes))]
      [_ (current-memory-use)])))

(define (specimen-case? item)
  (for/or ([provenance (in-list (port-case-provenance item))])
    (match provenance [`(fence ,_ ,_ specimen ,_) #t] [_ #f])))

(define (specimen-benchmark-cases cases)
  (append-map
   (lambda (item)
     (for/list ([provenance (in-list (port-case-provenance item))]
                #:when (match provenance
                         [`(fence ,_ ,_ specimen ,_) #t]
                         [_ #f]))
       (struct-copy port-case item
                    [id (format "~a:~s" (port-case-id item) provenance)]
                    [provenance (list provenance)])))
   cases))

(define (a0-specimen-benchmark-cases cases)
  (filter a0-corpus-eligible? (specimen-benchmark-cases cases)))

(define (proof-rule-names derivation)
  (append (if (derivation-name derivation)
              (list (derivation-name derivation)) '())
          (append-map proof-rule-names (derivation-subs derivation))))

(define (a0-case-rule-names item)
  (remove-duplicates
   (append-map proof-rule-names (a0-case-derivations item))))

(define (run-benchmark-mode name cases repetitions)
  (define totals '())
  (define all-term-times '())
  (define derivations 0)
  (define new-case-times (make-hash))
  (define new-case-counts (make-hash))
  (define (run-once record?)
    (define started (current-inexact-monotonic-milliseconds))
    (define term-times '())
    (define run-derivations 0)
    (for ([item (in-list cases)])
      (define term-start (current-inexact-monotonic-milliseconds))
      (define new-elapsed #f)
      (define records
        (case name
          [(old-only) (list (legacy-record item))]
          [(new-only)
           (define new-start (current-inexact-monotonic-milliseconds))
           (define new (a0-port-record item))
           (set! new-elapsed
                 (- (current-inexact-monotonic-milliseconds) new-start))
           (list new)]
          [(side-by-side)
           (define old (legacy-record item))
           (define new-start (current-inexact-monotonic-milliseconds))
           (define new (a0-port-record item))
           (set! new-elapsed
                 (- (current-inexact-monotonic-milliseconds) new-start))
           (list old new)]
          [else (error 'run-benchmark-mode "unsupported mode: ~e" name)]))
      (for ([result (in-list records)])
        (set! run-derivations
              (+ run-derivations (port-record-derivations result))))
      (set! term-times
            (cons (- (current-inexact-monotonic-milliseconds) term-start)
                  term-times))
      (when (and record? new-elapsed)
        (hash-update! new-case-times (port-case-id item)
                      (lambda (total) (+ total new-elapsed)) 0.0)
        (hash-update! new-case-counts (port-case-id item) add1 0)))
    (when record?
      (set! totals (cons (- (current-inexact-monotonic-milliseconds) started)
                         totals))
      (set! all-term-times (append term-times all-term-times))
      (set! derivations (+ derivations run-derivations))))
  (run-once #f)
  (for ([_ (in-range repetitions)]) (run-once #t))
  (define measured-peak-rss (peak-rss-bytes))
  (define hotspot-totals (make-hash))
  (define hotspot-counts (make-hash))
  (when (member name '(new-only side-by-side))
    (for ([item (in-list cases)])
      (define elapsed (hash-ref new-case-times (port-case-id item) 0.0))
      (define count (hash-ref new-case-counts (port-case-id item) 0))
      (for ([rule (in-list (a0-case-rule-names item))])
        (hash-update! hotspot-totals rule
                      (lambda (total) (+ total elapsed)) 0.0)
        (hash-update! hotspot-counts rule
                      (lambda (hits) (+ hits count)) 0))))
  (define hotspots
    (take
     (sort
      (for/list ([(rule elapsed) (in-hash hotspot-totals)])
        (list rule elapsed (hash-ref hotspot-counts rule)))
      (lambda (left right)
        (or (> (second left) (second right))
            (and (= (second left) (second right))
                 (string<? (first left) (first right))))))
     (min 5 (hash-count hotspot-totals))))
  (benchmark-mode name (reverse totals) all-term-times measured-peak-rss
                  derivations hotspots))

(define (benchmark-mode->datum mode)
  `(benchmark-mode ,(benchmark-mode-name mode)
                   (totals ,@(benchmark-mode-totals mode))
                   (term-times ,@(benchmark-mode-term-times mode))
                   (peak-rss ,(benchmark-mode-peak-rss mode))
                   (derivations ,(benchmark-mode-derivations mode))
                   (hotspots ,@(benchmark-mode-hotspots mode))))

(define (datum->benchmark-mode datum)
  (match datum
    [`(benchmark-mode ,(? symbol? name)
                     (totals ,(? real? totals) ...)
                     (term-times ,(? real? term-times) ...)
                     (peak-rss ,(? exact-nonnegative-integer? peak-rss))
                     (derivations ,(? exact-nonnegative-integer? derivations))
                     (hotspots (,(? string? rule)
                                ,(? real? milliseconds)
                                ,(? exact-nonnegative-integer? hits)) ...))
     (benchmark-mode name totals term-times peak-rss derivations
                     (map list rule milliseconds hits))]
    [_ (error 'datum->benchmark-mode "invalid benchmark mode: ~e" datum)]))

(define (isolated-benchmark-mode name runs)
  (define racket (or (find-executable-path "racket")
                     (error 'isolated-benchmark-mode
                            "racket executable not found")))
  (define output (make-temporary-file "smusni-port-benchmark-~a.sexp"))
  (dynamic-wind
    void
    (lambda ()
      (unless (system* racket benchmark-worker-path
                       (symbol->string name) (number->string runs) output)
        (error 'isolated-benchmark-mode "benchmark worker failed for ~a" name))
      (datum->benchmark-mode (call-with-input-file output read)))
    (lambda () (when (file-exists? output) (delete-file output)))))

(define (run-benchmarks #:runs [runs 5] #:print? [print? #t])
  (define all-specimens (specimen-benchmark-cases (load-port-corpus)))
  (define cases (a0-specimen-benchmark-cases (load-port-corpus)))
  (define modes
    (for/list ([name '(old-only new-only side-by-side)])
      ;; Each mode receives a fresh process so VmHWM/peak RSS is comparable.
      ;; The worker loads and warms before starting its timed repetitions.
      (isolated-benchmark-mode name runs)))
  (when print?
    (printf "port benchmark denominator: a0-eligible-specimen-terms=~a all-specimen-terms=~a\n"
            (length cases) (length all-specimens))
    (for ([mode (in-list modes)])
      (printf "port benchmark ~a: terms=~a runs=~a median-total-ms=~a p95-term-ms=~a max-term-ms=~a peak-rss=~a derivations=~a\n"
              (benchmark-mode-name mode) (length cases) runs
              (~r (median (benchmark-mode-totals mode)) #:precision '(= 3))
              (~r (percentile (benchmark-mode-term-times mode) 0.95)
                  #:precision '(= 3))
              (~r (if (null? (benchmark-mode-term-times mode)) 0
                      (apply max (benchmark-mode-term-times mode)))
                  #:precision '(= 3))
              (benchmark-mode-peak-rss mode)
              (benchmark-mode-derivations mode)))
    (let ([new-mode
           (findf (lambda (mode) (eq? (benchmark-mode-name mode) 'new-only))
                  modes)])
      (printf "port benchmark A0 clause hotspots (inclusive attributed ms): ~s\n"
              (benchmark-mode-hotspots new-mode))))
  modes)

(define (git-head)
  (define out (open-output-string))
  (define ok?
    (parameterize ([current-output-port out] [current-error-port (open-output-nowhere)])
      (system* (or (find-executable-path "git") "git") "rev-parse" "HEAD")))
  (if ok? (string-trim (get-output-string out)) "unknown"))

(define (mode->baseline-datum mode)
  `(mode ,(benchmark-mode-name mode)
         (median-total-ms ,(median (benchmark-mode-totals mode)))
         (p95-term-ms ,(percentile (benchmark-mode-term-times mode) 0.95))
         (max-term-ms ,(if (null? (benchmark-mode-term-times mode)) 0
                           (apply max (benchmark-mode-term-times mode))))
         (peak-rss-bytes ,(benchmark-mode-peak-rss mode))))

(define (refresh-port-baseline! [path port-baseline-path]
                                #:full-gate-ms [full-gate-ms 37000.0])
  (define cases (a0-specimen-benchmark-cases (load-port-corpus)))
  (define modes (run-benchmarks #:print? #t))
  (define datum
    `(smusni-port-baseline 1
       (head ,(git-head))
       (corpus-sha1 ,(corpus-cases-digest (load-port-corpus)))
       (terms ,(length cases))
       (runs 5)
       (full-gate-ms ,full-gate-ms)
       (triggers (new-factor 5.0) (new-wall-ms 2000.0)
                 (term-max-ms 250.0) (term-p95-ms 500.0)
                 (rss-factor 2.0) (side-factor 3.0)
                 (full-gate-factor 1.5) (size-growth-factor 4.0))
       (modes ,@(map mode->baseline-datum modes))))
  (call-with-output-file path
    (lambda (out) (pretty-write datum out))
    #:exists 'truncate/replace)
  datum)

(define (load-port-baseline [path port-baseline-path])
  (define datum (call-with-input-file path read))
  (match datum
    [`(smusni-port-baseline 1 (head ,(? string? _))
       (corpus-sha1 ,(? string? corpus-digest))
       (terms ,(? exact-nonnegative-integer? _)) (runs 5)
       (full-gate-ms ,(? real? _)) (triggers ,_ ...) (modes ,_ ...))
     (unless (string=? corpus-digest
                       (corpus-cases-digest (load-port-corpus)))
       (error 'load-port-baseline "baseline corpus digest is stale"))
     datum]
    [_ (error 'load-port-baseline "unsupported port baseline")]))

(define (load-b1-growth-profile [path b1-growth-profile-path])
  (define datum (call-with-input-file path read))
  (match datum
    [`(smusni-b1-growth-profile 1
       (base-head ,(? string? _))
       (depths ,(? exact-positive-integer? depths) ...)
       (before-ms ,(? positive? before) ...)
       (after-local-ms ,(? positive? after) ...)
       (before-ratios ,(? positive? before-ratios) ...)
       (after-local-ratios ,(? positive? after-ratios) ...)
       (attribution ,_ ...)
       (mitigation ,(? string? mitigation))
       (conclusion ,(? string? conclusion)))
     (unless (and (equal? depths '(16 32 64))
                  (= (length before) 3) (= (length after) 3)
                  (= (length before-ratios) 2)
                  (= (length after-ratios) 2)
                  (< (last after) (last before))
                  (sentence? mitigation) (sentence? conclusion))
       (error 'load-b1-growth-profile "invalid B1 growth profile"))
     datum]
    [_ (error 'load-b1-growth-profile "unsupported B1 growth profile")]))

(define (b1-growth-profile-findings)
  (with-handlers ([exn:fail? (lambda (exception)
                               (list (exn-message exception)))])
    (load-b1-growth-profile)
    '()))

(define (print-baseline-trigger-report baseline current-modes)
  (match-define
    `(smusni-port-baseline 1 (head ,head) (corpus-sha1 ,_)
       (terms ,terms) (runs 5) (full-gate-ms ,full-gate-ms)
       (triggers (new-factor ,new-factor) (new-wall-ms ,new-wall-ms)
                 (term-max-ms ,term-max-ms) (term-p95-ms ,term-p95-ms)
                 (rss-factor ,rss-factor) (side-factor ,side-factor)
                 (full-gate-factor ,full-gate-factor)
                 (size-growth-factor ,size-growth-factor))
       (modes ,baseline-modes ...))
    baseline)
  (define (current name)
    (findf (lambda (mode) (eq? (benchmark-mode-name mode) name)) current-modes))
  (define old (current 'old-only))
  (define new (current 'new-only))
  (define side (current 'side-by-side))
  (define old-median (median (benchmark-mode-totals old)))
  (define new-median (median (benchmark-mode-totals new)))
  (define side-median (median (benchmark-mode-totals side)))
  (define current-terms
    (quotient (length (benchmark-mode-term-times new)) 5))
  (define growth
    (run-a0-size-growth #:factor size-growth-factor #:print? #f))
  (define reports
    (list
     (list 'new-factor (> new-median (* new-factor old-median))
           new-median (* new-factor old-median))
     (list 'new-wall (> new-median new-wall-ms) new-median new-wall-ms)
     (list 'term-max (> (apply max (benchmark-mode-term-times new)) term-max-ms)
           (apply max (benchmark-mode-term-times new)) term-max-ms)
     (list 'term-p95 (> (percentile (benchmark-mode-term-times new) 0.95)
                           term-p95-ms)
           (percentile (benchmark-mode-term-times new) 0.95) term-p95-ms)
     (let ([rss-limit (* rss-factor (benchmark-mode-peak-rss old))])
       (list 'rss (> (benchmark-mode-peak-rss new) rss-limit)
             (benchmark-mode-peak-rss new) rss-limit))
     (list 'side-factor (> side-median (* side-factor old-median))
           side-median (* side-factor old-median))))
  (printf "port triggers (report-only until B): baseline-head=~a baseline-terms=~a a0-eligible-terms=~a full-gate-ms=~a full-gate-limit-ms=~a size-growth-limit=~ax\n"
          head terms current-terms full-gate-ms (* full-gate-ms full-gate-factor)
          size-growth-factor)
  (for ([report (in-list reports)])
    (match-define (list name triggered? actual limit) report)
    (printf "  ~a: ~a actual=~a limit=~a\n"
            name (if triggered? "TRIGGER" "ok") actual limit))
  (displayln "  full-gate: external measurement required; use --report-full-gate-ms")
  (printf "  size-growth: ~a depths=~s milliseconds=~s ratios=~s limit=~ax\n"
          (if (a0-size-growth-triggered? growth) "TRIGGER" "ok")
          (a0-size-growth-depths growth)
          (map (lambda (value) (~r value #:precision '(= 3)))
               (a0-size-growth-milliseconds growth))
          (map (lambda (value) (~r value #:precision '(= 3)))
               (a0-size-growth-ratios growth))
          size-growth-factor)
  (match (load-b1-growth-profile)
    [`(smusni-b1-growth-profile 1 ,_ (depths ,depths ...)
       (before-ms ,before ...) (after-local-ms ,after ...)
       (before-ratios ,before-ratios ...)
       (after-local-ratios ,after-ratios ...) ,_ ...)
     (printf "  B1 opener profile: depths=~s before-ms=~s after-local-ms=~s before-ratios=~s after-local-ratios=~s depth64-improvement=~a%\n"
             depths before after before-ratios after-ratios
             (~r (* 100.0 (- 1 (/ (last after) (last before))))
                 #:precision '(= 1)))]))

(define (report-full-gate-trigger observed-ms
                                  [baseline (load-port-baseline)])
  (match baseline
    [`(smusni-port-baseline 1 ,_ ...
       (full-gate-ms ,baseline-ms)
       (triggers ,trigger-items ...)
       ,_ ...)
     (define factor
       (second (findf (lambda (item) (eq? (first item) 'full-gate-factor))
                      trigger-items)))
     (define limit (* baseline-ms factor))
     (printf "port full-gate trigger (report-only until B): ~a actual=~a limit=~a baseline=~a factor=~a\n"
             (if (> observed-ms limit) "TRIGGER" "ok")
             observed-ms limit baseline-ms factor)
     (> observed-ms limit)]
    [_ (error 'report-full-gate-trigger "invalid baseline")]))

;; --------------------------------------------------------------------------
;; Combined gate and CLI

(define (print-classification-summary definitions branches taxonomy)
  (for ([status (in-list definition-statuses)])
    (define selected
      (filter (lambda (entry) (eq? (definition-entry-status entry) status))
              definitions))
    (printf "definition ledger ~a: ~a\n" status (length selected))
    (when (not (eq? status 'executable))
      (for ([entry (in-list selected)])
        (printf "  ~a (~a~a): ~a\n" (definition-entry-id entry)
                (definition-entry-head entry)
                (if (definition-entry-issue entry)
                    (format ", ~a" (definition-entry-issue entry)) "")
                (definition-entry-reason entry)))))
  (printf "definition equation ranges: reviewed=~a unranged=~a\n"
          (count (lambda (entry)
                   (pair? (definition-entry-equation-ranges entry)))
                 definitions)
          (count (lambda (entry)
                   (null? (definition-entry-equation-ranges entry)))
                 definitions))
  (for ([state (in-list port-states)])
    (printf "definition ledger port-state ~a: ~a\n" state
            (count (lambda (entry)
                     (eq? (definition-entry-port-state entry) state))
                   definitions)))
  (for* ([entry (in-list definitions)]
         [domain (in-list (definition-entry-domains entry))]
         #:when (member (definition-domain-status domain)
                        '(blocked prose-only-gap)))
    (printf "definition ledger domain ~a/~a (~a~a): ~a\n"
            (definition-entry-id entry) (definition-domain-name domain)
            (definition-domain-status domain)
            (if (definition-domain-issue domain)
                (format ", ~a" (definition-domain-issue domain)) "")
            (definition-domain-reason domain)))
  (for ([class (in-list branch-classes)])
    (printf "infer-core branches ~a: ~a\n" class
            (count (lambda (entry) (eq? (branch-entry-class entry) class))
                   branches)))
  (define helpers (load-infer-helpers))
  (for ([class (in-list branch-classes)])
    (printf "reachable helpers ~a: ~a\n" class
            (count (lambda (entry) (eq? (helper-entry-class entry) class))
                   helpers)))
  (define decisions (load-infer-decisions))
  (for ([class (in-list branch-classes)])
    (printf "internal decisions ~a: ~a\n" class
            (count (lambda (entry) (eq? (decision-entry-class entry) class))
                   decisions)))
  (define values (load-infer-value-helpers))
  (for ([class (in-list branch-classes)])
    (printf "reachable values ~a: ~a\n" class
            (count (lambda (entry) (eq? (value-helper-entry-class entry) class))
                   values)))
  (define migrations
    (filter (lambda (entry) (eq? (target-migration-family entry) 'B1))
            (load-target-migrations)))
  (printf "B1 target migrations: sources=~a full=~a partial=~a targets=~a\n"
          (length migrations)
          (count (lambda (entry)
                   (eq? (target-migration-extent entry) 'full))
                 migrations)
          (count (lambda (entry)
                   (eq? (target-migration-extent entry) 'partial))
                 migrations)
          (set-count
           (list->set (append-map target-migration-targets migrations))))
  (match (load-b1-lowering-manifest)
    [`(smusni-b1-lowering-subterms 1 ,_ ... (outputs ,outputs ...))
     (define (disposition-count wanted)
       (count (lambda (output)
                (match output
                  [`(output ,_ ... (disposition ,found) ,_ ...)
                   (eq? found wanted)]))
              outputs))
     (define subterm-count
       (for/sum ([output (in-list outputs)])
         (match output
           [`(output ,_ ... (subterms ,subterms ...)) (length subterms)])))
     (printf "B1 lowering manifest: outputs=~a selected=~a no-family-head=~a unrepresentable=~a subterms=~a\n"
             (length outputs) (disposition-count 'selected)
             (disposition-count 'no-family-head)
             (disposition-count 'unrepresentable) subterm-count)])
  (printf "diagnostic taxonomy: typing=~a no-lowering=~a allowed-evidence=~a forbidden-evidence=~a\n"
          (length (diagnostic-taxonomy-typing-causes taxonomy))
          (length (diagnostic-taxonomy-no-lowering-causes taxonomy))
          (length (diagnostic-taxonomy-allowed-evidence taxonomy))
          (length (diagnostic-taxonomy-forbidden-evidence taxonomy))))

(define (run-phase0-gate #:print? [print? #t] #:benchmark? [benchmark? #t])
  (define definitions (load-definition-ledger))
  (define branches (load-infer-branches))
  (define taxonomy (load-diagnostic-taxonomy))
  (define findings
    (append (definition-ledger-findings
             (extract-definition-observations) definitions)
            (infer-branch-findings (extract-infer-branches) branches)
            (target-migration-findings)
            (b1-lowering-manifest-findings)
            (b1-growth-profile-findings)
            (diagnostic-taxonomy-findings taxonomy)))
  (define cases
    (with-handlers ([exn:fail? (lambda (exception)
                                (set! findings
                                      (append findings
                                              (list (exn-message exception))))
                                '())])
      (load-port-corpus)))
  (define differential-ok? #f)
  (when (pair? cases)
    (define-values (ok? _differences _stale)
      (run-differential cases (load-port-waivers) #:print? print?))
    (set! differential-ok? ok?))
  (define a0-differential-ok? #f)
  (define-values (a0-ok? _a0-differences _a0-stale)
    (run-a0-differential #:print? print?))
  (set! a0-differential-ok? a0-ok?)
  (when print?
    (print-classification-summary definitions branches taxonomy))
  (when (and benchmark? (pair? cases))
    (define baseline (load-port-baseline))
    (define modes (run-benchmarks #:print? print?))
    (when print? (print-baseline-trigger-report baseline modes)))
  (when print?
    (for ([finding (in-list findings)])
      (printf "PHASE0-ERROR ~a\n" finding)))
  (and (null? findings) differential-ok? a0-differential-ok?))

(module+ main
  (define action 'check)
  (define full-gate-ms 37000.0)
  (define observed-full-gate-ms #f)
  (command-line
   #:program "port-phase0.rkt"
   #:once-each
   [("--check") "run the Phase 0 gates" (set! action 'check)]
   [("--refresh-corpus") "regenerate the frozen differential corpus"
    (set! action 'refresh-corpus)]
   [("--refresh-baseline") "regenerate the benchmark baseline"
    (set! action 'refresh-baseline)]
   [("--refresh-branches") "refresh reviewed infer branch ranges and source digests"
    (set! action 'refresh-branches)]
   [("--refresh-b1-lowering")
    "regenerate the tracked B1 lowering-subterm dispositions"
    (set! action 'refresh-b1-lowering)]
   [("--full-gate-ms") milliseconds "record the measured pre-port full-gate baseline"
    (set! full-gate-ms (string->number milliseconds))]
   [("--report-full-gate-ms") milliseconds
    "compare one externally measured full-gate run with the recorded trigger"
    (set! observed-full-gate-ms (string->number milliseconds))
    (set! action 'report-full-gate)])
  (case action
    [(refresh-corpus)
     (define cases (refresh-port-corpus!))
     (printf "port corpus refreshed: ~a cases sha1=~a\n"
             (length cases) (corpus-cases-digest cases))]
    [(refresh-baseline)
     (refresh-port-baseline! #:full-gate-ms full-gate-ms)
     (displayln "port benchmark baseline refreshed")]
    [(refresh-branches)
     (define entries (refresh-infer-branch-metadata!))
     (printf "infer-core branch metadata refreshed: ~a entries\n"
             (length entries))]
    [(refresh-b1-lowering)
     (define datum (refresh-b1-lowering-manifest!))
     (match datum
       [`(smusni-b1-lowering-subterms 1 (count ,count) ,_ ...)
        (printf "B1 lowering manifest refreshed: ~a outputs\n" count)])]
    [(report-full-gate)
     (void (report-full-gate-trigger observed-full-gate-ms))]
    [else (exit (if (run-phase0-gate) 0 1))]))
