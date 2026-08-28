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
         "extract.rkt"
         "inventory.rkt"
         "syntax.rkt"
         "types.rkt")

(provide (struct-out definition-observation)
         (struct-out definition-entry)
         (struct-out definition-domain)
         (struct-out branch-observation)
         (struct-out branch-entry)
         (struct-out diagnostic-taxonomy)
         (struct-out port-case)
         (struct-out port-record)
         (struct-out benchmark-mode)
         extract-definition-observations
         load-definition-ledger
         definition-ledger-findings
         extract-infer-branches
         load-infer-branches
         refresh-infer-branch-metadata!
         infer-branch-findings
         load-diagnostic-taxonomy
         diagnostic-taxonomy-findings
         load-port-corpus
         collect-port-cases
         refresh-port-corpus!
         run-differential
         load-port-waivers
         run-benchmarks
         run-benchmark-mode
         specimen-benchmark-cases
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
(define port-baseline-path (build-path inventory-dir "port-baseline.sexp"))

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
  (id head section status issue port-state dependencies implementations
      legacy-implementations domains reason)
  #:transparent)
(struct definition-domain (name status issue port-state reason) #:transparent)

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

(define (load-definition-ledger [path definitions-path])
  (match (call-with-input-file path read)
    [`(smusni-definition-ledger 1 ,raw-entries ...)
     (for/list ([raw (in-list raw-entries)])
       (match raw
         [`(definition (id ,(? string? id)) (head ,(? symbol? head))
                       (section ,(? string? section)) (status ,raw-status)
                       (port-state ,(? symbol? port-state))
                       (dependencies ,(? symbol? dependencies) ...)
                       (legacy-implementations ,(? symbol? legacy) ...)
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
                          "definition ~a domain ~a needs one sentence" id name))
                 (unless (member domain-port-state port-states)
                   (error 'load-definition-ledger
                          "definition ~a domain ~a has invalid port state ~e"
                          id name domain-port-state))
                 (definition-domain name parsed-status parsed-issue
                                    domain-port-state domain-reason)]
                [_ (error 'load-definition-ledger
                          "invalid definition domain in ~a: ~e" id raw-domain)])))
          (definition-entry id head section status issue port-state dependencies
                            implementations legacy domains reason)]
         [_ (error 'load-definition-ledger "invalid definition entry: ~e" raw)]))]
    [_ (error 'load-definition-ledger "unsupported definitions ledger")]))

(define (definition-key item)
  (cons (if (definition-entry? item)
            (definition-entry-head item)
            (definition-observation-head item))
        (if (definition-entry? item)
            (definition-entry-section item)
            (definition-observation-section item))))

(define (racket-sources)
  (for/list ([path (in-directory tool-dir)]
             #:when (regexp-match? #px"[.]rkt$" (path->string path)))
    path))

(define (implementation-defined? implementation source-text)
  (match implementation
    [`(metafunction ,(? symbol? name) (cases ,(? symbol? cases) ...))
     (and (regexp-match?
           (pregexp (format "(?s:[(]define-metafunction.*?\n[[:space:]]*~a[[:space:]]*:)"
                            (regexp-quote (symbol->string name))))
           source-text)
          (for/and ([case (in-list cases)])
            (string-contains? source-text
                              (format "definition-case:~a" case))))]
    [`(relation ,(? symbol? name) (cases ,(? symbol? cases) ...))
     (and (string-contains? source-text (format "(define ~a" name))
          (for/and ([case (in-list cases)])
            (string-contains? source-text
                              (format "definition-case:~a" case))))]
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
                (definition-entry-id entry)))]))
  (for ([entry (in-list entries)])
    (define names (map definition-domain-name (definition-entry-domains entry)))
    (unless (= (length names) (set-count (list->set names)))
      (note! "definition ~a has duplicate domain entries"
             (definition-entry-id entry))))
  (define source-text
    (string-join (for/list ([path (in-list (racket-sources))])
                   (file->string path)) "\n"))
  (for ([entry (in-list entries)]
        #:when (eq? (definition-entry-port-state entry) 'legacy-hybrid))
    (for ([name (in-list (definition-entry-legacy-implementations entry))])
      (unless (string-contains? source-text (symbol->string name))
        (note! "legacy-hybrid definition ~a names missing legacy implementation ~a"
               (definition-entry-id entry) name))))
  (for ([entry (in-list entries)]
        #:when (member (definition-entry-port-state entry) '(a0 ported)))
    (for ([implementation (in-list (definition-entry-implementations entry))])
      (unless (implementation-defined? implementation source-text)
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

(define (canonical-branch-id function pattern)
  (define digest
    (sha1 (open-input-string (format "~a|~s" function pattern))))
  (format "B.~a.~a" function (substring digest 0 10)))

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

(define (load-infer-branches [path infer-branches-path])
  (match (call-with-input-file path read)
    [`(smusni-infer-core-branches 1 ,raw-entries ...)
     (for/list ([raw (in-list raw-entries)])
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

(define (refresh-infer-branch-metadata! [path infer-branches-path])
  (define raw (call-with-input-file path read))
  (define observed
    (for/hash ([item (in-list (extract-infer-branches))])
      (values (cons (branch-observation-function item)
                    (branch-observation-pattern item))
              item)))
  (match-define `(smusni-infer-core-branches 1 ,raw-entries ...) raw)
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
                               [entries (load-infer-branches)])
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
       (spec-sha1 ,(file-digest spec-path))
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
       (spec-sha1 ,(? string? spec-digest))
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
     (unless (string=? spec-digest (file-digest spec-path))
       (error 'load-port-corpus "spec.md changed; refresh the frozen corpus deliberately"))
     (unless (equal? test-sources (source-digests (test-files)))
       (error 'load-port-corpus "test sources changed; refresh the frozen corpus deliberately"))
     cases]
    [_ (error 'load-port-corpus "unsupported port corpus")]))

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
          (set-add! used-waivers (port-case-id item))
          (set! differences
                (cons (list item difference-fields old new) differences)))))
  (define stale-waivers
    (for/list ([waiver (in-list waivers)]
               #:unless (match waiver
                          [`(waiver (case ,id) . ,_)
                           (set-member? used-waivers id)]))
      waiver))
  (when print?
    (printf "port differential: ~a cases; differences=~a waivers=~a stale-waivers=~a\n"
            (length cases) (length differences) (set-count used-waivers)
            (length stale-waivers)))
  (values (and (null? differences) (null? stale-waivers))
          (reverse differences) stale-waivers))

;; --------------------------------------------------------------------------
;; P0.4: in-process benchmark and recorded, report-only triggers

(struct benchmark-mode (name totals term-times peak-rss derivations)
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

(define (run-benchmark-mode name cases repetitions)
  (define totals '())
  (define all-term-times '())
  (define derivations 0)
  (define (run-once record?)
    (define started (current-inexact-monotonic-milliseconds))
    (define term-times '())
    (define run-derivations 0)
    (for ([item (in-list cases)])
      (define term-start (current-inexact-monotonic-milliseconds))
      (define calls (if (eq? name 'side-by-side) 2 1))
      (for ([_ (in-range calls)])
        (define result (legacy-record item))
        (set! run-derivations (+ run-derivations (port-record-derivations result))))
      (set! term-times
            (cons (- (current-inexact-monotonic-milliseconds) term-start)
                  term-times)))
    (when record?
      (set! totals (cons (- (current-inexact-monotonic-milliseconds) started)
                         totals))
      (set! all-term-times (append term-times all-term-times))
      (set! derivations (+ derivations run-derivations))))
  (run-once #f)
  (for ([_ (in-range repetitions)]) (run-once #t))
  (benchmark-mode name (reverse totals) all-term-times (peak-rss-bytes)
                  derivations))

(define (benchmark-mode->datum mode)
  `(benchmark-mode ,(benchmark-mode-name mode)
                   (totals ,@(benchmark-mode-totals mode))
                   (term-times ,@(benchmark-mode-term-times mode))
                   (peak-rss ,(benchmark-mode-peak-rss mode))
                   (derivations ,(benchmark-mode-derivations mode))))

(define (datum->benchmark-mode datum)
  (match datum
    [`(benchmark-mode ,(? symbol? name)
                     (totals ,(? real? totals) ...)
                     (term-times ,(? real? term-times) ...)
                     (peak-rss ,(? exact-nonnegative-integer? peak-rss))
                     (derivations ,(? exact-nonnegative-integer? derivations)))
     (benchmark-mode name totals term-times peak-rss derivations)]
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
  (define cases (specimen-benchmark-cases (load-port-corpus)))
  (define modes
    (for/list ([name '(old-only new-only side-by-side)])
      ;; Each mode receives a fresh process so VmHWM/peak RSS is comparable.
      ;; The worker loads and warms before starting its timed repetitions.
      (isolated-benchmark-mode name runs)))
  (when print?
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
    (displayln "port benchmark clause hotspots: unavailable (Phase 0 identity engine has no ported clauses)"))
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
  (define cases (specimen-benchmark-cases (load-port-corpus)))
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
  (define (mode-median name)
    (match (findf (lambda (item) (and (list? item) (eq? (second item) name)))
                  baseline-modes)
      [`(mode ,_ (median-total-ms ,value) . ,_) value]))
  (define (current name)
    (findf (lambda (mode) (eq? (benchmark-mode-name mode) name)) current-modes))
  (define old-baseline (mode-median 'old-only))
  (define new (current 'new-only))
  (define side (current 'side-by-side))
  (define new-median (median (benchmark-mode-totals new)))
  (define side-median (median (benchmark-mode-totals side)))
  (define reports
    (list
     (list 'new-factor (> new-median (* new-factor old-baseline))
           new-median (* new-factor old-baseline))
     (list 'new-wall (> new-median new-wall-ms) new-median new-wall-ms)
     (list 'term-max (> (apply max (benchmark-mode-term-times new)) term-max-ms)
           (apply max (benchmark-mode-term-times new)) term-max-ms)
     (list 'term-p95 (> (percentile (benchmark-mode-term-times new) 0.95)
                           term-p95-ms)
           (percentile (benchmark-mode-term-times new) 0.95) term-p95-ms)
     (let ([rss-limit
            (* rss-factor
               (match (findf (lambda (item)
                               (and (list? item)
                                    (eq? (second item) 'old-only)))
                             baseline-modes)
                 [`(mode ,_ ,_ ,_ ,_ (peak-rss-bytes ,rss)) rss]))])
       (list 'rss (> (benchmark-mode-peak-rss new) rss-limit)
             (benchmark-mode-peak-rss new) rss-limit))
     (list 'side-factor (> side-median (* side-factor old-baseline))
           side-median (* side-factor old-baseline))))
  (printf "port triggers (report-only until B): baseline-head=~a terms=~a full-gate-ms=~a full-gate-limit-ms=~a size-growth-limit=~ax\n"
          head terms full-gate-ms (* full-gate-ms full-gate-factor)
          size-growth-factor)
  (for ([report (in-list reports)])
    (match-define (list name triggered? actual limit) report)
    (printf "  ~a: ~a actual=~a limit=~a\n"
            name (if triggered? "TRIGGER" "ok") actual limit))
  (displayln "  full-gate: external measurement required; use --report-full-gate-ms")
  (displayln "  size-growth: unavailable until A0 supplies the closed grammar and ported judgment"))

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
  (when print?
    (print-classification-summary definitions branches taxonomy))
  (when (and benchmark? (pair? cases))
    (define baseline (load-port-baseline))
    (define modes (run-benchmarks #:print? print?))
    (when print? (print-baseline-trigger-report baseline modes)))
  (when print?
    (for ([finding (in-list findings)])
      (printf "PHASE0-ERROR ~a\n" finding)))
  (and (null? findings) differential-ok?))

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
    [(report-full-gate)
     (void (report-full-gate-trigger observed-full-gate-ms))]
    [else (exit (if (run-phase0-gate) 0 1))]))
