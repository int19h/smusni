#lang racket

(require racket/cmdline
         racket/list
         racket/match
         racket/runtime-path
         racket/string
         "elaborate.rkt"
         "extract.rkt"
         "inventory.rkt"
         "syntax.rkt"
         "types.rkt")

(provide run-checks)

(define-runtime-path tool-dir ".")
(define expected-findings-path
  (build-path tool-dir "inventory" "expected-findings.sexp"))

(struct expected-finding (source ordinal digest phase pattern issue note)
  #:transparent)
(struct observed-finding (source ordinal digest phase message) #:transparent)

(define (load-expected-findings)
  (match (call-with-input-file expected-findings-path read)
    [`(smusni-expected-findings 1 ,entries ...)
     (for/list ([entry (in-list entries)])
       (match entry
         [`(finding ,source ,ordinal ,digest ,phase ,pattern ,issue ,note)
          (expected-finding source ordinal digest phase pattern issue note)]
         [else (error 'load-expected-findings "invalid expected finding: ~e" entry)]))]
    [else (error 'load-expected-findings "unsupported expected-findings header")]))

(define (finding-key source ordinal) (cons source ordinal))

(define (match-expected observed expected-by-key)
  (define key (finding-key (observed-finding-source observed)
                           (observed-finding-ordinal observed)))
  (define expected (hash-ref expected-by-key key #f))
  (and expected
       (string=? (observed-finding-digest observed)
                 (expected-finding-digest expected))
       (eq? (observed-finding-phase observed)
            (expected-finding-phase expected))
       (string-contains? (observed-finding-message observed)
                         (expected-finding-pattern expected))
       expected))

(define (run-checks #:strict? [strict? #f])
  (define inventory (load-inventory))
  (check-assembled! inventory)
  (define classified
    (classify-fences (read-all-fences) (load-manifest)))
  (check-corpus! classified)

  (define expected-findings (load-expected-findings))
  (define expected-by-key
    (for/hash ([finding (in-list expected-findings)])
      (values (finding-key (expected-finding-source finding)
                           (expected-finding-ordinal finding))
              finding)))
  (define matched-expected (make-hash))
  (define unexpected '())
  (define passed-fences 0)
  (define passed-terms 0)
  (define schema-count 0)
  (define expansion-count 0)
  (define declaration-count 0)
  (define site-count 0)
  (define choice-count 0)

  (for ([item (in-list classified)])
    (case (fence-kind item)
      [(specimen)
       (with-handlers
           ([exn:fail?
             (lambda (exception)
               (define observed
                 (observed-finding (fence-source item) (fence-ordinal item)
                                   (fence-digest item) 'type-error
                                   (exn-message exception)))
               (define expected (match-expected observed expected-by-key))
               (if expected
                   (hash-set! matched-expected
                              (finding-key (fence-source item)
                                           (fence-ordinal item))
                              expected)
                   (set! unexpected (cons observed unexpected))))])
         (define forms
           (read-core-forms (fence-content item)
                            (format "~a#~a" (fence-source item)
                                    (fence-ordinal item))))
         (for ([form (in-list forms)])
           (validate-core-form form)
           (define elaborated (elaborate-core form inventory))
           (set! site-count (+ site-count (length (elaboration-sites elaborated))))
           (set! choice-count
                 (+ choice-count (length (elaboration-choices elaborated))))
           (define result (infer-core (elaboration-ast elaborated) (hash) inventory))
           (unless (null? (typing-gaps result))
             (error 'check.rkt "unresolved typing gaps: ~a"
                    (string-join (typing-gaps result) "; ")))
           (set! passed-terms (add1 passed-terms)))
         (set! passed-fences (add1 passed-fences)))]
      [(schema)
       (read-core-forms (fence-content item)
                        (format "~a#~a" (fence-source item)
                                (fence-ordinal item)))
       (set! schema-count (add1 schema-count))]
      [(expansion)
       (read-core-forms (fence-content item)
                        (format "~a#~a" (fence-source item)
                                (fence-ordinal item)))
       (set! expansion-count (add1 expansion-count))]
      [(declaration)
       (read-core-forms (fence-content item)
                        (format "~a#~a" (fence-source item)
                                (fence-ordinal item)))
       (set! declaration-count (add1 declaration-count))]
      [(unchecked)
       (set! unexpected
             (cons (observed-finding
                    (fence-source item) (fence-ordinal item)
                    (fence-digest item) 'unchecked
                    (format "unchecked fence: ~a (~a)"
                            (fence-note item) (fence-issue item)))
                   unexpected))]))

  (define stale-expected
    (for/list ([expected (in-list expected-findings)]
               #:unless (hash-has-key?
                         matched-expected
                         (finding-key (expected-finding-source expected)
                                      (expected-finding-ordinal expected))))
      expected))

  (printf "corpus: ~a fences classified; ~a specimen fences/~a terms pass\n"
          (length classified) passed-fences passed-terms)
  (printf "coverage: ~a schemata, ~a expansions, ~a declarations, 0 unchecked\n"
          schema-count expansion-count declaration-count)
  (printf "elaboration: ~a retrieval sites, ~a recorded choices\n"
          site-count choice-count)
  (define sorted-matched-keys
    (sort (hash-keys matched-expected)
          (lambda (left right)
            (string<? (format "~a" left) (format "~a" right)))))
  (for ([key (in-list sorted-matched-keys)])
    (define finding (hash-ref matched-expected key))
    (printf "KNOWN ~a#~a [~a] ~a — ~a\n"
            (expected-finding-source finding)
            (expected-finding-ordinal finding)
            (expected-finding-issue finding)
            (expected-finding-pattern finding)
            (expected-finding-note finding)))
  (for ([finding (in-list (reverse unexpected))])
    (printf "UNEXPECTED ~a#~a [~a] ~a\n"
            (observed-finding-source finding)
            (observed-finding-ordinal finding)
            (observed-finding-phase finding)
            (observed-finding-message finding)))
  (for ([finding (in-list stale-expected)])
    (printf "STALE-EXPECTED ~a#~a [~a] no longer produces: ~a\n"
            (expected-finding-source finding)
            (expected-finding-ordinal finding)
            (expected-finding-issue finding)
            (expected-finding-pattern finding)))

  (define failure?
    (or (pair? unexpected)
        (pair? stale-expected)
        (and strict? (positive? (hash-count matched-expected)))))
  (when (and strict? (positive? (hash-count matched-expected)))
    (printf "STRICT: ~a known findings remain\n" (hash-count matched-expected)))
  (if failure? 1 0))

(module+ main
  (define strict? #f)
  (command-line
   #:program "check.rkt"
   #:once-each
   [("--strict") "fail while any known corpus finding remains"
    (set! strict? #t)])
  (exit (run-checks #:strict? strict?)))
