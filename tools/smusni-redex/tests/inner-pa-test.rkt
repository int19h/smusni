#lang racket
(require json rackunit racket/list racket/match racket/runtime-path
         "../lower.rkt" "../syntax.rkt")

;; Fable F1, confirmed by Astra (2026-09-10). These grammar probes replace the
;; complete PA run in a real gentufa parse, preserving every continuation and
;; adjusting its source spans. They do not claim a new inner-PA interpretation.
(define-runtime-path probe-path "../inventory/parses/in-place-probes.json")
(define base
  (findf (lambda (p) (equal? (hash-ref p 'surface) "mi tavla lo ci gerku"))
         (hash-ref (call-with-input-file probe-path read-json) 'cases)))
(define count-start (caar (regexp-match-positions #rx"ci" (hash-ref base 'surface))))
(define count-end (+ count-start 2))
(define (terminal word start)
  (hash 'Plain (hash 'PlainWord (hash 'Cmavo
    (hash 'phonemes word 'span (list start (+ start (string-length word))))))))
(define (input words)
  (define run-text (string-join words " "))
  (define delta (- (string-length run-text) 2))
  (define (walk node)
    (cond
      [(hash? node)
       (for/hash ([(key value) (in-hash node)])
         (values key
           (cond
             [(eq? key 'PaRunQuantifier)
              (hash 'number
                (hash 'first_number (terminal (first words) count-start)
                      'continuations
                      (for/list ([word (rest words)] [index (in-naturals 1)])
                        (hash 'NumberWordPaContinuation
                          (terminal word (+ count-start index
                                            (apply + (map string-length (take words index)))))))))]
             [(eq? key 'span) (map (lambda (n) (if (>= n count-end) (+ n delta) n)) value)]
             [else (walk value)])))]
      [(list? node) (map walk node)]
      [else node]))
  (hash-set (hash-set base 'parse (walk (hash-ref base 'parse))) 'surface
    (string-append (substring (hash-ref base 'surface) 0 count-start)
                   run-text (substring (hash-ref base 'surface) count-end))))
(define fields
  (hash 'parse '("inner-pa-regression" 1) 'attach '() 'readings '(actual inner-pa)
        'rows '(gerku tavla) 'stores '() 'sites '() 'anaphora '() 'force '(assert)
        'references (map (lambda (start) `(,start invariant)) (reference-occurrences base))))
(define positive (lower (input '("ci")) (rr-case 1 fields)))
(check-true (lowered? positive))
(check-true
 (redex-alpha-equivalent?
  (core->plain-datum (lowered-term positive))
  '(Bind ($r :: Referents Entity)
         (Refer (λ ($reference :: Referents Entity)
                  (∧ (gerku $reference)
                     (= (CardBasis $reference (λ ($unit :: Entity) (gerku $unit))) 3))))
     (Assert (Close (tavla Speaker $r))))))

(for ([words '(("su'o") ("su'o" "re") ("su'o" "re" "mu")
              ("re" "mu") ("no" "ci") ("me'i") ("me'i" "pa"))]
      [reason '(#rx"bare inner su'o" #rx"inner su'o n" #rx"inner su'o n"
                #rx"multi-digit inner exact" #rx"multi-digit inner exact"
                #rx"inner me'i" #rx"inner me'i")])
  (define parse (input words))
  (define result (lower parse (rr-case 1 fields)))
  (check-equal? (no-lowering-rule result) "L3.9")
  (check-equal? (no-lowering-cause result) 'rule-underspecified)
  (check-regexp-match reason (no-lowering-premise result))
  (check-equal? (no-lowering-detail result) words)
  ;; Coverage refusal must follow unrelated RR checks, not mask bad inputs.
  (for ([bad-fields (list (hash-set fields 'stores '(unexpected))
                          (hash-set fields 'rows '(tavla))
                          (hash-set fields 'references '()))])
    (check-equal? (no-lowering-cause (lower parse (rr-case 1 bad-fields))) 'rr-missing)))

(define (corrupt-continuation node)
  (cond [(hash? node)
         (for/hash ([(key value) (in-hash node)])
           (values (if (eq? key 'NumberWordPaContinuation) 'UnknownContinuation key)
                   (corrupt-continuation value)))]
        [(list? node) (map corrupt-continuation node)]
        [else node]))
(define malformed (input '("ci" "pa")))
(define bad-result
  (lower (hash-set malformed 'parse (corrupt-continuation (hash-ref malformed 'parse)))
         (rr-case 1 fields)))
(check-equal? (no-lowering-rule bad-result) "L3.9")
(check-regexp-match #rx"unknown wrapper" (no-lowering-premise bad-result))
