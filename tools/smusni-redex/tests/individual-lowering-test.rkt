#lang racket

(require json rackunit racket/list racket/match racket/runtime-path
         "../lower.rkt" "../syntax.rkt" "../types.rkt")

(define-runtime-path parse-path "../inventory/parses/samples-044.json")
(define base (first (hash-ref (call-with-input-file parse-path read-json) 'cases)))
(define (terminal word start)
  (hash 'Plain (hash 'PlainWord
                     (hash 'Cmavo (hash 'phonemes word
                                        'span (list start (+ start (string-length word))))))))
(define (replace-count node words)
  (define delta (- (string-length (string-join words " ")) 2))
  (cond
    [(hash? node)
     (for/hash ([(key value) (in-hash node)])
       (values key
               (cond [(eq? key 'span) (map (lambda (n) (+ n delta)) value)]
                     [(eq? key 'PaRunQuantifier)
                   (hash 'number
                         (hash 'first_number (terminal (first words) 0)
                               'continuations
                               (for/list ([word (in-list (rest words))]
                                          [index (in-naturals 1)])
                                 (hash 'NumberWordPaContinuation
                                       (terminal word
                                                 (add1 (string-length
                                                        (string-join (take words index) " "))))))))]
                     [else (replace-count value words)])))]
    [(list? node) (map (lambda (v) (replace-count v words)) node)]
    [else node]))
(define (input words)
  (hash-set (hash-set base 'parse (replace-count (hash-ref base 'parse) words))
            'surface (string-join (append words '("gerku" "cu" "blabi")) " ")))
(define (rr readings)
  (rr-case 1 (hash 'parse '("test" 1) 'attach '() 'readings readings
                   'rows '(gerku blabi) 'stores '() 'sites '()
                   'references '() 'anaphora '() 'force '(assert))))
(define P '(λ ($p :: Entity) (gerku $p)))
(define Q '(λ ($q :: Entity) (Close (blabi $q))))
(for ([words '(("ci") ("re" "mu") ("su'o" "re") ("su'e")
              ("za'u" "pa") ("me'i" "pa") ("da'a") ("me'i"))]
      [quantity '(3 25 (at-least 2) (at-most 1) (more-than 1)
                  (fewer-than 1) (all-but 1) not-all)])
  (define readings (if (number? quantity) '(actual global-exact)
                       '(actual individual-count)))
  (define result (lower (input words) (rr readings)))
  (check-true (lowered? result) (format "~s: ~s" words result))
  (when (lowered? result)
    (check-not-false (member (if (equal? quantity '(all-but 1)) "L5.4" "L5.2")
                             (lowered-rules result)))
    (check-equal? (typing-type (infer-core (lowered-term result))) '(Act Assertion))
    (check-true
     (redex-alpha-equivalent?
      (normalization-datum (normalize-core (lowered-term result) (rr readings)))
      (normalization-datum
       (normalize-core
        (datum->core `(Assert ,(individual-count-condition quantity P Q)))
        (rr readings)))))))

;; Domain-size independent bare me'i must remain universal negation.
(check-equal? (individual-count-condition 'not-all P Q)
              `(¬ (IndividualEvery ,P ,Q)))
(check-equal? (individual-count-condition '(at-most 4) 'P 'Q)
              '(≤ (Card (SetOf (λ ($individual :: Entity)
                                (∧ (P $individual) (Q $individual))))) 4))
(for ([words '(("ro") ("su'o") ("su'o" "pa") ("no"))]
      [head '(IndividualEvery IndividualSome IndividualSome IndividualNo)])
  (define readings (if (eq? head 'IndividualEvery) '(actual non-importing)
                       '(actual individual)))
  (define result (lower (input words) (rr readings)))
  (check-true (lowered? result) (format "~s: ~s" words result))
  (when (lowered? result)
    (check-true (regexp-match? (regexp (symbol->string head))
                               (format "~s" (core->datum (lowered-term result)))))))

;; Retired metadata cannot silently recover a standard reading.
(for ([words '(("ci") ("ro") ("su'o"))]
      [readings '((actual witness-set) (actual importing) (actual witness-set))])
  (check-true (no-lowering? (lower (input words) (rr readings)))))
(for ([words '(("su'o" "me'i" "ci") ("ci" "pi" "mu") ("me'i" "ro"))])
  (check-true (no-lowering? (lower (input words) (rr '(actual individual-count))))))
