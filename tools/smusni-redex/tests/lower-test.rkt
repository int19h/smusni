#lang racket

(require rackunit
         racket/list
         racket/set
         "../lower.rkt")

(define manifest (load-lowering-manifest))
(check-equal? (lowering-manifest-families manifest) '("L0" "L1" "L3" "L5"))
(check-equal? (lowering-manifest-rule-count manifest) 46)
(check-equal? (length (lowering-manifest-candidates manifest)) 25)
(check-equal?
 (for/sum ([candidate (in-list (lowering-manifest-candidates manifest))])
   (length (lowering-candidate-cases candidate)))
 28)

(define rules (fragment-rule-ids manifest))
(check-equal? (length rules) 46)
(check-not-false (member "L0.1" rules))
(check-not-false (member "L1.10" rules))
(check-not-false (member "L3.15" rules))
(check-not-false (member "L5.29" rules))
(check-false (member "L1.9" rules))
(check-false (member "L3.7" rules))
(check-false (member "L5.14" rules))

(check-not-exn (lambda () (validate-lowering-fixtures! manifest)))

(define samples-17
  (findf (lambda (candidate)
           (and (string=? (lowering-candidate-source candidate) "samples.md")
                (= (lowering-candidate-ordinal candidate) 17)))
         (lowering-manifest-candidates manifest)))
(check-equal? (map lowering-case-index (lowering-candidate-cases samples-17))
              '(1 2))
(define samples-17-parse (load-parse-fixture samples-17))
(check-equal? (hash-ref samples-17-parse 'source) "samples.md")
(check-equal? (length (hash-ref samples-17-parse 'cases)) 2)
(for ([case (in-list (hash-ref samples-17-parse 'cases))])
  (check-true (hash? (hash-ref case 'parse))))

(define samples-63
  (findf (lambda (candidate)
           (and (string=? (lowering-candidate-source candidate) "samples.md")
                (= (lowering-candidate-ordinal candidate) 63)))
         (lowering-manifest-candidates manifest)))
(check-equal? (length (rr-fixture-cases (load-rr-fixture samples-63))) 3)

(define spec-10
  (findf (lambda (candidate)
           (and (string=? (lowering-candidate-source candidate) "spec.md")
                (= (lowering-candidate-ordinal candidate) 10)))
         (lowering-manifest-candidates manifest)))
(define spec-10-case (first (lowering-candidate-cases spec-10)))
(check-false (lowering-case-surface spec-10-case))
(check-true (string-contains? (lowering-case-unresolved spec-10-case)
                              "missing Lojban surface"))
(check-false
 (hash-ref (first (hash-ref (load-parse-fixture spec-10) 'cases)) 'parse))

(define absent
  (lower 'parse 'rr))
(check-true (no-lowering? absent))
(check-equal? (no-lowering-cause absent) 'implementation)

(displayln "lowering fixture tests: ok")
