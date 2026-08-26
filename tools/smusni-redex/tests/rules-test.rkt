#lang racket

(require rackunit
         racket/set
         "../check.rkt"
         "../extract.rkt")

;; Gate 3a (#9 M1): rule ids come from spec §11; citations from the manifest.
(define ids (spec-rule-ids))
(check-true (>= (length ids) 140))
(check-equal? (length ids) (set-count (list->set ids)))
(check-not-false (member "L1.1" ids) "L1.1 present")

(define (fake source ordinal rules)
  (fence source ordinal 1 "" "digest" 'specimen #f #f rules))

(define-values (clean cited ledgered)
  (rule-coverage-findings '("L1.1" "L1.2")
                          (list (fake "s" 1 '("L1.1")))
                          '(("L1.2" . "#9"))))
(check-equal? clean '())
(check-equal? cited 1)
(check-equal? ledgered 1)

(define-values (bad _c _l)
  (rule-coverage-findings '("L1.1" "L1.2" "L1.3")
                          (list (fake "s" 1 '("L9.99"))   ; unknown id
                                (fake "s" 2 '()))          ; no citation
                          '(("L1.1" . "#9")               ; ledgered but cited? no: L1.1 not cited
                            ("L7.7" . "#9"))))            ; ledger names unknown rule
(define messages (map cdr bad))
(check-true (ormap (lambda (m) (regexp-match? #rx"unknown rule L9.99" m)) messages))
(check-true (ormap (lambda (m) (regexp-match? #rx"cites no lowering rule" m)) messages))
(check-true (ormap (lambda (m) (regexp-match? #rx"names unknown rule L7.7" m)) messages))
(check-true (ormap (lambda (m) (regexp-match? #rx"L1.2 is cited by no specimen" m)) messages))
(check-true (ormap (lambda (m) (regexp-match? #rx"L1.3 is cited by no specimen" m)) messages))

(define-values (stale _c2 _l2)
  (rule-coverage-findings '("L1.1") (list (fake "s" 1 '("L1.1"))) '(("L1.1" . "#9"))))
(check-true (ormap (lambda (m) (regexp-match? #rx"but a specimen cites it" (cdr m))) stale))

(displayln "rules tests: ok")
