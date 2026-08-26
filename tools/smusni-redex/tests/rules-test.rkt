#lang racket

(require rackunit
         racket/set
         "../check.rkt"
         "../extract.rkt")

;; Gate 3a (#9 M1): rule ids come from spec §11; citations from the manifest.
(define ids (spec-rule-ids))
(define rules (spec-rules))
(check-true (>= (length ids) 140))
(check-true (ormap (lambda (r) (eq? (cdr r) 'gap)) rules) "gap rules are classified")
(check-equal? (length ids) (set-count (list->set ids)))
(check-not-false (member "L1.1" ids) "L1.1 present")

(define (fake source ordinal rules [origin "surface"])
  (fence source ordinal 1 "" "digest" 'specimen #f #f rules origin))
(define (R . ids) (map (lambda (id) (cons id 'map)) ids))

(define-values (clean cited ledgered)
  (rule-coverage-findings (R "L1.1" "L1.2")
                          (list (fake "s" 1 '("L1.1")) (fake "s" 9 '() "core"))
                          '(("L1.2" . "#9"))
                          1))
(check-equal? clean '())
(check-equal? cited 1)
(check-equal? ledgered 1)

(define-values (bad _c _l)
  (rule-coverage-findings (R "L1.1" "L1.2" "L1.3")
                          (list (fake "s" 1 '("L9.99"))   ; unknown id
                                (fake "s" 2 '()))          ; no citation
                          '(("L1.1" . "#9")               ; ledgered but cited? no: L1.1 not cited
                            ("L7.7" . "#9"))             ; ledger names unknown rule
                          0))
(define messages (map cdr bad))
(check-true (ormap (lambda (m) (regexp-match? #rx"unknown rule L9.99" m)) messages))
(check-true (ormap (lambda (m) (regexp-match? #rx"cites no lowering rule" m)) messages))
(check-true (ormap (lambda (m) (regexp-match? #rx"names unknown rule L7.7" m)) messages))
(check-true (ormap (lambda (m) (regexp-match? #rx"L1.2 is cited by no specimen" m)) messages))
(check-true (ormap (lambda (m) (regexp-match? #rx"L1.3 is cited by no specimen" m)) messages))

(define-values (stale _c2 _l2)
  (rule-coverage-findings (R "L1.1") (list (fake "s" 1 '("L1.1"))) '(("L1.1" . "#9")) 1))
(check-true (ormap (lambda (m) (regexp-match? #rx"but a specimen cites it" (cdr m))) stale))


;; Ratchet: coverage below the floor fails; coverage above it demands a raise.
(define-values (below _c3 _l3)
  (rule-coverage-findings (R "L1.1" "L1.2") (list (fake "s" 1 '("L1.1"))) '(("L1.2" . "#9")) 2))
(check-true (ormap (lambda (m) (regexp-match? #rx"below the ratchet floor 2" (cdr m))) below))
(define-values (above _c4 _l4)
  (rule-coverage-findings (R "L1.1" "L1.2") (list (fake "s" 1 '("L1.1" "L1.2"))) '() 1))
(check-true (ormap (lambda (m) (regexp-match? #rx"raise \\(cited-floor 1\\)" (cdr m))) above))
(define-values (floor-ok ledger-ok) (load-rule-coverage))
(check-true (exact-nonnegative-integer? floor-ok))
(check-true (list? ledger-ok))


;; Kinds and origins: a gap rule is never citable or ledgerable; a core
;; fixture cites nothing; a surface specimen must cite.
(define-values (kinds _c5 _l5)
  (rule-coverage-findings (list (cons "L1.1" 'map) (cons "L1.2" 'gap))
                          (list (fake "s" 1 '("L1.2")) (fake "s" 2 '("L1.1") "core"))
                          '(("L1.2" . "#9")) 0))
(define kmsgs (map cdr kinds))
(check-true (ormap (lambda (m) (regexp-match? #rx"L1.2, a gap rule" m)) kmsgs))
(check-true (ormap (lambda (m) (regexp-match? #rx"core specimen s#2 must not cite" m)) kmsgs))
(check-true (ormap (lambda (m) (regexp-match? #rx"lists L1.2, a gap rule" m)) kmsgs))

(displayln "rules tests: ok")
