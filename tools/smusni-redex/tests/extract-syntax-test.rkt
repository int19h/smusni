#lang racket

(require rackunit
         racket/list
         "../extract.rkt"
         "../syntax.rkt")

(define all-fences (read-all-fences))
(check-not-exn (lambda () (validate-notation! all-fences)))
(check-equal? (length all-fences) 81)
(check-equal? (count (lambda (item) (string=? (fence-source item) "samples.md"))
                     all-fences)
              60)
(check-equal? (count (lambda (item) (string=? (fence-source item) "spec.md"))
                     all-fences)
              21)

(define classified (classify-fences all-fences (load-manifest)))
(check-equal? (count (lambda (item) (eq? (fence-kind item) 'specimen))
                     classified)
              64)
(check-equal? (count (lambda (item) (eq? (fence-kind item) 'unchecked))
                     classified)
              0)
(check-not-exn (lambda () (check-corpus! classified)))

(for ([item (in-list classified)]
      #:when (eq? (fence-kind item) 'specimen))
  (define forms
    (read-core-forms (fence-content item)
                     (format "~a:~a" (fence-source item)
                             (fence-start-line item))))
  (check-true (pair? forms)
              (format "~a fence ~a has a term"
                      (fence-source item) (fence-ordinal item)))
  (for ([form (in-list forms)])
    (check-true (core-list? form)
                (format "~a fence ~a has only top-level forms"
                        (fence-source item) (fence-ordinal item)))
    (check-not-exn (lambda () (validate-core-form form)))))

(define lambda-form
  (read-core-specimen "{λ [$x :: Entity] (gerku $x)}" 'lambda-test))
(define lambda-paren-form
  (read-core-specimen "(λ ($x :: Entity) (gerku $x))" 'lambda-paren-test))
(check-equal? (core->datum lambda-form) (core->datum lambda-paren-form))

(check-not-exn
 (lambda ()
   (read-core-specimen
    "{Bind [$x :: Entity] (Context) [$y :: Entity] (Refer P) (R $x $y)}"
    'variadic-bind)))

(check-exn
 exn:fail?
 (lambda () (read-core-specimen "(gerku x) (mlatu y)" 'two-terms)))

(define apostrophe-form (read-core-specimen "(te'a 2 3)" 'apostrophe))
(check-equal? (core-atom-value (first (core-list-elements apostrophe-form)))
              (string->symbol "te'a"))

(displayln "extract/syntax tests: ok")
