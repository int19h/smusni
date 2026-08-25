#lang racket

(require rackunit
         racket/list
         "../extract.rkt"
         "../syntax.rkt")

(define all-fences (read-all-fences))
(check-equal? (length all-fences) 81)
(check-equal? (count (lambda (item) (string=? (fence-source item) "samples.md"))
                     all-fences)
              60)
(check-equal? (count (lambda (item) (string=? (fence-source item) "spec.md"))
                     all-fences)
              21)

(define lambda-form
  (read-core-specimen "(λ {$x :: Entity} {(gerku $x)})" 'lambda-test))
(check-equal? (core-list-shape lambda-form) 'paren)
(check-equal? (core-list-shape (second (core-list-elements lambda-form))) 'brace)

(check-exn
 exn:fail?
 (lambda ()
   (read-core-specimen "(λ ($x :: Entity) {(gerku $x)})" 'bad-braces)))

(check-not-exn
 (lambda ()
   (read-core-specimen
    "(Bind {$x :: Entity} (Context) {$y :: Entity} (Refer P) {(R $x $y)})"
    'variadic-bind)))

(check-exn
 exn:fail?
 (lambda () (read-core-specimen "(gerku x) (mlatu y)" 'two-terms)))

(displayln "extract/syntax tests: ok")

