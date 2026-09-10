#lang racket

(require rackunit "../extract.rkt")

(define (validate text)
  (validate-notation!
   (list (fence "test.md" 1 1 text "unused" #f #f #f '() "core"))))

(check-not-exn (lambda () (validate "; prose, Fn<T>, x1\n(gerku $x)")))
(check-not-exn (lambda () (validate "(WordSign \"a, x1; Fn<T>\")")))
(check-not-exn (lambda () (validate "(WordSign \"a\\\"b, c\")")))
(check-exn #rx"comma" (lambda () (validate "; comment\n(foo ,bar)")))
(check-exn #rx"comma" (lambda () (validate "(foo \"text\" ,bar)")))
(check-exn #rx"comma" (lambda () (validate "(foo \"text\\\\\" ,bar)")))
(check-exn #rx"legacy x-prefixed" (lambda () (validate "(foo x1)")))
(check-exn #rx"angle-bracket" (lambda () (validate "(foo Fn<T>)")))
