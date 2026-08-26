#lang racket

(require racket/set)

(provide (struct-out law-profile)
         (struct-out model-result)
         make-result
         result-ok?
         set-coref?)

(struct law-profile (name decision-status laws) #:transparent)
(struct model-result (model profile expected verdict failures) #:transparent)

(define (make-result model profile expected failures)
  (model-result model profile expected
                (if (null? failures) 'accept 'reject)
                failures))

(define (result-ok? result)
  (eq? (model-result-expected result) (model-result-verdict result)))

(define (set-coref? left right) (set=? left right))

