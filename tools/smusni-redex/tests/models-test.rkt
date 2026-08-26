#lang racket

(require rackunit
         racket/set
         "../models/common.rkt"
         "../models/contribution.rkt"
         "../models/constitution.rkt"
         "../models/contrast.rkt"
         "../models/kernel.rkt"
         "../models/run.rkt"
         "../models/symbolic.rkt")

(for ([result all-model-results])
  (check-true (result-ok? result)
              (format "~a under ~a"
                      (model-result-model result)
                      (law-profile-name (model-result-profile result)))))

(check-false (covered-by? (lambda (x) (eq? x 'dog)) (set 'dog 'cat)))
(check-true (refinement-stable? (lambda (x) (member x '(dog1 dog2)))
                                (set 'dog1 'dog2)))
(check-true (refinement-stable? (lambda (x) (member x '(dog1 dog2)))
                                (set 'dog1 'cat)))
(check-true (proper-refinement-witness? (dyadic-interval 0 1)))
(check-equal? (hash-ref (constitution-bounded-search) 'structures) 16)
(check-equal? (hash-ref (contrast-bounded-search) 'structures) 512)
(check-true
 (parameterize ([current-output-port (open-output-nowhere)])
   (run-model-bank)))

(displayln "model-bank tests: ok")
