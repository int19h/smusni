#lang racket

(require racket/set "common.rkt")

(provide contribution-results)

(define profile
  (law-profile 'contribution-basis 'live-baseline
               '(permutation duplicate-collapse every-operand-contributes)))

(define (contribution-failures required observed)
  (if (subset? required observed) '() '(every-operand-contributes)))

(define contribution-results
  (for/list ([fixture
              (list (list 'blue-red (set 'blue 'red) (set 'blue 'red))
                    (list 'lion-tiger-origin
                          (set 'lion-origin 'tiger-origin)
                          (set 'lion-origin 'tiger-origin))
                    (list 'desire-fear-aspects
                          (set 'desire-aspect 'fear-aspect)
                          (set 'desire-aspect 'fear-aspect))
                    (list 'missing-red (set 'blue 'red) (set 'blue)))])
    (define failures (contribution-failures (second fixture) (third fixture)))
    (make-result (first fixture) profile
                 (if (eq? (first fixture) 'missing-red) 'reject 'accept)
                 failures)))

