#lang racket

(require racket/set "common.rkt")

(provide contribution-results contribution-law-failures
         contribution-unknown-law-rejected?)

(define profile
  (law-profile 'contribution-basis 'live-baseline
               '(permutation duplicate-collapse every-operand-contributes)))

(struct contribution-fixture (name kind required observed pure-parts) #:transparent)

(define (normalized values) (list->set values))

(define (contribution-law-failures fixture profile)
  (for/list ([law (law-profile-laws profile)]
             #:unless
             (case law
               [(permutation)
                (set=? (normalized (contribution-fixture-observed fixture))
                       (normalized (reverse (contribution-fixture-observed fixture))))]
               [(duplicate-collapse)
                (define observed (contribution-fixture-observed fixture))
                (or (null? observed)
                    (set=? (normalized observed)
                           (normalized (cons (first observed) observed))))]
               [(every-operand-contributes)
                (subset? (normalized (contribution-fixture-required fixture))
                         (normalized (contribution-fixture-observed fixture)))]
               [else (error 'contribution-law-failures
                            "unknown contribution law: ~a" law)]))
    law))

(define fixtures
  (list
   (contribution-fixture 'blue-red 'color-regions
                         '(blue red) '(red blue) '(blue-region red-region))
   (contribution-fixture 'lion-tiger-origin 'origin
                         '(lion-origin tiger-origin)
                         '(tiger-origin lion-origin) '(hybrid-cell))
   (contribution-fixture 'desire-fear-aspects 'aspect
                         '(desire-aspect fear-aspect)
                         '(fear-aspect desire-aspect) '())
   (contribution-fixture 'missing-red 'color-regions
                         '(blue red) '(blue) '(blue-region))))

(define contribution-results
  (for/list ([fixture fixtures])
    (define failures (contribution-law-failures fixture profile))
    (make-result (contribution-fixture-name fixture) profile
                 (if (eq? (contribution-fixture-name fixture) 'missing-red)
                     'reject 'accept)
                 failures)))

(define (contribution-unknown-law-rejected?)
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (contribution-law-failures
     (first fixtures) (law-profile 'bad 'live-baseline '(nonsense)))
    #f))
