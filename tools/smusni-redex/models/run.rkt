#lang racket

(require racket/list
         racket/set
         "common.rkt"
         "contribution.rkt"
         "constitution.rkt"
         "contrast.rkt"
         "kernel.rkt"
         "symbolic.rkt")

(provide run-model-bank all-model-results)

(define all-model-results
  (append kernel-results constitution-results contribution-results contrast-results))

(define (run-model-bank)
  (define failed (filter (lambda (result) (not (result-ok? result)))
                         all-model-results))
  (for ([status '(live-baseline human-adopted-pending-sync reviewer-consensus
                                comparative rejected-alternative)])
    (define rows
      (filter (lambda (result)
                (eq? (law-profile-decision-status (model-result-profile result))
                     status))
              all-model-results))
    (unless (null? rows)
      (printf "model-profile ~a:\n" status)
      (for ([result rows])
        (printf "  ~a / ~a: ~a (expected ~a)~a\n"
                (model-result-model result)
                (law-profile-name (model-result-profile result))
                (model-result-verdict result)
                (model-result-expected result)
                (if (null? (model-result-failures result)) ""
                    (format " failures=~a" (model-result-failures result)))))))
  (printf "bounded kernel search: ~a\n" (kernel-bounded-search))
  (printf "count-fixture refinement stability: ~a\n"
          (and (refinement-stable? (lambda (x) (member x '(dog1 dog2)))
                                   (set 'dog1 'dog2))
               (refinement-stable? (lambda (x) (member x '(dog1 dog2)))
                                   (set 'dog1 'cat))))
  (printf "bounded constitution search: ~a\n" (constitution-bounded-search))
  (printf "bounded contrast search (cell/opposite/between varied; involution and symmetry fixed by construction): ~a\n"
          (contrast-bounded-search))
  (define symbolic-ok?
    (for/and ([interval (list (dyadic-interval 0 1)
                              (dyadic-interval 1/4 3/4)
                              (dyadic-interval -2 6))])
      (proper-refinement-witness? interval)))
  (define mass-covered?
    (mass-covered-by-witness? (dyadic-interval 0 1) (lambda (_) #t)))
  (define atomistic-distrib-available?
    (distrib-only-witness? '() (lambda (_) #t)))
  (printf "symbolic divisible mass witness: CoveredBy=~a Distrib-only-available=~a\n"
          mass-covered? atomistic-distrib-available?)
  (and (null? failed) mass-covered? (not atomistic-distrib-available?)))

(module+ main
  (exit (if (run-model-bank) 0 1)))
