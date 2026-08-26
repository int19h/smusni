#lang racket

(provide (struct-out dyadic-interval)
         split-interval
         proper-refinement-witness?)

(struct dyadic-interval (lo hi) #:transparent)

(define (split-interval interval)
  (define lo (dyadic-interval-lo interval))
  (define hi (dyadic-interval-hi interval))
  (unless (< lo hi) (error 'split-interval "interval must be nonempty"))
  (define midpoint (/ (+ lo hi) 2))
  (values (dyadic-interval lo midpoint)
          (dyadic-interval midpoint hi)))

(define (proper-refinement-witness? interval)
  (define-values (left right) (split-interval interval))
  (and (= (dyadic-interval-lo left) (dyadic-interval-lo interval))
       (= (dyadic-interval-hi right) (dyadic-interval-hi interval))
       (= (dyadic-interval-hi left) (dyadic-interval-lo right))
       (< (dyadic-interval-lo left) (dyadic-interval-hi left))
       (< (dyadic-interval-lo right) (dyadic-interval-hi right))
       (< (- (dyadic-interval-hi left) (dyadic-interval-lo left))
          (- (dyadic-interval-hi interval) (dyadic-interval-lo interval)))
       (< (- (dyadic-interval-hi right) (dyadic-interval-lo right))
          (- (dyadic-interval-hi interval) (dyadic-interval-lo interval)))))

