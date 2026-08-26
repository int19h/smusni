#lang racket

(require racket/set "common.rkt")

(provide contrast-results contrast-bounded-search)

(struct contrast-model
  (name universe cell complement opposite between opposite-back between-opposite)
  #:transparent)

(define profile
  (law-profile 'contrast-domain 'live-baseline
               '(cell complement opposite-outside between-outside separation
                      opposite-involution between-symmetry)))

(define (failures model)
  (define universe (contrast-model-universe model))
  (define cell (contrast-model-cell model))
  (define complement (contrast-model-complement model))
  (define opposite (contrast-model-opposite model))
  (define between (contrast-model-between model))
  (append
   (if (subset? cell universe) '() '(cell))
   (if (set=? complement (set-subtract universe cell)) '() '(complement))
   (if (subset? opposite complement) '() '(opposite-outside))
   (if (subset? between complement) '() '(between-outside))
   (if (set-empty? (set-intersect between opposite)) '() '(separation))
   (if (set=? (contrast-model-opposite-back model) cell)
       '() '(opposite-involution))
   (if (set=? (contrast-model-between-opposite model) between)
       '() '(between-symmetry))))

(define witness
  (contrast-model 'polar-witness (set 'p 'middle 'n) (set 'p)
                  (set 'middle 'n) (set 'n) (set 'middle)
                  (set 'p) (set 'middle)))
(define collapsed
  (contrast-model 'between-equals-opposite (set 'p 'middle 'n) (set 'p)
                  (set 'middle 'n) (set 'n) (set 'n)
                  (set 'p) (set 'n)))

(define contrast-results
  (list (make-result 'polar-witness profile 'accept (failures witness))
        (make-result 'between-equals-opposite profile 'reject (failures collapsed))))

(define (subsets values)
  (for/list ([mask (in-range (expt 2 (length values)))])
    (for/set ([value values] [bit (in-naturals)]
              #:when (bitwise-bit-set? mask bit)) value)))

(define (contrast-bounded-search)
  (define universe (set 'p 'middle 'n))
  (define candidates (subsets '(p middle n)))
  (define checked 0)
  (define satisfying 0)
  (for* ([cell candidates] [opposite candidates] [between candidates])
    (set! checked (add1 checked))
    (define model
      (contrast-model 'generated universe cell (set-subtract universe cell)
                      opposite between cell between))
    (when (null? (failures model)) (set! satisfying (add1 satisfying))))
  (hash 'structures checked 'law-satisfying satisfying))
