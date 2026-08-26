#lang racket

(require racket/list
         racket/set
         "common.rkt")

(provide constitution-results constitution-bounded-search)

(struct whole-model (name situations groups aggregate? covers required) #:transparent)
(struct basis-fixture (name operand-units combined-units peer-units null-unit)
  #:transparent)

(define (cover-key situation group) (cons situation group))
(define (covers-at model situation group)
  (hash-ref (whole-model-covers model) (cover-key situation group) '()))

(define (law-F model)
  (for*/and ([s (whole-model-situations model)]
             [g (whole-model-groups model)])
    (define covers (covers-at model s g))
    (or (null? covers)
        (for*/and ([left covers] [right covers]) (set-coref? left right)))))

(define (law-U model)
  (for*/and ([s (whole-model-situations model)]
             [g1 (whole-model-groups model)] [g2 (whole-model-groups model)]
             #:when (not (eq? g1 g2)))
    (for*/and ([c1 (covers-at model s g1)] [c2 (covers-at model s g2)])
      (not (set-coref? c1 c2)))))

(define (law-A model)
  (for*/and ([s (whole-model-situations model)]
             [g1 (whole-model-groups model)] [g2 (whole-model-groups model)]
             #:when (and (not (eq? g1 g2))
                         ((whole-model-aggregate? model) g1)
                         ((whole-model-aggregate? model) g2)))
    (for*/and ([c1 (covers-at model s g1)] [c2 (covers-at model s g2)])
      (not (set-coref? c1 c2)))))

(define (rigid-cover? model group)
  (define covers
    (append-map (lambda (s) (covers-at model s group))
                (whole-model-situations model)))
  (and (pair? covers)
       (for/and ([cover covers]) (set-coref? cover (first covers)))))

(define (law-R model)
  (for/and ([g (whole-model-groups model)]
            #:when ((whole-model-aggregate? model) g))
    (rigid-cover? model g)))

(define (law-E model)
  (for/and ([required (whole-model-required model)])
    (match-define (list situation cover) required)
    (for/or ([g (whole-model-groups model)])
      (and ((whole-model-aggregate? model) g)
           (for/or ([actual (covers-at model situation g)])
             (set-coref? actual cover))))))

(define (law-biconditional model)
  (for/and ([g (whole-model-groups model)])
    (equal? ((whole-model-aggregate? model) g) (rigid-cover? model g))))

(define live-profile
  (law-profile 'constitution-live 'live-baseline '(F)))
(define consensus-profile
  (law-profile 'canonical-aggregate 'reviewer-consensus '(F R E A)))
(define unrestricted-profile
  (law-profile 'unrestricted-U 'rejected-alternative '(F U)))
(define biconditional-profile
  (law-profile 'rigid-cover-biconditional 'rejected-alternative
               '(F R E A biconditional)))
(define basis-profile
  (law-profile 'constitution-basis 'live-baseline
               '(operand-respect null-absorption)))

(define (basis-failures fixture)
  (append
   (if (for/and ([operand (basis-fixture-operand-units fixture)])
         (subset? operand (basis-fixture-combined-units fixture)))
       '() '(operand-respect))
   (if (set-member? (basis-fixture-peer-units fixture)
                    (basis-fixture-null-unit fixture))
       '(null-absorption) '())))

(define maximal-phase-merge
  (basis-fixture 'maximal-phase-merge
                 (list (set 'phase-a) (set 'phase-b))
                 (set 'merged-phase) (set 'merged-phase) 'hold-top))
(define null-as-peer
  (basis-fixture 'hold-top-as-peer (list (set 'event)) (set 'event)
                 (set 'event 'hold-top) 'hold-top))
(define absorbable-null
  (basis-fixture 'hold-top-absorbable (list (set 'event)) (set 'event)
                 (set 'event) 'hold-top))

(define c1 (set 'a 'b 'c))
(define c2 (set 'd 'b 'c))

(define coincidence
  (whole-model
   'coincidence-then-divergence '(t1 t2) '(aggregate budget ethics)
   (lambda (g) (eq? g 'aggregate))
   (hash (cover-key 't1 'aggregate) (list c1)
         (cover-key 't2 'aggregate) (list c1)
         (cover-key 't1 'budget) (list c1)
         (cover-key 't2 'budget) (list c1)
         (cover-key 't1 'ethics) (list c1)
         (cover-key 't2 'ethics) (list c2))
   (list (list 't1 c1))))

(define permanent
  (whole-model
   'permanent-organizations '(t1 t2) '(aggregate foundation1 foundation2)
   (lambda (g) (eq? g 'aggregate))
   (for*/hash ([s '(t1 t2)] [g '(aggregate foundation1 foundation2)])
     (values (cover-key s g) (list c1)))
   (list (list 't1 c1))))

(define f-violator
  (whole-model
   'one-group-two-covers '(t1) '(g) (lambda (_) #f)
   (hash (cover-key 't1 'g) (list c1 c2)) '()))

(define (failures model profile)
  (for/list ([law (law-profile-laws profile)]
             #:unless
             (case law
               [(F) (law-F model)] [(U) (law-U model)] [(A) (law-A model)]
               [(R) (law-R model)] [(E) (law-E model)]
               [(biconditional) (law-biconditional model)]
               [else #t]))
    law))

(define constitution-results
  (list
   (make-result 'maximal-phase-merge basis-profile 'reject
                (basis-failures maximal-phase-merge))
   (make-result 'hold-top-as-peer basis-profile 'reject
                (basis-failures null-as-peer))
   (make-result 'hold-top-absorbable basis-profile 'accept
                (basis-failures absorbable-null))
   (make-result 'one-group-two-covers live-profile 'reject
                (failures f-violator live-profile))
   (make-result 'coincidence-then-divergence consensus-profile 'accept
                (failures coincidence consensus-profile))
   (make-result 'coincidence-then-divergence unrestricted-profile 'reject
                (failures coincidence unrestricted-profile))
   (make-result 'permanent-organizations consensus-profile 'accept
                (failures permanent consensus-profile))
   (make-result 'permanent-organizations biconditional-profile 'reject
                (failures permanent biconditional-profile))))

;; Enumerate the 16 two-group/two-situation choices between c1 and c2 and
;; report exactly how often F/U hold. Group identity remains intensional.
(define (constitution-bounded-search)
  (define assignments 0)
  (define u-models 0)
  (for* ([b1 (list c1 c2)] [b2 (list c1 c2)]
         [e1 (list c1 c2)] [e2 (list c1 c2)])
    (set! assignments (add1 assignments))
    (define model
      (whole-model 'generated '(t1 t2) '(b e) (lambda (_) #f)
                   (hash (cover-key 't1 'b) (list b1)
                         (cover-key 't2 'b) (list b2)
                         (cover-key 't1 'e) (list e1)
                         (cover-key 't2 'e) (list e2)) '()))
    (when (law-U model) (set! u-models (add1 u-models))))
  (hash 'structures assignments 'unrestricted-U-models u-models))
