#lang racket

(require racket/list
         racket/set
         "common.rkt")

(provide constitution-results constitution-bounded-search constitution-law-failures
         constitution-unknown-law-rejected?)

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
  (define per-situation
    (for/list ([s (whole-model-situations model)]) (covers-at model s group)))
  (define covers (append* per-situation))
  (and (andmap pair? per-situation)
       (for/and ([cover covers]) (set-coref? cover (first covers)))))

(define (law-R model)
  (for/and ([g (whole-model-groups model)]
            #:when ((whole-model-aggregate? model) g))
    (rigid-cover? model g)))

(define (law-E model)
  (define occurring-covers
    (remove-duplicates
     (append-map (lambda (covers) covers)
                 (hash-values (whole-model-covers model)))
     set-coref?))
  (for*/and ([situation (whole-model-situations model)]
             [cover occurring-covers])
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
  (law-profile 'canonical-aggregate 'human-adopted-pending-sync '(F R E A)))
(define unrestricted-profile
  (law-profile 'unrestricted-U 'rejected-alternative '(F U)))
(define biconditional-profile
  (law-profile 'rigid-cover-biconditional 'rejected-alternative
               '(F R E A biconditional)))
(define basis-profile
  (law-profile 'constitution-basis 'live-baseline
               '(operand-respect null-absorption)))
(define a-only-profile
  (law-profile 'canonical-A-negative 'human-adopted-pending-sync '(A)))
(define r-only-profile
  (law-profile 'canonical-R-negative 'human-adopted-pending-sync '(R)))
(define e-only-profile
  (law-profile 'canonical-E-negative 'human-adopted-pending-sync '(E)))

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
   'coincidence-then-divergence '(t1 t2) '(aggregate1 aggregate2 budget ethics)
   (lambda (g) (member g '(aggregate1 aggregate2)))
   (hash (cover-key 't1 'aggregate1) (list c1)
         (cover-key 't2 'aggregate1) (list c1)
         (cover-key 't1 'aggregate2) (list c2)
         (cover-key 't2 'aggregate2) (list c2)
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

(define a-violator
  (whole-model
   'two-aggregates-one-cover '(t1) '(a1 a2) (lambda (_) #t)
   (hash (cover-key 't1 'a1) (list c1)
         (cover-key 't1 'a2) (list c1)) '()))

(define r-violator
  (whole-model
   'aggregate-cover-diverges '(t1 t2) '(a) (lambda (_) #t)
   (hash (cover-key 't1 'a) (list c1)
         (cover-key 't2 'a) (list c2)) '()))

(define r-missing-cover
  (whole-model
   'aggregate-cover-missing '(t1 t2) '(a) (lambda (_) #t)
   (hash (cover-key 't1 'a) (list c1)) '()))

(define e-violator
  (whole-model
   'cover-without-aggregate '(t1) '(organization) (lambda (_) #f)
   (hash (cover-key 't1 'organization) (list c1)) '()))

(define (constitution-law-failures model profile)
  (for/list ([law (law-profile-laws profile)]
             #:unless
             (case law
               [(F) (law-F model)] [(U) (law-U model)] [(A) (law-A model)]
               [(R) (law-R model)] [(E) (law-E model)]
               [(biconditional) (law-biconditional model)]
               [else (error 'constitution-law-failures
                            "unknown constitution law: ~a" law)]))
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
                (constitution-law-failures f-violator live-profile))
   (make-result 'two-aggregates-one-cover a-only-profile 'reject
                (constitution-law-failures a-violator a-only-profile))
   (make-result 'aggregate-cover-diverges r-only-profile 'reject
                (constitution-law-failures r-violator r-only-profile))
   (make-result 'aggregate-cover-missing r-only-profile 'reject
                (constitution-law-failures r-missing-cover r-only-profile))
   (make-result 'cover-without-aggregate e-only-profile 'reject
                (constitution-law-failures e-violator e-only-profile))
   (make-result 'coincidence-then-divergence consensus-profile 'accept
                (constitution-law-failures coincidence consensus-profile))
   (make-result 'coincidence-then-divergence unrestricted-profile 'reject
                (constitution-law-failures coincidence unrestricted-profile))
   (make-result 'permanent-organizations consensus-profile 'accept
                (constitution-law-failures permanent consensus-profile))
   (make-result 'permanent-organizations biconditional-profile 'reject
                (constitution-law-failures permanent biconditional-profile))))

(define (constitution-unknown-law-rejected?)
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (constitution-law-failures
     coincidence (law-profile 'bad 'live-baseline '(nonsense)))
    #f))

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
