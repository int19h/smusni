#lang racket

(require racket/list
         racket/set
         "common.rkt")

(provide kernel-results
         covered-by?
         refinement-stable?
         kernel-law-failures
         kernel-unknown-law-rejected?
         kernel-bounded-search)

(struct kref (id units) #:transparent)
(struct kernel-fixture (name refs coref?) #:transparent)

(define (same-units? left right)
  (set=? (kref-units left) (kref-units right)))

(define (cj-holds? fixture)
  (for*/and ([left (kernel-fixture-refs fixture)]
             [right (kernel-fixture-refs fixture)])
    (or (not (same-units? left right))
        ((kernel-fixture-coref? fixture) left right))))

;; At an atomic count basis, CoveredBy reduces to every represented unit
;; satisfying the resolved unit predicate. The symbolic mass case is separate.
(define (covered-by? predicate reference)
  (and (not (set-empty? reference))
       (for/and ([unit (in-set reference)]) (predicate unit))))

(define baseline
  (law-profile 'baseline 'live-baseline '(aci among coref)))
(define baseline+cj
  (law-profile 'baseline+CJ 'comparative '(aci among coref CJ)))
(define count-profile
  (law-profile 'count-CoveredBy 'human-adopted-pending-sync '(CoveredBy)))

(define same-units-distinct
  (let ([left (kref 'left (set 'u1 'u2))]
        [right (kref 'right (set 'u1 'u2))])
    (kernel-fixture 'F-without-CJ (list left right)
                    (lambda (a b) (eq? (kref-id a) (kref-id b))))))

(define (aci-holds? fixture)
  (define refs (kernel-fixture-refs fixture))
  (for*/and ([a refs] [b refs] [c refs])
    (define ua (kref-units a))
    (define ub (kref-units b))
    (define uc (kref-units c))
    (and (set=? (set-union ua ub) (set-union ub ua))
         (set=? (set-union (set-union ua ub) uc)
                (set-union ua (set-union ub uc)))
         (set=? (set-union ua ua) ua))))

(define (among-holds? fixture)
  (define refs (kernel-fixture-refs fixture))
  (define (among? a b) (subset? (kref-units a) (kref-units b)))
  (and (for/and ([a refs]) (among? a a))
       (for*/and ([a refs] [b refs] [c refs])
         (or (not (and (among? a b) (among? b c))) (among? a c)))))

(define (coref-holds? fixture)
  (define refs (kernel-fixture-refs fixture))
  (define relation (kernel-fixture-coref? fixture))
  (and (for/and ([a refs]) (relation a a))
       (for*/and ([a refs] [b refs])
         (equal? (relation a b) (relation b a)))
       (for*/and ([a refs] [b refs] [c refs])
         (or (not (and (relation a b) (relation b c))) (relation a c)))))

(define (kernel-law-failures fixture profile)
  (for/list ([law (law-profile-laws profile)]
             #:unless
             (case law
               [(aci) (aci-holds? fixture)]
               [(among) (among-holds? fixture)]
               [(coref) (coref-holds? fixture)]
               [(CJ) (cj-holds? fixture)]
               [else (error 'kernel-law-failures "unknown kernel law: ~a" law)]))
    law))

(define dog? (lambda (unit) (member unit '(dog1 dog2))))

(define (refine-unit unit)
  (set (cons unit 'left) (cons unit 'right)))

(define (refine-reference reference)
  (for/fold ([refined (set)]) ([unit (in-set reference)])
    (set-union refined (refine-unit unit))))

(define (refined-predicate predicate)
  (lambda (part) (and (pair? part) (predicate (car part)))))

(define (refinement-stable? predicate reference)
  (equal? (covered-by? predicate reference)
          (covered-by? (refined-predicate predicate)
                       (refine-reference reference))))

(define kernel-results
  (append
   (list
    (make-result 'F-without-CJ baseline 'accept
                 (kernel-law-failures same-units-distinct baseline))
    (make-result 'F-without-CJ baseline+cj 'reject
                 (kernel-law-failures same-units-distinct baseline+cj)))
   (for/list ([case (list (cons 'dogs (set 'dog1 'dog2))
                          (cons 'dog-plus-cat (set 'dog1 'cat))
                          (cons 'dogs-plus-pack (set 'dog1 'dog2 'pack)))])
     (make-result (car case) count-profile
                  (if (eq? (car case) 'dogs) 'accept 'reject)
                  (if (covered-by? dog? (cdr case)) '() '(CoveredBy))))))

(define (kernel-unknown-law-rejected?)
  (with-handlers ([exn:fail? (lambda (_) #t)])
    (kernel-law-failures
     same-units-distinct (law-profile 'bad 'live-baseline '(nonsense)))
    #f))

;; Exhaust all two-reference unit assignments over two units. This is a real
;; bounded result about the stated signature, not an atomless claim.
(define (kernel-bounded-search)
  (define unit-sets
    (filter (lambda (s) (not (set-empty? s)))
            (for/list ([mask (in-range 4)])
              (for/set ([bit (in-range 2)] #:when (bitwise-bit-set? mask bit))
                (list-ref '(u1 u2) bit)))))
  (define checked 0)
  (define cj-counterexamples 0)
  (for* ([left unit-sets] [right unit-sets])
    (set! checked (add1 checked))
    (when (set=? left right) (set! cj-counterexamples (add1 cj-counterexamples))))
  (hash 'structures checked 'same-unit-pairs cj-counterexamples))
