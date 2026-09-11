#lang racket
(require rackunit "../lower.rkt" "../types.rkt" "../syntax.rkt")

;; E01-C01, constructed by Astra in the first E01 gate (2026-09-10).
;; The outer argument of P is unused; the joint telescope shadows it.
(define P '(λ ($x :: Entity)
             (∃ (λ (($x :: Entity) ($y :: Entity))
                  (∧ (gerku $x) (prenu $y))))))
(define Q '(λ ($z :: Entity) (= $z $z)))
(define counted (individual-count-condition '(at-least 2) P Q))
(check-equal?
 counted
 '(≤ 2 (Card (SetOf (λ ($individual :: Entity)
                     (∧ (∃ (λ (($x :: Entity) ($y :: Entity))
                              (∧ (gerku $x) (prenu $y))))
                        (= $individual $individual)))))))
(check-equal? (typing-type (infer-core (datum->core counted))) 'Content)

(for ([binder '((($x :: Entity) ($y :: Number))
                ($x $y :: Entity) (($x $y :: Entity)) ($x :: Entity))])
  (define term `(λ ,binder (pair $x $free)))
  (check-equal? (substitute-free-symbol term '$x '$replacement) term)
  (check-equal? (substitute-free-symbol term '$free '$replacement)
                `(λ ,binder (pair $x $replacement))))
(check-equal?
 (substitute-free-symbol '(Let ($x :: Entity) $x (pair $x $free)) '$x '$new)
 '(Let ($x :: Entity) $new (pair $x $free)))
(check-equal?
 (substitute-free-symbol
  '(Bind ($a :: Entity) (F $x) ($x :: Entity) (G $x)
         ($b :: Entity) (H $x) (pair $x $a)) '$x '$new)
 '(Bind ($a :: Entity) (F $new) ($x :: Entity) (G $new)
        ($b :: Entity) (H $x) (pair $x $a)))

;; Replacement names may themselves be bound below the substitution site.
;; Alpha-renaming must free the replacement while preserving the old binder.
(for ([term '((λ (($y :: Entity) ($z :: Number)) (pair $x $y))
              (Let ($y :: Entity) $x (pair $x $y))
              (Bind ($y :: Entity) (F $x) ($z :: Entity) (G $y)
                    (pair $x $y)))]
      [expected '((λ (($fresh :: Entity) ($z :: Number)) (pair $y $fresh))
                  (Let ($fresh :: Entity) $y (pair $y $fresh))
                  (Bind ($fresh :: Entity) (F $y) ($z :: Entity) (G $fresh)
                        (pair $y $fresh)))])
  (check-true (redex-alpha-equivalent?
               (substitute-free-symbol term '$x '$y) expected)))
(check-true
 (redex-alpha-equivalent?
  (substitute-free-symbol
   '(λ ($y :: Entity) (pair $x (λ ($y :: Entity) (pair $x $y)))) '$x '$y)
  '(λ ($outer :: Entity) (pair $y (λ ($inner :: Entity) (pair $y $inner))))))
(check-equal? (substitute-free-symbol '(pair "$x" $x) '$x '$new)
              '(pair "$x" $new))
(check-equal? (substitute-free-symbol P '$x '$x) P)

;; The same shared telescope parser now supplies retrieval-site scope IDs.
(define sites (site-signatures '(λ (($x :: Entity) ($y :: Number)) (Context $x $y))))
(check-equal? sites (site-signatures '(λ (($a :: Entity) ($b :: Number)) (Context $a $b))))

;; Astra's A1 clearance control (2026-09-10): alpha-invariance must not erase
;; which variable a site uses under a shared telescope.
(check-equal? (site-signatures '(λ (($x :: Entity) ($y :: Entity)) (Context $x)))
              '((site 1 Context (1))))
(check-equal? (site-signatures '(λ (($x :: Entity) ($y :: Entity)) (Context $y)))
              '((site 1 Context (2))))
