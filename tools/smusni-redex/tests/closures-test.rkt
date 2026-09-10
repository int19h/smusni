#lang racket

(require rackunit racket/set redex/reduction-semantics
         "../port-a0.rkt" "../syntax.rkt" "../types.rkt")

(define (synth env datum)
  (define records (judgment-holds (a0-synth ,env ,datum R) R))
  (check-equal? (length (build-derivations (a0-synth ,env ,datum R))) 1)
  (check-equal? (length records) 1)
  (first records))

;; Unseen parameters and domain types must work through the same equations.
(for* ([domain '(Entity Eventuality Number)]
       [effectful? '(#f #t)]
       [head '(IndividualSome IndividualNo IndividualEvery PluralSome PluralNo)])
  (define plural? (member head '(PluralSome PluralNo)))
  (define parameter (if plural? `(Referents ,domain) domain))
  (define arrow (if effectful? 'EFn 'Fn))
  (define env `(($x (Fn (,parameter) Content)) ($r (,arrow (,parameter) Content))))
  (define input `(,head $x $r))
  (define expanded
    (case head
      [(IndividualSome) (term (e01-expand-individual-some ,domain $x $r))]
      [(IndividualNo) (term (e01-expand-individual-no ,domain $x $r))]
      [(IndividualEvery) (term (e01-expand-individual-every ,domain $x $r))]
      [(PluralSome) (term (e01-expand-plural-some ,domain $x $r))]
      [(PluralNo) (term (e01-expand-plural-no ,domain $x $r))]))
  (define result (synth env input))
  (check-equal? result `(typing Content ,(if effectful? '(effectful-call) '()) ()))
  (check-equal? (synth env expanded) result)
  (define legacy
    (infer-core (read-core-specimen (format "~s" input))
                (make-immutable-hash (map (lambda (p) (cons (first p) (second p))) env))))
  (check-equal? (typing-type legacy) 'Content)
  (check-equal? (typing-effects legacy) (list->set (third result))))

;; Purity, referential carrier, and compatible domain are real gates.
(for ([head '(IndividualSome IndividualNo IndividualEvery PluralSome PluralNo)])
  (check-equal?
   (judgment-holds
    (a0-synth ((P (EFn (Entity) Content)) (Q (Fn (Entity) Content)))
              (,head P Q) R) R) '()))
(for ([head '(PluralSome PluralNo)])
  (check-equal?
   (judgment-holds
    (a0-synth ((P (Fn (Entity) Content)) (Q (Fn (Entity) Content)))
              (,head P Q) R) R) '()))
(for ([head '(IndividualSome IndividualNo IndividualEvery)])
  (check-equal?
   (judgment-holds
    (a0-synth ((P (Fn ((Referents Entity)) Content))
               (Q (Fn ((Referents Entity)) Content)))
              (,head P Q) R) R) '()))
(check-equal?
 (judgment-holds
  (a0-synth ((P (Fn (Entity) Content)) (Q (Fn (Number) Content)))
            (IndividualSome P Q) R) R) '())
(check-equal?
 (synth '((P (Fn (Eventuality) Content)) (Q (Fn (Entity) Content)))
        '(IndividualEvery P Q))
 '(typing Content () ()))

(define only-env '((A (Fn ((Referents Entity)) Content))
                   (H (Fn ((Referents Entity)) Content))))
(check-equal? (synth only-env '(Only A H Speaker)) '(typing Content () ()))
(check-equal? (synth only-env (term (e01-expand-only Entity A H Speaker)))
              '(typing Content () ()))
(check-equal?
 (judgment-holds
  (a0-synth ((A (Fn ((Referents Entity)) Content))
             (H (EFn ((Referents Entity)) Content)))
            (Only A H Speaker) R) R) '())
(check-equal?
 (term (e01-expand-only Entity A H Speaker))
 '(∧ (H Speaker)
     (∀ (λ (($alternative (Referents Entity)))
          (→ (∧ (A $alternative) (H $alternative))
             (Among $alternative Speaker))))))
