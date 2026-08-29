#lang racket

(require rackunit
         redex/reduction-semantics
         "../port-a0.rkt")

(define (synth environment term)
  (define derivations
    (build-derivations (a0-synth ,environment ,term R)))
  (check-equal? (length derivations) 1
                (format "unique B1 synthesis derivation for ~s" term))
  (define results (judgment-holds (a0-synth ,environment ,term R) R))
  (check-equal? (length results) 1
                (format "unique B1 synthesis result for ~s" term))
  (and (= (length results) 1) (first results)))

(define (check-at environment term type)
  (define derivations
    (build-derivations (a0-check ,environment ,term ,type R)))
  (check-equal? (length derivations) 1
                (format "unique B1 checking derivation for ~s" term))
  (define results (judgment-holds (a0-check ,environment ,term ,type R) R))
  (check-equal? (length results) 1
                (format "unique B1 checking result for ~s" term))
  (and (= (length results) 1) (first results)))

(define (no-checking? environment term type)
  (and (null? (judgment-holds (a0-check ,environment ,term ,type R) R))
       (null? (build-derivations
               (a0-check ,environment ,term ,type R)))))

(define P '(λ (($x Entity)) ⊤))
(define Q-reference '(λ (($w (Referents Entity))) ⊤))
(define Q-member '(λ (($x Entity)) ⊤))

;; General definition equations, including capture-avoiding fresh binders.
(check-equal? (term (b1-expand-at-least 0 Entity P Q)) '⊤)
(check-true
 (alpha-equivalent?
  SmusniA0
  (term (b1-expand-at-least 2 Entity P Q))
  '(Bind (($w (Referents Entity) (SelectAtLeast 2 P))) (Q $w))))
(check-true
 (alpha-equivalent?
  SmusniA0
  (term (b1-expand-some Entity P Q))
  '(Bind (($w (Referents Entity) (SelectSome P))) (Q $w))))
(check-true
 (alpha-equivalent?
  SmusniA0
  (term (b1-expand-every Entity P Q))
  '(Bind (($w (Referents Entity) (MaxRefer P))) (Distrib Q $w))))
(check-equal? (term (b1-expand-no Entity P Q)) '(¬ (Some P Q)))
(check-equal?
 (term (b1-expand-at-most n Entity P Q))
 '(¬ (AtLeast (+ n 1) P Q)))
(check-equal?
 (term (b1-expand-more-than n Entity P Q))
 '(AtLeast (+ n 1) P Q))
(check-equal?
 (term (b1-expand-fewer-than n Entity P Q))
 '(¬ (AtLeast n P Q)))
(check-true
 (alpha-equivalent?
  SmusniA0
  (term (b1-expand-distrib Entity Q r))
  '(∀ (λ (($member Entity))
        (→ (Among $member r) (Q $member))))))
(check-true
 (alpha-equivalent?
  SmusniA0
  (term (b1-expand-overlap Entity a b))
  '(∃ (λ (($common (Referents Entity)))
        (∧ (Among $common a) (Among $common b))))))
(check-true
 (alpha-equivalent?
  SmusniA0
  (term (b1-expand-covered-by Entity P r))
  '(∧ (Distrib P r)
      (∀ (λ (($r2 (Referents Entity)))
           (→ (Among $r2 r)
              (∃ (λ (($x Entity))
                   (∧ (P $x) (Overlap $x $r2))))))))))
(check-equal?
 (term (b1-expand-select-some Entity P))
 '(SelectAtLeast 1 P))
(check-true
 (alpha-equivalent?
  SmusniA0
  (term (b1-expand-max-refer Entity P))
  '(Presuppose
    (∃ P)
    (Refer
     (λ (($r (Referents Entity)))
       (∧ (CoveredBy P $r)
          (∀ (λ (($x Entity))
               (→ (P $x) (Among $x $r))))))))))

(define gq-env
  (term ((P (Fn (Entity) Content))
         (Q (EFn ((Referents Entity)) Content)))))
(define every-env
  (term ((P (Fn (Entity) Content))
         (Q (EFn (Entity) Content)))))

;; Selection floor and complement-selection boundary.
(check-equal?
 (check-at '() (term (SelectAtLeast 1 ,P))
           (term (RefComp (Referents Entity))))
 '(typing (RefComp (Referents Entity)) (refer) ()))
(check-true
 (no-checking? '() (term (SelectAtLeast 0 ,P))
               (term (RefComp (Referents Entity)))))
(check-equal?
 (check-at '() (term (SelectAllBut 0 ,P))
           (term (RefComp (Referents Entity))))
 '(typing (RefComp (Referents Entity)) (refer) ()))
(check-equal?
 (check-at (term ((n Natural)))
           (term (SelectAtLeast (+ n 1) ,P))
           (term (RefComp (Referents Entity))))
 '(typing (RefComp (Referents Entity)) (refer) ()))
(check-equal?
 (check-at (term ((n Natural)))
           (term (SelectAtLeast (+ 1 n) ,P))
           (term (RefComp (Referents Entity))))
 '(typing (RefComp (Referents Entity)) (refer) ()))
(check-true
 (no-checking? (term ((n Natural)))
               (term (SelectAtLeast n ,P))
               (term (RefComp (Referents Entity)))))
(check-equal? (synth (term ((n Natural))) (term (+ n 1)))
              '(typing Natural () ()))
(check-equal?
 (synth (term ((c Cardinal))) (term (+ c c)))
 '(typing Cardinal () ()))
(check-equal?
 (synth (term ((c Cardinal) (n Natural))) (term (+ c n)))
 '(typing Natural () ()))
(check-equal?
 (synth (term ((n Natural) (z Number))) (term (+ n z)))
 '(typing Number () ()))

;; Direct GQ effect/export signatures.
(check-equal? (synth gq-env (term (AtLeast 0 P Q)))
              '(typing Content () ()))
(check-equal? (synth gq-env (term (AtLeast 2 P Q)))
              '(typing Content (effectful-call refer) ()))
(check-equal?
 (synth (term ((n Natural)
                (P (Fn (Entity) Content))
                (Q (EFn ((Referents Entity)) Content))))
        (term (AtLeast n P Q)))
 '(typing Content (effectful-call refer) ()))
(check-exn exn:fail?
           (lambda () (term (b1-expand-at-least n Entity P Q))))
(check-equal? (synth gq-env (term (Some P Q)))
              '(typing Content (effectful-call refer) ()))
(check-equal? (synth gq-env (term (No P Q)))
              '(typing Content (effectful-call) ()))
(check-equal? (synth gq-env (term (FewerThan 0 P Q)))
              '(typing Content () ()))
(check-equal? (synth gq-env (term (FewerThan 2 P Q)))
              '(typing Content (effectful-call) ()))
(check-equal?
 (synth (term ((n Natural)
                (P (Fn (Entity) Content))
                (Q (EFn ((Referents Entity)) Content))))
        (term (FewerThan n P Q)))
 '(typing Content (effectful-call) ()))
(check-equal?
 (synth (term ((n Natural)
                (P (Fn (Entity) Content))
                (Q (EFn ((Referents Entity)) Content))))
        (term (MoreThan n P Q)))
 '(typing Content (effectful-call refer) ()))
(check-equal?
 (synth (term ((n Natural)
                (P (Fn (Entity) Content))
                (Q (EFn ((Referents Entity)) Content))))
        (term (AtMost n P Q)))
 '(typing Content (effectful-call) ()))
(check-equal?
 (synth every-env (term (Every P Q)))
 '(typing Content (effectful-call projective refer)
          ((presuppose (∃ P) (RefComp (Referents Entity))))))

;; Generic negation masks only escaping refer and retains other effects and
;; obligations. Presuppose conditions are canonicalized modulo alpha.
(check-equal? (synth gq-env (term (¬ (Some P Q))))
              '(typing Content (effectful-call) ()))
(check-equal?
 (term
  (negate-record
   (typing Content
           (refer context projective effectful-call performance)
           (finite-set-cardinality-defined))))
 '(typing Content
          (context effectful-call performance projective)
          (finite-set-cardinality-defined)))
(check-equal?
 (synth gq-env (term (Presuppose (Some P Q) ⊤)))
 '(typing Content (effectful-call projective)
          ((presuppose (Some P Q) Content))))
(define alpha-left
  (synth '()
         (term
          (Presuppose
           (∃ (λ (($x Entity)) (Among $x Speaker)))
           ⊤))))
(define alpha-right
  (synth '()
         (term
          (Presuppose
           (∃ (λ (($y Entity)) (Among $y Speaker)))
           ⊤))))
(check-equal? alpha-left alpha-right)
(check-equal?
 alpha-left
 '(typing Content (projective)
          ((presuppose
            (∃ (λ (($alpha0 Entity)) (Among $alpha0 Speaker)))
            Content))))

;; Expected-only Presuppose formation stays exclusive from Check-Synth even
;; through arbitrarily nested wrappers.  The ultimate synthable variable uses
;; Check-Synth only; the ultimate Context uses the direct expected-mode rule.
(check-equal?
 (check-at (term (($r (RefComp Entity))))
           (term (Presuppose ⊤ (Presuppose ⊤ $r)))
           (term (RefComp Entity)))
 '(typing (RefComp Entity) (projective)
          ((presuppose ⊤ (RefComp Entity)))))
(check-equal?
 (check-at '()
           (term (Presuppose ⊤ (Presuppose ⊤ (Context))))
           (term (RefComp (Referents Entity))))
 '(typing (RefComp (Referents Entity)) (context projective)
          ((presuppose ⊤ (RefComp (Referents Entity))))))

;; Conditions can depend on an enclosing binder.  Canonicalization happens as
;; the derivation exits λ, Let, and Bind, so alpha variants have identical
;; complete records without rewriting genuinely free variables.
(define enclosing-lambda-left
  (synth '()
         (term
          (λ (($x Entity))
            (Presuppose (= $x $x) ⊤)))))
(define enclosing-lambda-right
  (synth '()
         (term
          (λ (($y Entity))
            (Presuppose (= $y $y) ⊤)))))
(check-equal? enclosing-lambda-left enclosing-lambda-right)
(check-equal?
 enclosing-lambda-left
 '(typing (EFn (Entity) Content) ()
          ((presuppose (= $alpha0 $alpha0) Content))))
(check-equal?
 (synth (term (($free Entity)))
        (term
         (λ (($renamed Entity))
           (Presuppose (= $renamed $free) ⊤))))
 '(typing (EFn (Entity) Content) ()
          ((presuppose (= $alpha0 $free) Content))))

(define enclosing-let-left
  (synth (term (($value Entity)))
         (term
          (Let ($x Entity) $value
            (Presuppose (= $x $x) ⊤)))))
(define enclosing-let-right
  (synth (term (($value Entity)))
         (term
          (Let ($y Entity) $value
            (Presuppose (= $y $y) ⊤)))))
(check-equal? enclosing-let-left enclosing-let-right)
(check-equal?
 enclosing-let-left
 '(typing Content (projective)
          ((presuppose (= $alpha0 $alpha0) Content))))

(define enclosing-bind-left
  (synth '()
         (term
          (Bind (($x (Referents Entity) (Context)))
            (Presuppose (Among $x $x) ⊤)))))
(define enclosing-bind-right
  (synth '()
         (term
          (Bind (($y (Referents Entity) (Context)))
            (Presuppose (Among $y $y) ⊤)))))
(check-equal? enclosing-bind-left enclosing-bind-right)
(check-equal?
 enclosing-bind-left
 '(typing Content (context projective)
          ((presuppose (Among $alpha0 $alpha0) Content))))

;; A symbolic count may instantiate to the obligation-free zero branch.  Its
;; positive-branch effects remain the authorized static upper bound, while P/Q
;; obligations are represented explicitly as conditional on positivity.
(define Q-projective
  '(λ (($w (Referents Entity))) (Presuppose ⊤ ⊤)))
(check-equal?
 (synth (term ((n Natural)))
        (term (AtLeast n ,P ,Q-projective)))
 '(typing Content (effectful-call refer)
          ((when-positive n (presuppose ⊤ Content)))))
(check-equal?
 (synth '() (term (AtLeast 0 ,P ,Q-projective)))
 '(typing Content () ()))
(check-equal?
 (synth (term ((n Natural)))
        (term (FewerThan n ,P ,Q-projective)))
 '(typing Content (effectful-call)
          ((when-positive n (presuppose ⊤ Content)))))
(check-equal?
 (synth '() (term (FewerThan 0 ,P ,Q-projective)))
 '(typing Content () ()))
(define guarded-binder-left
  (synth '()
         (term
          (λ (($n Natural))
            (AtLeast
             $n ,P
             (λ (($w (Referents Entity)))
               (Presuppose (= $n $n) ⊤)))))))
(define guarded-binder-right
  (synth '()
         (term
          (λ (($m Natural))
            (AtLeast
             $m ,P
             (λ (($w (Referents Entity)))
               (Presuppose (= $m $m) ⊤)))))))
(check-equal? guarded-binder-left guarded-binder-right)
(check-equal?
 guarded-binder-left
 '(typing (EFn (Natural) Content) ()
          ((when-positive
            $alpha0
            (presuppose (= $alpha0 $alpha0) Content)))))
(check-equal?
 (synth '()
        (term
         (¬ (Presuppose
             ⊤
             (Bind (($r (Referents Entity) (Context))) ⊤)))))
 '(typing Content (context projective)
          ((presuppose ⊤ Content))))

;; Direct terms and their definitions preserve the complete record.
(define (check-preserved environment source expanded)
  (check-equal? (synth environment source)
                (synth environment expanded)))

(check-preserved gq-env
                 (term (AtLeast 0 P Q))
                 (term (b1-expand-at-least 0 Entity P Q)))
(check-preserved gq-env
                 (term (AtLeast 2 P Q))
                 (term (b1-expand-at-least 2 Entity P Q)))
(check-preserved
 (term ((n Natural)
        (P (Fn (Entity) Content))
        (Q (EFn ((Referents Entity)) Content))))
 (term (AtLeast (+ n 1) P Q))
 (term (b1-expand-at-least (+ n 1) Entity P Q)))
(check-preserved gq-env
                 (term (Some P Q))
                 (term (b1-expand-some Entity P Q)))
(check-preserved gq-env
                 (term (No P Q))
                 (term (b1-expand-no Entity P Q)))
(check-preserved
 (term ((n Natural)
        (P (Fn (Entity) Content))
        (Q (EFn ((Referents Entity)) Content))))
 (term (AtMost n P Q))
 (term (b1-expand-at-most n Entity P Q)))
(check-preserved
 (term ((n Natural)
        (P (Fn (Entity) Content))
        (Q (EFn ((Referents Entity)) Content))))
 (term (MoreThan n P Q))
 (term (b1-expand-more-than n Entity P Q)))
(check-preserved gq-env
                 (term (FewerThan 0 P Q))
                 (term (b1-expand-fewer-than 0 Entity P Q)))
(check-preserved gq-env
                 (term (FewerThan 2 P Q))
                 (term (b1-expand-fewer-than 2 Entity P Q)))
(check-preserved every-env
                 (term (Every P Q))
                 (term (b1-expand-every Entity P Q)))

(define reference-env (term ((r (Referents Entity)))))
(check-preserved
 (term ((Q (EFn (Entity) Content)) (r (Referents Entity))))
 (term (Distrib Q r))
 (term (b1-expand-distrib Entity Q r)))
(check-preserved
 reference-env
 (term (Overlap Speaker r))
 (term (b1-expand-overlap Entity Speaker r)))
(check-preserved
 (term ((P (Fn (Entity) Content)) (r (Referents Entity))))
 (term (CoveredBy P r))
 (term (b1-expand-covered-by Entity P r)))
(check-equal?
 (check-at '() (term (SelectSome ,P))
           (term (RefComp (Referents Entity))))
 (check-at '() (term (b1-expand-select-some Entity ,P))
           (term (RefComp (Referents Entity)))))

(check-equal?
 (check-at (term ((P (Fn (Entity) Content))))
           (term (MaxRefer P))
           (term (RefComp (Referents Entity))))
 '(typing (RefComp (Referents Entity)) (projective refer)
          ((presuppose (∃ P) (RefComp (Referents Entity))))))
(check-equal?
 (check-at (term ((P (Fn (Entity) Content))))
           (term (b1-expand-max-refer Entity P))
           (term (RefComp (Referents Entity))))
 (check-at (term ((P (Fn (Entity) Content))))
           (term (MaxRefer P))
           (term (RefComp (Referents Entity)))))

(displayln "B1 quantifier/selection family: ok")
