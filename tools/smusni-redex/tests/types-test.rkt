#lang racket

(require rackunit
         racket/set
         redex/reduction-semantics
         "../syntax.rkt"
         "../types.rkt")

(define (infer-text text)
  (infer-core (read-core-specimen text 'types-test)))

(define (type-error? thunk)
  (with-handlers ([exn:fail:smusni? (lambda (_) #t)])
    (thunk)
    #f))

(define (type-error-matches? pattern thunk)
  (with-handlers ([exn:fail:smusni?
                   (lambda (error) (regexp-match? pattern (exn-message error)))])
    (thunk)
    #f))

(define pure-entity-restrictor
  "{λ [$x :: Entity] (gerku $x)}")

(define effectful-entity-restrictor
  "{λ [$x :: Entity]
      {Bind [$s :: Scale] (Context) (gerku $x)}}")

(define pure-member-nuclear
  "{λ [$x :: Entity] (Close (jmaji $x))}")

(define pure-reference-nuclear
  "{λ [$w :: Referents Entity] (Close (jmaji $w))}")

(define effectful-reference-nuclear
  "{λ [$w :: Referents Entity]
      {Bind [$s :: Scale] (Context) (Close (jmaji $w))}}")

(define effectful-member-nuclear
  "{λ [$x :: Entity]
      {Bind [$s :: Scale] (Context) (Close (jmaji $x))}}")

(define (check-l0.1-rejection text)
  (check-true
   (type-error-matches? #rx"L0[.]1" (lambda () (infer-text text)))))

(check-true (judgment-holds (type-compatible Natural Number)))
(check-true
 (judgment-holds
  (type-compatible (Fn ((Referents Eventuality)) Content) ClauseContent)))
(check-false (judgment-holds (type-compatible ClauseContent Content)))

(check-equal?
 (typing-type
  (infer-text
   "{λ [$f :: Fn ((Referents Entity) (Referents Entity)) Content]
       ($f Speaker Audience)}"))
 '(Fn ((Fn ((Referents Entity) (Referents Entity)) Content)) Content))

(check-equal?
 (typing-type
  (infer-text "{λ [$f :: Fn () Content] ($f)}"))
 '(Fn ((Fn () Content)) Content))

(check-equal?
 (typing-type
  (infer-text
   "{λ [$c :: EFn ((Referents Eventuality)) Content] (CloseClause $c)}"))
 '(Fn ((EFn ((Referents Eventuality)) Content)) Content))

(check-true
 (type-error?
  (lambda () (infer-text "{λ [$f :: Fn Entity Content] ($f Speaker)}"))))

(check-true
 (type-error?
  (lambda ()
    (infer-text "(gerku Speaker Audience This That)"))))

(define partial-explicit-event
  (infer-text
   "{λ [$e :: Referents Eventuality]
       (Close (klama Speaker :Eventuality $e))}"))
(check-equal? (first (typing-type partial-explicit-event)) 'EFn)

(define full-explicit-event
  (infer-text
   "{λ [$e :: Referents Eventuality]
       (Close (klama Speaker This That Yonder Audience :Eventuality $e))}"))
(check-equal? (first (typing-type full-explicit-event)) 'Fn)

(check-true
 (type-error?
  (lambda ()
    (infer-text
     "(SetOf {λ [$x :: Entity]
        {Bind [$n :: Natural] (Vague P) (gerku $x)}})"))))

(check-true
 (type-error?
  (lambda ()
    (infer-text
     "{λ [$f :: EFn ((Referents Entity)) Content]
        (SetOf {λ [$x :: Entity] ($f $x)})}"))))

;; #9 M2 gate 3b: every pure position accepts a pure property and rejects an
;; effectful one with the L0.1 hoisting diagnostic.
(check-not-exn
 (lambda () (infer-text (format "(SetOf ~a)" pure-entity-restrictor))))
(check-l0.1-rejection
 (format "(SetOf ~a)" effectful-entity-restrictor))

;; The gate is effect-class complete, not just a Context-site spelling check.
(for ([restrictor
       (in-list
        (list
         "{λ [$x :: Entity]
             {Bind [$n :: Natural] (Vague) (gerku $x)}}"
         "{λ [$x :: Entity]
             {Bind [$r :: Referents Entity]
                   (Refer {λ [$y :: Entity] (gerku $y)})
               (gerku $x)}}"
         "{λ [$x :: Entity]
             {Bind [$r :: Referents Entity]
                   (SelectSome {λ [$y :: Entity] (gerku $y)})
               (gerku $x)}}"
         "{λ [$x :: Entity]
             (Presuppose (gerku $x) (gerku $x))}"))])
  (check-l0.1-rejection (format "(SetOf ~a)" restrictor)))

(for ([head (in-list '(SelectExactly SelectAtLeast SelectSome SelectAllBut))])
  (define counted? (not (eq? head 'SelectSome)))
  (define (selection restrictor)
    (if counted?
        (format "(~a 1 ~a)" head restrictor)
        (format "(~a ~a)" head restrictor)))
  (check-not-exn
   (lambda ()
     (infer-text
      (format "{Bind [$w :: Referents Entity] ~a (Mention $w)}"
              (selection pure-entity-restrictor)))))
  (check-l0.1-rejection
   (format "{Bind [$w :: Referents Entity] ~a (Mention $w)}"
           (selection effectful-entity-restrictor))))

(check-not-exn
 (lambda ()
   (infer-text
    (format "(Generic Typical ~a ~a)"
            pure-entity-restrictor effectful-member-nuclear))))
(check-l0.1-rejection
 (format "(Generic Typical ~a ~a)"
         effectful-entity-restrictor pure-member-nuclear))

(define counted-witness-gqs '(Exactly AtLeast MoreThan AtMost FewerThan))
(define uncounted-witness-gqs '(Some No))

(for ([head (in-list counted-witness-gqs)])
  (check-not-exn
   (lambda ()
     (infer-text
      (format "(~a 1 ~a ~a)"
              head pure-entity-restrictor effectful-reference-nuclear))))
  (check-l0.1-rejection
   (format "(~a 1 ~a ~a)"
           head effectful-entity-restrictor pure-reference-nuclear)))

(for ([head (in-list uncounted-witness-gqs)])
  (check-not-exn
   (lambda ()
     (infer-text
      (format "(~a ~a ~a)"
              head pure-entity-restrictor effectful-reference-nuclear))))
  (check-l0.1-rejection
   (format "(~a ~a ~a)"
           head effectful-entity-restrictor pure-reference-nuclear)))

;; ClauseContent is the transparent EFn<Referents<Eventuality>, Content>
;; alias and remains usable as an event-witness nuclear scope.
(check-not-exn
 (lambda ()
   (infer-text
    "{λ [[$p :: Fn (Eventuality) Content] [$c :: ClauseContent]]
       (Exactly 1 $p $c)}")))

;; Every is the member-level exception among the cardinal/logical GQs.
(check-not-exn
 (lambda ()
   (infer-text
    "(Every {λ [$x :: Entity] (datka $x)}
       {λ [$duck :: Entity]
         (CloseClause (CapableClause (DirectClause (flulimna $duck))))})")))
(check-true
 (type-error?
  (lambda ()
    (infer-text
     (format "(Every ~a ~a)"
             pure-entity-restrictor pure-reference-nuclear)))))
(check-l0.1-rejection
 (format "(Every ~a ~a)"
         effectful-entity-restrictor pure-member-nuclear))

;; GlobalExactly and Most put both operands inside SetOf.
(for ([text (in-list
             (list (format "(GlobalExactly 1 ~a ~a)"
                           pure-entity-restrictor pure-member-nuclear)
                   (format "(Most ~a ~a)"
                           pure-entity-restrictor pure-member-nuclear)))])
  (check-not-exn (lambda () (infer-text text))))

(for ([text (in-list
             (list (format "(GlobalExactly 1 ~a ~a)"
                           effectful-entity-restrictor pure-member-nuclear)
                   (format "(GlobalExactly 1 ~a ~a)"
                           pure-entity-restrictor effectful-member-nuclear)
                   (format "(Most ~a ~a)"
                           effectful-entity-restrictor pure-member-nuclear)
                   (format "(Most ~a ~a)"
                           pure-entity-restrictor effectful-member-nuclear)))])
  (check-l0.1-rejection text))

;; Defined GQ results retain the effects of their §12 expansions. Exporting
;; forms introduce a witness, except for the two literal-zero boundaries.
(for ([content
       (in-list
        (list (format "(Exactly 1 ~a ~a)"
                      pure-entity-restrictor pure-reference-nuclear)
              (format "(AtLeast 1 ~a ~a)"
                      pure-entity-restrictor pure-reference-nuclear)
              (format "(Some ~a ~a)"
                      pure-entity-restrictor pure-reference-nuclear)
              (format "(MoreThan 0 ~a ~a)"
                      pure-entity-restrictor pure-reference-nuclear)
              (format "(Every ~a ~a)"
                      pure-entity-restrictor pure-member-nuclear)))])
  (check-l0.1-rejection
   (format "(SetOf {λ [$z :: Entity] ~a})" content)))

(for ([content
       (in-list
        (list (format "(No ~a ~a)"
                      pure-entity-restrictor pure-reference-nuclear)
              (format "(AtMost 1 ~a ~a)"
                      pure-entity-restrictor pure-reference-nuclear)
              (format "(FewerThan 1 ~a ~a)"
                      pure-entity-restrictor pure-reference-nuclear)
              (format "(AtLeast 0 ~a ~a)"
                      pure-entity-restrictor pure-reference-nuclear)
              (format "(Exactly 0 ~a ~a)"
                      pure-entity-restrictor pure-reference-nuclear)))])
  (check-not-exn
   (lambda ()
     (infer-text (format "(SetOf {λ [$z :: Entity] ~a})" content)))))

;; Card's finite-set definedness projects, including through the two §12
;; comparison forms that are defined with Card.
(for ([content
       (in-list
        (list (format "(GlobalExactly 1 ~a ~a)"
                      pure-entity-restrictor pure-member-nuclear)
              (format "(Most ~a ~a)"
                      pure-entity-restrictor pure-member-nuclear)))])
  (check-l0.1-rejection
   (format "(SetOf {λ [$z :: Entity] ~a})" content)))

(define standalone-some
  (infer-text
   (format "(Some ~a ~a)"
           pure-entity-restrictor pure-reference-nuclear)))
(check-true (set-member? (typing-effects standalone-some) 'refer))

(define finite-card
  (infer-text (format "(Card (SetOf ~a))" pure-entity-restrictor)))
(check-equal? (typing-type finite-card) 'Cardinal)
(check-true (set-member? (typing-effects finite-card) 'projective))
(check-not-false
 (member 'finite-set-cardinality-defined (typing-obligations finite-card)))

(check-not-exn
 (lambda ()
   (infer-text
    "{λ [[$c :: ClauseContent] [$e :: Referents Eventuality]] ($c $e)}")))

(check-equal?
 (typing-type
  (infer-text
   "{λ [$r :: PredTerm
                (Row (1 (Referents Entity)) (2 (Referents Entity)))]
       ($r Speaker Audience)}"))
 '(Fn ((PredTerm (Row (1 (Referents Entity)) (2 (Referents Entity)))))
      Content))

(check-true
 (type-error?
  (lambda ()
    (infer-text
     "{λ [$r :: PredTerm
                  (Row (1 (Referents Entity)) (2 (Referents Entity)))]
         ($r Speaker Audience This)}"))))

(check-not-exn (lambda () (infer-text "(At klama 2 This)")))
(check-not-exn (lambda () (infer-text "(DropPlace klama 3)")))
(check-true (type-error? (lambda () (infer-text "(At klama x2 This)"))))
(check-true (type-error? (lambda () (infer-text "(At klama 9 This)"))))
(check-true
 (type-error?
  (lambda ()
    (infer-text "{λ [$p :: PredTerm (RowOf zzzz)] (Close $p)}"))))
(check-not-exn
 (lambda ()
   (infer-text
    "{λ [$p :: PredTerm (RowMinus (RowOf klama) 3)]
        (Close ($p Speaker This That Yonder))}")))
(check-true
 (type-error?
  (lambda ()
    (infer-text "(SetOf {λ [$x :: Entity] (Context)})"))))

(check-not-exn
 (lambda ()
   (infer-text
    "{λ [$k :: DecompositionBasis (Group Entity) Entity]
       {Bind [$g :: Referents (Group Entity)] (Massify $k Speaker)
         (Mention $g)}}")))

(check-equal?
 (typing-type
  (infer-text
   "{λ [[$k :: DecompositionBasis (Group Entity) Entity]
        [$g :: Group Entity]]
      (components_κ $k $g)}"))
 '(Fn ((DecompositionBasis (Group Entity) Entity) (Group Entity))
      (Referents Entity)))

(check-true
 (type-error?
  (lambda ()
    (infer-text
     "{λ [$k :: Number]
        {Bind [$g :: Referents (Group Entity)] (Massify $k Speaker)
          (Mention $g)}}"))))

(check-true
 (type-error?
  (lambda ()
    (infer-text
     "{λ [[$k :: Number] [$g :: Group Entity]]
        (components_κ $k $g)}"))))

(check-not-exn
 (lambda ()
   (infer-text
    "{λ [[$p :: Fn (Entity) Content] [$r :: Referents Entity]]
       (CoveredBy $p $r)}")))

(check-true
 (type-error?
  (lambda ()
    (infer-text
     "{λ [[$p :: EFn (Entity) Content] [$r :: Referents Entity]]
        (CoveredBy $p $r)}"))))

(check-true
 (type-error?
  (lambda ()
    (infer-text
     "{λ [[$p :: Fn (Eventuality) Content] [$r :: Referents Entity]]
        (CoveredBy $p $r)}"))))

(check-equal?
 (typing-type (infer-text "(Combine Speaker Audience)"))
 '(Referents Entity))

(check-equal?
 (typing-type
  (infer-text "{λ [$x :: Entity] (Combine $x Speaker)}"))
 '(Fn (Entity) (Referents Entity)))

(check-true
 (type-error?
  (lambda () (infer-text "(Combine Speaker (Close (gerku Speaker)))"))))

(check-not-exn
 (lambda ()
   (infer-text
    "{λ [$k :: DecompositionBasis (Group Entity) Entity]
       {Bind [$g :: Referents (Group Entity)]
             (JoiGroup $k Speaker Audience)
         (Mention $g)}}")))

(define personal-others-use (infer-text "(Mention MiAOthers)"))
(check-not-false
 (member 'mi-a-others-defined (typing-obligations personal-others-use)))

(check-equal?
 (typing-type
  (infer-text
   "(Assert (CloseClause {λ [$e :: Referents Eventuality] (gerku Speaker)}))"))
 '(Act Assertion))

(check-true
 (type-error?
  (lambda ()
    (infer-text
     "(Assert {λ [$e :: Referents Eventuality] (gerku Speaker)})"))))

(check-true
 (type-error?
  (lambda ()
    (infer-text "(∃ {λ [$c :: Content] $c})"))))

(check-true
 (type-error?
  (lambda ()
    (infer-text
     "{λ [[$x3 :: Referents Entity] [$s :: Set Entity]] (∈ $x3 $s)}"))))

(check-not-exn
 (lambda ()
   (infer-text
    "{λ [[$x3 :: Referents Entity] [$r :: Referents Entity]] (Among $x3 $r)}")))

(check-true
 (type-error?
  (lambda ()
    (infer-text
     "{Bind [$o :: ActOccurrence Assertion]
            (Local (Perform (Assert (Close (gerku Speaker)))))
        (Mention $o)}"))))

(check-true
 (type-error?
  (lambda ()
    (infer-text
     "{λ [$g :: Group (PredTerm R)] (Mention $g)}"))))

(check-true
 (type-error?
  (lambda ()
    (infer-text
     "{λ [[$k :: ContributionBasis R1]
           [$p :: PredTerm R1]
           [$q :: PredTerm R2]]
         (JoiPred $k $p $q)}"))))

(check-true
 (type-error?
  (lambda ()
    (infer-text
     "{λ [[$p :: PredTerm R1] [$q :: PredTerm R1]]
         (JoiPred $p $q $q)}"))))

(define zero-mei
  (infer-text
   "{λ [$k :: DecompositionBasis (Group Entity) Entity] (MeiRel $k 0)}"))
(check-not-false (member "MeiRel kappa 0 is gap #23" (typing-gaps zero-mei)))

(check-equal?
 (typing-type
  (infer-text
   "{Let [$a :: Act Assertion] (Assert (Close (gerku Speaker)))
       (Do (Perform $a) (Perform $a))}"))
 'Discourse)

;; spec §5.3 (#33/#34): Refer's reference-level restrictor is EFn — it may
;; sequence retrieval sites, unlike SetOf/quantifier/selection restrictors.
(check-not-exn
 (lambda ()
   (infer-text
    "{Bind [$r :: Referents Entity]
       (Refer {λ [$x :: Referents Entity]
         {Bind [$s :: Scale] (Context) (gerku $x)}})
       (Mention $r)}")))

;; A member-level restrictor is the pure CoveredBy lift: an effectful one is
;; not a term (its sites must be hoisted outside the Refer, spec §5.3).
(check-true
 (type-error?
  (lambda ()
    (infer-text
     "{Bind [$r :: Referents Entity]
        (Refer {λ [$x :: Entity]
          {Bind [$s :: Scale] (Context) (gerku $x)}})
        (Mention $r)}"))))

;; A pure member-level restrictor is admitted (the lift).
(check-not-exn
 (lambda ()
   (infer-text
    "{Bind [$r :: Referents Entity]
       (Refer {λ [$x :: Entity] (gerku $x)})
       (Mention $r)}")))

(displayln "typing tests: ok")
