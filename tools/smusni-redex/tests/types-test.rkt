#lang racket

(require rackunit
         redex/reduction-semantics
         "../syntax.rkt"
         "../types.rkt")

(define (infer-text text)
  (infer-core (read-core-specimen text 'types-test)))

(define (type-error? thunk)
  (with-handlers ([exn:fail:smusni? (lambda (_) #t)])
    (thunk)
    #f))

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

;; Refer is deliberately EFn-admitting: its property may sequence retrieval
;; sites, unlike SetOf/quantifier/selection restrictors.
(check-not-exn
 (lambda ()
   (infer-text
    "{Bind [$r :: Referents Entity]
       (Refer {λ [$x :: Entity]
         {Bind [$s :: Scale] (Context) (gerku $x)}})
       (Mention $r)}")))

(displayln "typing tests: ok")
