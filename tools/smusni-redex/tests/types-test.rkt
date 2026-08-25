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
   "(Assert (CloseClause (λ {$e :: Referents Eventuality} {(gerku Speaker)})))"))
 '(Act Assertion))

(check-true
 (type-error?
  (lambda ()
    (infer-text
     "(Assert (λ {$e :: Referents Eventuality} {(gerku Speaker)}))"))))

(check-true
 (type-error?
  (lambda ()
    (infer-text "(∃ (λ {$c :: Content} {$c}))"))))

(check-true
 (type-error?
  (lambda ()
    (infer-text
     "(λ {{$x3 :: Referents Entity} {$s :: Set Entity}} {(∈ $x3 $s)})"))))

(check-not-exn
 (lambda ()
   (infer-text
    "(λ {{$x3 :: Referents Entity} {$r :: Referents Entity}} {(Among $x3 $r)})")))

(check-true
 (type-error?
  (lambda ()
    (infer-text
     "(Bind {$o :: ActOccurrence Assertion}
            (Local (Perform (Assert (Close (gerku Speaker)))))
        {(Mention $o)})"))))

(check-true
 (type-error?
  (lambda ()
    (infer-text
     "(λ {$g :: Group (PredTerm R)} {(Mention $g)})"))))

(check-true
 (type-error?
  (lambda ()
    (infer-text
     "(λ {{$k :: ContributionBasis R1}
           {$p :: PredTerm R1}
           {$q :: PredTerm R2}}
         {(JoiPred $k $p $q)})"))))

(check-true
 (type-error?
  (lambda ()
    (infer-text
     "(λ {{$p :: PredTerm R1} {$q :: PredTerm R1}}
         {(JoiPred $p $q $q)})"))))

(define zero-mei
  (infer-text
   "(λ {$k :: DecompositionBasis (Group Entity) Entity} {(MeiRel $k 0)})"))
(check-not-false (member "MeiRel kappa 0 is gap #23" (typing-gaps zero-mei)))

(check-equal?
 (typing-type
  (infer-text
   "(Let {$a :: Act Assertion} (Assert (Close (gerku Speaker)))
       {(Do (Perform $a) (Perform $a))})"))
 'Discourse)

(displayln "typing tests: ok")

