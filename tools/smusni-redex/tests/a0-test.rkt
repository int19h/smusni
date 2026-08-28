#lang racket

(require rackunit
         redex/reduction-semantics
         "../port-a0.rkt")

(define (synth environment term)
  (define derivations
    (build-derivations (a0-synth ,environment ,term R)))
  (check-equal? (length derivations) 1
                (format "unique synthesis derivation for ~s" term))
  (define results (judgment-holds (a0-synth ,environment ,term R) R))
  (check-equal? (length results) 1 (format "unique synthesis for ~s" term))
  (and (= (length results) 1) (first results)))

(define (check-at environment term type)
  (define derivations
    (build-derivations (a0-check ,environment ,term ,type R)))
  (check-equal? (length derivations) 1
                (format "unique checking derivation for ~s" term))
  (define results (judgment-holds (a0-check ,environment ,term ,type R) R))
  (check-equal? (length results) 1 (format "unique check for ~s" term))
  (and (= (length results) 1) (first results)))

(define entity-P '(λ (($x Entity)) ⊤))
(define reference-Q '(λ (($w (Referents Entity))) ⊤))
(define member-Q '(λ (($x Entity)) ⊤))

(define (no-synthesis? environment term)
  (and (null? (judgment-holds (a0-synth ,environment ,term R) R))
       (null? (build-derivations (a0-synth ,environment ,term R)))))

(define (no-checking? environment term type)
  (and (null? (judgment-holds (a0-check ,environment ,term ,type R) R))
       (null? (build-derivations
               (a0-check ,environment ,term ,type R)))))

;; Every definition is a general metafunction over its declared parameters.
(check-equal?
 (term (a0-expand-let $x Entity Speaker (P $x)))
 '((λ (($x Entity)) (P $x)) Speaker))
(check-equal? (term (a0-expand-exactly 0 Entity P Q)) '(No P Q))
(check-true
 (alpha-equivalent?
  SmusniA0
  (term (a0-expand-exactly 3 Entity P Q))
  '(Bind (($w (Referents Entity) (SelectExactly 3 P))) (Q $w))))
(check-true
 (alpha-equivalent?
  SmusniA0
  (term (a0-expand-global-exactly 3 Entity P Q))
  '(= (Card
       (SetOf
        (λ (($member Entity))
          (∧ (P $member) (Q $member)))))
      3)))
(check-true
 (alpha-equivalent?
  SmusniA0
  (term (a0-expand-too-many Entity P Q))
  '(Bind (($purpose (Referents Entity) (Context))
          ($threshold Natural
                      (Vague
                       (AdmissibleThreshold TooManyK P $purpose))))
     (MoreThan $threshold P Q))))
(check-true
 (alpha-equivalent?
  SmusniA0
  (term (a0-expand-massify Entity $basis $cover))
  '(SelectExactly
    1
    (λ (($group (Group Entity)))
      (CanonicalAggregateAt $basis $group $cover)))))
(check-equal? (term (a0-expand-zipwith f (List) (List))) '⊤)
(check-equal?
 (term (a0-expand-zipwith f (List a as) (List b bs)))
 '(∧ (f a b) (ZipWith f (List as) (List bs))))
(check-exn exn:fail?
           (lambda ()
             (term (a0-expand-zipwith f (List a) (List)))))

(define holding-close
  (term (a0-expand-close
         (row tavla 3 holding-state (1 2 3))
         ((1 Speaker) (2 Audience)))))
(check-true
 (alpha-equivalent?
  SmusniA0 holding-close
  '(Bind (($place3 (Referents Entity) (Context)))
     (CloseClause
      (ActualClause
       (StateClause (tavla Speaker Audience $place3)))))))
(define event-close
  (term (a0-expand-close
         (row bajra 4 direct-event (1 2 3 4))
         ((1 Speaker)))))
(check-not-false (member 'ActualClause (flatten event-close)))
(check-equal? (count (lambda (value) (eq? value 'Context))
                     (flatten event-close))
              3)
(check-not-false (member 'DirectClause (flatten event-close)))

(define explicit-event-close
  (term (a0-expand-close
         (row bajra 4 direct-event (1 2 3 4))
         ((1 Speaker) (Eventuality $shared-event)))))
(check-true
 (alpha-equivalent?
  SmusniA0 explicit-event-close
  '(Bind (($place2 (Referents Entity) (Context))
          ($place3 (Referents Entity) (Context))
          ($place4 (Referents Entity) (Context)))
     (CloseClause
      (λ (($clause-event (Referents Eventuality)))
        (∧ (CoRef $clause-event $shared-event)
           ((ActualClause
             (DirectClause
              (λ (($lexical-event (Referents Eventuality)))
                (bajra Speaker $place2 $place3 $place4 $lexical-event))))
            $shared-event)))))))
(check-exn
 exn:fail?
 (lambda ()
   (term (a0-expand-close
          (row tavla 3 holding-state (1 2 3))
          ((Eventuality $event))))))
(check-exn
 exn:fail?
 (lambda ()
   (term (a0-expand-close
          (row bajra 4 direct-event (1 2 3 4))
          ((Eventuality $left) (Eventuality $right))))))

;; Two-mode typing: definitions and their expansions agree record-for-record.
(define gq-env
  (term ((P (Fn (Entity) Content))
         (Q (EFn ((Referents Entity)) Content)))))
(define global-env
  (term ((P (Fn (Entity) Content))
         (Q (Fn (Entity) Content)))))
(check-equal? (synth gq-env (term (Exactly 0 P Q)))
              '(typing Content (effectful-call) ()))
(check-equal? (synth gq-env (term (Exactly 3 P Q)))
              '(typing Content (effectful-call refer) ()))
(check-equal? (synth global-env (term (GlobalExactly 3 P Q)))
              '(typing Content (projective)
                       (finite-set-cardinality-defined)))
(check-equal? (synth gq-env (term (TooMany P Q)))
              '(typing Content (context effectful-call refer) ()))

(check-equal?
 (length
  (build-derivations
   (a0-synth ()
             (ActualClause (λ (($e (Referents Eventuality))) ⊤)) R)))
 1)

(check-equal?
 (synth (term (($v (Referents Entity))))
        (term (Let ($x (Referents Entity)) $v $x)))
 '(typing (Referents Entity) () ()))
(check-true
 (no-synthesis?
  '()
  (term (Let ($c (RefComp (Referents Entity))) (Context) ⊤))))
(check-true
 (no-synthesis?
  (term (($f (EFn () Content))))
  (term (Let ($c Content) ($f) ⊤))))
(check-equal?
 (synth '() (term (Bind (($x (Referents Entity) (Context))) ⊤)))
 '(typing Content (context) ()))
(check-equal?
 (synth (term (($act (Act Assertion))))
        (term (Bind (($occ (ActOccurrence Assertion) (Perform $act)))
                $act)))
 '(typing Discourse (performance) ()))

(define basis-env
  (term (($basis (DecompositionBasis (Group Entity) Entity))
         ($cover (Referents Entity)))))
(check-equal?
 (check-at basis-env (term (Massify $basis $cover))
           (term (RefComp (Referents (Group Entity)))))
 '(typing (RefComp (Referents (Group Entity))) (refer) ()))

(define zip-env
  (term ((f (Fn ((Referents Entity) (Referents Entity)) Content)))))
(check-equal?
 (synth zip-env (term (ZipWith f (List Speaker) (List Audience))))
 '(typing Content () ()))
(define effectful-zip-env
  (term ((f (EFn ((Referents Entity) (Referents Entity)) Content)))))
(check-equal?
 (synth effectful-zip-env (term (ZipWith f (List) (List))))
 '(typing Content () ()))

(define close-env
  (term ((tavla
          (Fn ((Referents Entity) (Referents Entity) (Referents Entity))
              Content)))))
(check-equal?
 (synth close-env
        (term (CloseWith
               (row tavla 3 holding-state (1 2 3))
               ((1 Speaker) (2 Audience)))))
 '(typing Content (context) ()))

(define event-close-env
  (term ((bajra
          (Fn ((Referents Entity) (Referents Entity)
               (Referents Entity) (Referents Entity)
               (Referents Eventuality))
              Content))
         ($shared-event (Referents Eventuality)))))
(check-equal?
 (synth event-close-env
        (term (CloseWith
               (row bajra 4 direct-event (1 2 3 4))
               ((1 Speaker) (Eventuality $shared-event)))))
 '(typing Content (context) ()))
(define full-explicit-event-close
  (term (a0-expand-close
         (row bajra 4 direct-event (1 2 3 4))
         ((1 Speaker) (2 Audience) (3 Speaker) (4 Audience)
          (Eventuality $shared-event)))))
(check-equal?
 (synth event-close-env full-explicit-event-close)
 '(typing Content () ()))
(check-not-exn
 (lambda ()
   (judgment-holds
    (a0-synth
     ,close-env
     (CloseWith (row tavla 3 holding-state (1 2 3)) ((4 Speaker)))
     R)
    R)))
(check-true
 (no-synthesis?
  close-env
  (term (CloseWith
         (row tavla 3 holding-state (1 2 3)) ((4 Speaker))))))

(define (check-preserved environment source expanded)
  (check-equal? (synth environment source) (synth environment expanded)))

(check-preserved
 (term (($v (Referents Entity))))
 (term (Let ($x (Referents Entity)) $v $x))
 (term (a0-expand-let $x (Referents Entity) $v $x)))
(check-preserved gq-env
                 (term (Exactly 0 P Q))
                 (term (a0-expand-exactly 0 Entity P Q)))
(check-preserved gq-env
                 (term (Exactly 3 P Q))
                 (term (a0-expand-exactly 3 Entity P Q)))
(check-preserved global-env
                 (term (GlobalExactly 3 P Q))
                 (term (a0-expand-global-exactly 3 Entity P Q)))
(check-preserved gq-env
                 (term (TooMany P Q))
                 (term (a0-expand-too-many Entity P Q)))
(check-equal?
 (check-at basis-env (term (Massify $basis $cover))
           (term (RefComp (Referents (Group Entity)))))
 (check-at basis-env (term (a0-expand-massify Entity $basis $cover))
           (term (RefComp (Referents (Group Entity))))))
(check-preserved zip-env
                 (term (ZipWith f (List Speaker) (List Audience)))
                 (term (a0-expand-zipwith f (List Speaker) (List Audience))))
(check-preserved effectful-zip-env
                 (term (ZipWith f (List) (List)))
                 (term (a0-expand-zipwith f (List) (List))))
(check-preserved close-env
                 (term (CloseWith
                        (row tavla 3 holding-state (1 2 3))
                        ((1 Speaker) (2 Audience))))
                 holding-close)
(check-preserved
 event-close-env
 (term (CloseWith
        (row bajra 4 direct-event (1 2 3 4))
        ((1 Speaker) (Eventuality $shared-event))))
 explicit-event-close)
(check-preserved
 event-close-env
 (term (CloseWith
        (row bajra 4 direct-event (1 2 3 4))
        ((1 Speaker) (2 Audience) (3 Speaker) (4 Audience)
         (Eventuality $shared-event))))
 full-explicit-event-close)

;; L0.1's six profiles plus scope/quotation negatives.
(define independent-body
  (term (λ (($x Entity)) (P $x (Site b) (Site a)))))
(define independent-sites-ab
  (term (sites
         (site a (context) (Referents Entity) pure (deps))
         (site b (context) (Referents Entity) pure (deps)))))
(define independent-sites-ba
  (term (sites
         (site b (context) (Referents Entity) pure (deps))
         (site a (context) (Referents Entity) pure (deps)))))
(define independent-ab
  (term (a0-hoist () ,independent-body ,independent-sites-ab)))
(define independent-ba
  (term (a0-hoist () ,independent-body ,independent-sites-ba)))
(check-true (alpha-equivalent? SmusniA0 independent-ab independent-ba))
(match independent-ab
  [`(ok ,hoisted)
   (check-equal?
    (synth
     (term ((P
             (Fn (Entity (Referents Entity) (Referents Entity)) Content))))
     hoisted)
    '(typing (Fn (Entity) Content) (context) ()))]
  [other (fail-check (format "unexpected independent hoist: ~e" other))])

(define dependent-result
  (term
   (a0-hoist
    ()
    (λ (($x Entity)) (P $x (Site cutoff) (Site scale)))
    (sites
     (site cutoff (vague (F (SiteValue scale))) Natural pure
           (deps (site scale)))
     (site scale (context) (Referents Entity) pure (deps))))))
(match dependent-result
  [`(ok (Bind ((,scale-var (Referents Entity) (Context)))
          (Bind ((,_cutoff-var Natural (Vague (F ,dependency)))) ,_)))
   (check-equal? dependency scale-var)]
  [other (fail-check (format "unexpected dependent hoist: ~e" other))])

(define outer-result
  (term
   (a0-hoist
    (($topic (Referents Entity)))
    (λ (($x Entity)) (P $x (Site standard)))
    (sites
     (site standard (context $topic) (Referents Entity) pure
           (deps (outer $topic (Referents Entity))))))))
(check-not-false (member '$topic (flatten outer-result)))
(check-equal?
 (term
  (a0-hoist
   ()
   (λ (($x Entity)) (P $x (Site standard)))
   (sites
    (site standard (context $x) (Referents Entity) pure (deps)))))
 '(refusal member-dependent))
(check-equal?
 (term
  (a0-hoist
   (($topic (Referents Entity)))
   (λ (($x Entity)) (P $x (Site standard)))
   (sites
    (site standard (context $topic) (Referents Entity) pure (deps)))))
 '(refusal malformed-metadata))
(check-equal?
 (term
  (a0-hoist
   ()
   (λ (($x Entity)) (P $x (Site standard)))
   (sites
    (site standard (context $topic) (Referents Entity) pure
          (deps (outer $topic (Referents Entity)))))))
 '(refusal malformed-metadata))

;; Normative formation boundaries that compatibility must not erase.
(check-true
 (no-checking?
  '() (term (SelectExactly 0 (λ (($x Entity)) ⊤)))
  (term (RefComp (Referents Entity)))))
(check-true (no-synthesis? '() (term (= Speaker Audience))))
(check-true
 (no-synthesis?
  (term (($f (Fn (Entity) Content))))
  (term (= $f $f))))
(check-equal?
 (check-at
  (term (($P (EFn ((Referents Entity)) Content))))
  (term (Refer $P))
  (term (RefComp (Referents Entity))))
 '(typing (RefComp (Referents Entity)) (effectful-call refer) ()))

(check-equal?
 (term
  (a0-hoist
   ()
   (λ (($x Entity)) (P $x (Site standard)))
   (sites
    (site standard (context) (Referents Entity) pure (deps (member))))))
 '(refusal member-dependent))

(check-equal?
 (term
  (a0-hoist
   ()
   (λ (($x Entity)) (SelectSome (λ (($y Entity)) ⊤)))
   (sites)))
 '(refusal introduction))
(check-equal?
 (term
  (a0-hoist
   ()
   (λ (($x Entity))
     (Let ($z (Referents Entity))
          (SelectExactly 1 (λ (($y Entity)) ⊤))
       ⊤))
   (sites)))
 '(refusal introduction))

;; An introduction outside the supplied pure-position term is out of scope;
;; quotation/syntax inside it is inert and must not trigger refusal.
(check-equal?
 (term (a0-hoist () (λ (($x Entity)) ⊤) (sites)))
 '(ok (λ (($x Entity)) ⊤)))
(check-equal?
 (term
  (a0-hoist
   () (λ (($x Entity)) (Quote (SelectSome (λ (($y Entity)) ⊤))))
   (sites)))
 '(ok (λ (($x Entity)) (Quote (SelectSome (λ (($y Entity)) ⊤))))))

(define-values (witnessed-rules uncovered-rules native-cases)
  (a0-coverage-report #:print? #f))
(check-equal? (length witnessed-rules) (length a0-required-rules))
(check-equal? (sort (map first a0-rule-anchors) string<?)
              (sort a0-required-rules string<?))
(check-equal? (second (assoc "A0-T-Context" a0-rule-anchors)) "spec §5.3")
(check-equal? (second (assoc "A0-T-Equality" a0-rule-anchors)) "spec §4.5")
(check-equal? uncovered-rules '())
(check-true (andmap (lambda (entry) (positive? (cdr entry))) native-cases))

(define generation
  (run-a0-generation-measurement
   #:attempts 100 #:size 5 #:seed 520 #:print? #f))
(check-equal? (a0-generation-attempts generation) 100)
(check-equal? (a0-generation-generated generation) 100)
(check-true (positive? (a0-generation-satisfying generation)))
(check-equal?
 (a0-generation-disposition generation)
 (if (and (<= (a0-generation-discard-ratio generation) 0.99)
          (>= (a0-generation-cases-per-minute generation) 100)
          (pair? (a0-generation-constructors generation))
          (positive? (a0-generation-max-binder-depth generation)))
     'generated
     'fixture/enumeration-only))

(displayln "A0 Redex vertical slice: ok")
