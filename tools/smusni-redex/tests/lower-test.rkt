#lang racket

(require json
         rackunit
         racket/list
         racket/set
         redex/reduction-semantics
         "../elaborate.rkt"
         "../lower.rkt"
         "../syntax.rkt"
         "../types.rkt")

(define manifest (load-lowering-manifest))
(check-equal? (lowering-manifest-families manifest) '("L0" "L1" "L3" "L5"))
(check-equal? (lowering-manifest-rule-count manifest) 46)
(check-equal? (length (lowering-manifest-candidates manifest)) 27)
(check-equal?
 (for/sum ([candidate (in-list (lowering-manifest-candidates manifest))])
   (length (lowering-candidate-cases candidate)))
 30)

(define rules (fragment-rule-ids manifest))
(check-equal? (length rules) 46)
(check-not-false (member "L0.1" rules))
(check-not-false (member "L1.10" rules))
(check-not-false (member "L3.15" rules))
(check-not-false (member "L5.29" rules))
(check-false (member "L1.9" rules))
(check-false (member "L3.7" rules))
(check-false (member "L5.14" rules))

(define redex-rule-names
  (map symbol->string (judgment-form->rule-names m3-lower)))
(check-equal? (length redex-rule-names)
              (set-count (list->set redex-rule-names)))
(check-equal? (length redex-rule-names) 31)
(for ([name (in-list redex-rule-names)])
  (check-not-false (member name rules)))

(check-not-exn (lambda () (validate-lowering-fixtures! manifest)))

(define samples-17
  (findf (lambda (candidate)
           (and (string=? (lowering-candidate-source candidate) "samples.md")
                (= (lowering-candidate-ordinal candidate) 17)))
         (lowering-manifest-candidates manifest)))
(check-equal? (map lowering-case-index (lowering-candidate-cases samples-17))
              '(1 2))
(define samples-17-parse (load-parse-fixture samples-17))
(check-equal? (hash-ref samples-17-parse 'source) "samples.md")
(check-equal? (length (hash-ref samples-17-parse 'cases)) 2)
(for ([case (in-list (hash-ref samples-17-parse 'cases))])
  (check-true (hash? (hash-ref case 'parse))))
(define samples-17-first (first (hash-ref samples-17-parse 'cases)))
(check-equal? (parse-case-tokens samples-17-first)
              '("mi" "klama" ".ije" "do" "stali"))
(check-true (set-member? (parse-case-variants samples-17-first)
                         'IStatementConnection))
(check-equal? (hash-ref samples-17-first 'source_comment)
              "mi klama .ije do stali — joint State; one assertion")

(define samples-63
  (findf (lambda (candidate)
           (and (string=? (lowering-candidate-source candidate) "samples.md")
                (= (lowering-candidate-ordinal candidate) 63)))
         (lowering-manifest-candidates manifest)))
(check-equal? (length (rr-fixture-cases (load-rr-fixture samples-63))) 3)

(define spec-10
  (findf (lambda (candidate)
           (and (string=? (lowering-candidate-source candidate) "spec.md")
                (= (lowering-candidate-ordinal candidate) 10)))
         (lowering-manifest-candidates manifest)))
(define spec-10-case (first (lowering-candidate-cases spec-10)))
(check-equal? (lowering-case-surface spec-10-case) "ci gerku cu bajra")
(check-false (lowering-case-unresolved spec-10-case))
(check-true
 (hash? (hash-ref (first (hash-ref (load-parse-fixture spec-10) 'cases))
                  'parse)))
(check-true
 (string-prefix?
  (hash-ref (first (hash-ref (load-parse-fixture spec-10) 'cases))
            'source_comment)
  "ci gerku cu bajra"))

(define absent
  (lower 'parse 'rr))
(check-true (no-lowering? absent))
(check-equal? (no-lowering-cause absent) 'rr-missing)

(define (candidate-at source ordinal)
  (findf (lambda (candidate)
           (and (string=? (lowering-candidate-source candidate) source)
                (= (lowering-candidate-ordinal candidate) ordinal)))
         (lowering-manifest-candidates manifest)))

(define (case-input source ordinal [index 1])
  (define candidate (candidate-at source ordinal))
  (define parse-case
    (list-ref (hash-ref (load-parse-fixture candidate) 'cases) (sub1 index)))
  (define rr
    (list-ref (rr-fixture-cases (load-rr-fixture candidate)) (sub1 index)))
  (values parse-case rr))

(define-values (description-parse _description-rr) (case-input "samples.md" 19))
(check-true (set-member? (parse-case-variants description-parse)
                         'DescriptorWithGadriSumti))
(define-values (quantity-parse _quantity-rr) (case-input "spec.md" 9))
(check-true (set-member? (parse-case-variants quantity-parse)
                         'DescriptorWithoutGadriSumti))
(check-true (set-member? (parse-case-variants quantity-parse)
                         'PaRunQuantifier))

(define (plain node)
  (cond [(core-atom? node) (core-atom-value node)]
        [else (map plain (core-list-elements node))]))

(define (check-lowers source ordinal expected rules [index 1])
  (define-values (parse-case rr) (case-input source ordinal index))
  (define result (lower parse-case rr))
  (check-true (lowered? result) (format "~a#~a.~a lowers" source ordinal index))
  (when (lowered? result)
    (check-true
     (redex-alpha-equivalent? (plain (lowered-term result)) expected)
     (format "~a#~a.~a output is alpha-equivalent to expected"
             source ordinal index))
    (for ([rule (in-list rules)])
      (check-not-false
       (member rule (lowered-rules result))
       (format "~a#~a.~a derivation contains ~a; got ~e"
               source ordinal index rule (lowered-rules result))))))

(define (check-does-not-lower source ordinal cause rule [index 1])
  (define-values (parse-case rr) (case-input source ordinal index))
  (define result (lower parse-case rr))
  (check-true (no-lowering? result))
  (when (no-lowering? result)
    (check-equal? (no-lowering-cause result) cause)
    (check-equal? (no-lowering-rule result) rule)))

(check-lowers "samples.md" 1
              '(Assert (Close (klama Speaker)))
              '("L1.1" "L1.3" "L1.6"))
(check-lowers "samples.md" 3
              '(Assert (Close (klama :2 This Yonder)))
              '("L1.4" "L1.6"))
(check-lowers "samples.md" 4
              '(Assert (Close ((DropPlace klama 3) Speaker This This This)))
              '("L1.5"))
(check-lowers "samples.md" 5
              '(Assert (Close (klama Speaker This)))
              '("L1.4"))
(check-lowers "samples.md" 58
              '(Assert (Close ((Tanru sutra klama) Speaker)))
              '("L1.10" "L1.6"))
(check-lowers "samples.md" 63
              '(Bind ($r :: PredTerm
                         (Row (1 (Referents Entity)) (2 (Referents Entity))))
                     (Context)
                 (Assert (Close ($r Speaker Audience))))
              '("L1.8") 3)
(check-lowers "spec.md" 1 '(klama Speaker This) '("L1.1"))
(check-lowers "spec.md" 2 '(klama :2 This Yonder) '("L1.4"))
(check-lowers "spec.md" 4
              '(λ ($new1 $new2 :: Referents Entity) (tavla $new2 $new1))
              '("L1.4"))

(check-lowers
 "samples.md" 19
 '(Bind ($cat :: Referents Entity)
        (Refer (λ ($x :: Referents Entity) (mlatu $x)))
    (Assert (Close (blabi $cat))))
 '("L3.1"))
(check-lowers
 "samples.md" 21
 '(Bind ($cat :: Referents Entity)
        (Refer (λ ($x :: Referents Entity) (mlatu $x)))
    (Assert (CloseClause (ClauseNot (DirectClause (jbena $cat))))))
 '("L3.1" "L5.9"))
(check-lowers
 "samples.md" 22
 '(Bind ($it :: Referents Entity)
        (Refer
         (λ ($x :: Referents Entity)
           (SpeakerDescribes
            $x (λ ($y :: Referents Entity) (mlatu $y)))))
    (Assert (Close (blabi $it))))
 '("L3.2"))
(check-lowers
 "samples.md" 23
 '(Bind ($alis :: Referents Entity)
        (Refer (λ ($x :: Referents Entity) (Named "alis" $x)))
    (Assert (Close (klama $alis))))
 '("L3.3"))
(check-lowers
 "samples.md" 45
 '(Assert
   (No (λ ($x :: Entity) (prenu $x))
       (λ ($w :: Referents Entity) (Close (jmaji $w)))))
 '("L3.10"))
(check-lowers
 "samples.md" 27
 '(Bind ($basis :: DecompositionBasis (Group Entity) Entity)
        (Context (GroupBasisConstraint joi Entity) deps…)
    (Bind ($group :: Referents (Group Entity))
          (JoiGroup $basis Speaker Audience)
      (Mention $group)))
 '("L5.22"))
(check-lowers
 "samples.md" 30
 '(Bind ($base :: Referents Entity)
        (Local (Refer (λ ($x :: Entity) (gerku $x))))
    (Bind ($sets :: Referents (Set Entity))
          (Refer (λ ($s :: Set Entity) (Close (selcmi $s $base))))
      (Mention $sets)))
 '("L3.5" "L3.6"))
(check-lowers
 "samples.md" 34
 '(Bind ($people :: Referents Entity)
        (Local
         (SelectExactly
          3
          (λ ($x :: Entity)
            (SpeakerDescribes
             $x (λ ($y :: Referents Entity) (prenu $y))))))
    (Bind ($κ :: DecompositionBasis (Group Entity) Entity)
          (Context (GroupBasisConstraint |lu'o| Entity) deps…)
      (Bind ($aggregate :: Referents (Group Entity))
            (Massify $κ $people)
        (Mention $aggregate))))
 '("L3.2" "L3.9" "L3.14" "L3.15"))
(check-lowers
 "samples.md" 36
 '(Assert
   (Generic Typical
            (λ ($x :: Entity) (mlatu $x))
            (λ ($x :: Entity) (Close (cinri $x)))))
 '("L3.4"))

(check-lowers
 "samples.md" 16
 '(Assert
   (CloseClause
    (ActualClause (ClauseNot (DirectClause (klama Speaker))))))
 '("L5.9"))
(check-lowers
 "samples.md" 17
 '(Assert
   (CloseClause
    (ActualClause
     (ClauseAnd (DirectClause (klama Speaker))
                (DirectClause (stali Audience))))))
 '("L5.12" "L5.8") 1)
(check-lowers
 "samples.md" 17
 '(Assert
   (CloseClause
    (ActualClause
     (ClauseOr (DirectClause (klama Speaker))
               (DirectClause (stali Audience))))))
 '("L5.12" "L5.8") 2)
(check-lowers
 "samples.md" 44
 '(Assert
   (Every (λ ($x :: Entity) (gerku $x))
          (λ ($x :: Entity) (Close (blabi $x)))))
 '("L5.1"))
(check-lowers
 "samples.md" 46
 '(Bind ($dogs :: Referents Entity)
        (SelectExactly 3 (λ ($x :: Entity) (gerku $x)))
        ($people :: Referents Entity)
        (SelectExactly 2 (λ ($x :: Entity) (prenu $x)))
    (Assert
     (Distrib
      (λ ($d :: Entity)
        (Distrib
         (λ ($p :: Entity) (Close (nelci $d $p)))
         $people))
      $dogs)))
 '("L5.3"))
(check-lowers
 "samples.md" 48
 '(Bind ($n :: Natural)
        (Vague (AdmissibleThreshold
                ManyK (λ ($x :: Entity) (prenu $x))))
    (Assert
     (AtLeast $n
              (λ ($x :: Entity) (prenu $x))
              (λ ($w :: Referents Entity) (Close (klama $w))))))
 '("L5.28"))
(check-lowers
 "samples.md" 59
 '(Bind ($d :: ContrastDomain (RowOf melbi)) (Context)
    (Assert (Close ((Scalar OtherThan $d melbi) That))))
 '("L5.11"))
(check-lowers
 "samples.md" 63
 '(Bind ($s :: Scale) (Context)
        ($reg :: Region Scale)
        (Vague (λ ($r :: Region Scale) (AdmissibleCutoff $s $r)))
    (Assert (Close ((Grade barda $s $reg) That))))
 '("L5.29") 1)
(check-lowers
 "samples.md" 63
 '(Bind ($purpose :: Referents Entity) (Context)
        ($n :: Natural)
        (Vague
         (AdmissibleThreshold
          TooManyK (λ ($x :: Entity) (gerku $x)) $purpose))
    (Assert
     (MoreThan $n
               (λ ($x :: Entity) (gerku $x))
               (λ ($w :: Referents Entity) (Close (klama $w))))))
 '("L5.28") 2)
(check-lowers
 "spec.md" 9
 '(Bind ($w :: Referents Entity)
        (SelectExactly 3 (λ ($x :: Entity) (gerku $x)))
    (Close (bajra $w)))
 '("L5.2"))
(check-lowers
 "spec.md" 19
 '(ZipWith
   (λ ($s $l :: Referents Entity) (Close (tavla $s $l)))
   (List Speaker Audience)
   (List Audience Speaker))
 '("L5.21"))

(define-values (spec-10-parse spec-10-rr) (case-input "spec.md" 10))
(define spec-10-result (lower spec-10-parse spec-10-rr))
(check-true (lowered? spec-10-result))
(when (lowered? spec-10-result)
  (check-not-false (member 'GlobalExactly
                           (flatten (plain (lowered-term spec-10-result)))))
  (check-not-false (member "L5.2" (lowered-rules spec-10-result)))
  (check-not-false (member "L0.1" (lowered-rules spec-10-result))))

;; Symmetric normalizer: α-renaming, Close/P15, force shorthand, and L0.1.
(check-true
 (redex-alpha-equivalent?
  '(λ ($x :: Entity) (gerku $x))
  '(λ ($dog :: Entity) (gerku $dog))))
(check-false
 (redex-alpha-equivalent?
  '(λ ($x :: Entity) (gerku $x))
  '(λ ($dog :: Entity) (gerku Speaker))))
(check-true
 (redex-alpha-equivalent?
  '(Let ($x :: Entity) Speaker (gerku $x))
  '(Let ($speaker :: Entity) Speaker (gerku $speaker))))
(check-true
 (redex-alpha-equivalent?
  '(Bind ($x :: Entity) (Context) (gerku $x))
  '(Bind ($dog :: Entity) (Context) (gerku $dog))))
(check-true
 (redex-alpha-equivalent?
  '(Bind ($x :: Entity) (Context)
         ($y :: Entity) (Refer (λ ($r :: Entity) (nelci $x $r)))
     (nelci $x $y))
  '(Bind ($cat :: Entity) (Context)
         ($friend :: Entity) (Refer (λ ($z :: Entity) (nelci $cat $z)))
     (nelci $cat $friend))))
(check-true
 (redex-alpha-equivalent?
  '(λ ($x :: Entity) (λ ($y :: Entity) (nelci $x $y)))
  '(λ ($y :: Entity) (λ ($x :: Entity) (nelci $y $x)))))
(check-false
 (redex-alpha-equivalent?
  '(λ ($x :: Entity) (λ ($y :: Entity) (nelci $x $y)))
  '(λ ($y :: Entity) (λ ($x :: Entity) (nelci $x $y)))))

;; Rule construction itself avoids capturing variables supplied by an unseen
;; source view; alpha-equivalence is not being used to hide capture afterward.
(define capture-safe-pure
  (judgment-holds
   (m3-lower rr (gentufa parse (l0 (pure lexical $x))) e_output)
   e_output))
(check-equal? (length capture-safe-pure) 1)
(match (first capture-safe-pure)
  [`(λ (,binder :: Entity) ($x ,use))
   (check-equal? binder use)
   (check-not-equal? binder '$x)]
  [other (fail-check (format "unexpected capture test output: ~e" other))])

(check-true
 (redex-alpha-equivalent?
  '(Bind ($x :: Entity) (Context)
         ($x :: Entity) (Context)
     (gerku $x))
  '(Bind ($cat :: Entity) (Context)
         ($dog :: Entity) (Context)
     (gerku $dog))))
(check-false
 (redex-alpha-equivalent?
  '(Bind ($x :: Entity) (Context)
         ($x :: Entity) (Context)
     (gerku $x))
  '(Bind ($cat :: Entity) (Context)
         ($dog :: Entity) (Context)
     (gerku $cat))))

(define located-core
  (read-core-specimen
   "{Bind [$x :: Entity] (Context)\n
      [$y :: Entity] (Context)\n
      (nelci $x $y)}"
   'adapter-roundtrip))
(define located-adapter (core->redex-adapter located-core))
(check-equal? (redex-adapter->core located-adapter) located-core)
(check-exn
 exn:fail?
 (lambda ()
   (redex-adapter->core
    (struct-copy core-redex-adapter located-adapter
                 [term '(blabi Speaker)]))))
(check-equal?
 (elaboration-sites (elaborate-core (redex-adapter->core located-adapter)))
 (elaboration-sites (elaborate-core located-core)))

(define alpha-site-left
  (read-core-specimen
   "{Bind [$x :: Entity] (Context)\n  (gerku $x)}" 'site-alpha))
(define alpha-site-right
  (read-core-specimen
   "{Bind [$dog :: Entity] (Context)\n  (gerku $dog)}" 'site-alpha))
(check-true
 (alpha-equivalent?
  SmusniCore
  (core-redex-adapter-term (core->redex-adapter alpha-site-left))
  (core-redex-adapter-term (core->redex-adapter alpha-site-right))))
;; Binding equivalence does not rewrite source-derived site identity: changing
;; binder spelling shifts the written Context column, so the site ids differ.
(check-not-equal? (elaboration-sites (elaborate-core alpha-site-left))
                  (elaboration-sites (elaborate-core alpha-site-right)))
(check-equal? (site-signatures (plain alpha-site-left))
              (site-signatures (plain alpha-site-right)))
(check-not-equal?
 (site-signatures
  '(Bind ($x :: Entity) (Context)
     (Vague (Admissible $x))))
 (site-signatures
  '(Bind ($renamed :: Entity) (Context)
     (Vague (Admissible Speaker)))))
(check-not-equal?
 (site-signatures '(Bind ($x :: Entity) (Context) (Vague (Use $x))))
 (site-signatures '(Bind ($x :: Entity) (Vague (Use Speaker)) (Context))))

(define close-normal
  (normalize-core (datum->core '(Close (klama Speaker)))
                  (hash 'rows '(klama))))
(check-not-false
 (member "Close (§4.6/L1.3)" (normalization-expansions close-normal)))
(check-not-false
 (member "4 omitted places (P15/L1.6)"
         (normalization-expansions close-normal)))
(check-false (member 'Close (flatten (normalization-datum close-normal))))
(define normalized-symbols
  (filter symbol? (flatten (normalization-datum close-normal))))
(check-equal? (length (remove-duplicates
                       (filter (lambda (value)
                                 (regexp-match? #rx"^[$]ctx[1-5]$"
                                                (symbol->string value)))
                               normalized-symbols)))
              4)

(define capture-safe-close
  (normalization-datum
   (normalize-core (datum->core '(Close (klama $ctx2 $event)))
                   (hash 'rows '(klama)))))
(check-equal?
 capture-safe-close
 '(CloseClause
   (ActualClause
    (λ ($event1 :: Referents Eventuality)
      (Bind ($ctx3 :: Referents Entity) (Context)
        (Bind ($ctx4 :: Referents Entity) (Context)
          (Bind ($ctx5 :: Referents Entity) (Context)
            (klama :1 $ctx2 :2 $event :3 $ctx3 :4 $ctx4 :5 $ctx5
                   :Eventuality $event1))))))))

(define force-normal
  (normalize-core (datum->core '(Assert (gerku Speaker)))
                  (hash 'rows '(gerku))))
(check-equal? (normalization-datum force-normal)
              '(Assert (CloseClause (ActualClause (StateClause (gerku Speaker))))))
(check-not-false
 (member "force-boundary clause shorthand (§2)"
         (normalization-expansions force-normal)))

(define l0-normal
  (normalize-core
   (datum->core '(SetOf (λ ($x :: Entity) (gerku $x))))
   (hash 'rows '(gerku))))
(check-not-false
 (member "bare lexical property (L0.1)"
         (normalization-expansions l0-normal)))
(define reference-refer-normal
  (normalize-core
   (datum->core
    '(Refer (λ ($x :: Referents Entity) (mlatu $x))))
   (hash 'rows '(mlatu))))
(check-false
 (member "bare lexical property (L0.1)"
         (normalization-expansions reference-refer-normal)))

;; Explicit §12 definitions normalize one way, before pure-position display
;; rewrites, and are idempotent/type- and site-preserving.
(define global-defined
  '(GlobalExactly
    2
    (λ ($p :: Entity) (prenu $p))
    (λ ($q :: Entity) (blabi $q))))
(define global-defined-normal
  (normalize-core (datum->core global-defined)
                  (hash 'rows '(prenu blabi))))
(define global-expanded (normalization-datum global-defined-normal))
(check-not-false
 (member "§12 definition of `GlobalExactly`"
         (normalization-expansions global-defined-normal)))
(check-true
 (redex-alpha-equivalent?
  global-expanded
  '(= (Card
       (SetOf
        (λ ($member :: Entity)
          (∧ (prenu $member) (blabi $member)))))
      2)))
(define global-idempotent
  (normalize-core (datum->core global-expanded)
                  (hash 'rows '(prenu blabi))))
(check-equal? (normalization-datum global-idempotent) global-expanded)
(check-false
 (member "§12 definition of `GlobalExactly`"
         (normalization-expansions global-idempotent)))
(define global-original-typing (infer-core (datum->core global-defined)))
(define global-expanded-typing (infer-core (datum->core global-expanded)))
(check-equal? (typing-type global-original-typing)
              (typing-type global-expanded-typing))
(check-equal? (typing-gaps global-expanded-typing) '())
(check-equal? (site-signatures global-defined)
              (site-signatures global-expanded))

(define most-defined
  '(Most
    (λ ($p :: Entity) (prenu $p))
    (λ ($q :: Entity) (blabi $q))))
(define most-defined-normal
  (normalize-core (datum->core most-defined)
                  (hash 'rows '(prenu blabi))))
;; Most is deliberately deferred: its normative expansion uses primitive `>`,
;; which is not yet in the checker inventory/type judgment. Expanding it here
;; would violate the required type-preservation property.
(check-not-false (member 'Most (flatten (normalization-datum most-defined-normal))))
(check-false
 (member "§12 definition of `Most`"
         (normalization-expansions most-defined-normal)))
(check-equal?
 (typing-type
  (infer-core (datum->core (normalization-datum most-defined-normal))))
 'Content)
(check-equal? (site-signatures most-defined)
              (site-signatures (normalization-datum most-defined-normal)))

(define impure-most
  '(Most
    (λ ($p :: Entity) (prenu $p))
    (λ ($q :: Entity)
      (Bind ($context :: Referents Entity) (Context)
        (blabi $q)))))
(define impure-most-normal
  (normalize-core (datum->core impure-most)
                  (hash 'rows '(prenu blabi))))
(check-not-false (member 'Most (flatten (normalization-datum impure-most-normal))))
(check-false
 (member "§12 definition of `Most`"
         (normalization-expansions impure-most-normal)))

;; Full candidate run: structurally formed cases match; the honest unformed
;; and missing-surface dispositions remain visible/non-failing.
(define-values (gate-ok? reports fence-reports)
  (run-lowering-gate #:print? #f))
(check-true gate-ok?)
(check-equal? (count (lambda (report)
                       (eq? (case-report-disposition report)
                            'in-fragment/matched))
                     reports)
              30)
(check-equal? (count (lambda (report)
                       (eq? (case-report-disposition report) 'unresolved))
                     reports)
              0)
(check-equal? (count (lambda (report)
                       (eq? (case-report-disposition report)
                            'in-fragment/no-lowering))
                     reports)
              0)
(check-equal? (count (lambda (report)
                       (eq? (case-report-disposition report)
                            'out-of-fragment))
                     reports)
              0)
(check-equal? (length reports) 30)
(check-equal? (length fence-reports) 27)
(define fence-17-report
  (findf (lambda (report)
           (and (string=? (fence-report-source report) "samples.md")
                (= (fence-report-ordinal report) 17)))
         fence-reports))
(check-equal? (length (fence-report-cases fence-17-report)) 2)
(check-equal? (fence-report-disposition fence-17-report)
              'in-fragment/matched)

;; Fence aggregation is deterministic and preserves a failing case over a
;; report-only case regardless of traversal order.
(define report-unresolved
  (case-report "s" 1 1 'unresolved #f '() '() "gap" #f #f))
(define report-implementation
  (case-report "s" 1 2 'in-fragment/no-lowering 'implementation
               '() '() "bug" #f #f))
(check-equal?
 (aggregate-fence-disposition (list report-unresolved report-implementation))
 'in-fragment/no-lowering)
(check-equal?
 (aggregate-fence-disposition (list report-implementation report-unresolved))
 'in-fragment/no-lowering)
(check-true (no-lowering-fails? 'rr-missing '(force) '()))
(check-true (no-lowering-fails? 'implementation "bug" '()))
(check-false (no-lowering-fails? 'rule-underspecified "gap" '()))
(check-false (no-lowering-fails? 'row-missing '(skicu) '(gerku)))
(check-true (no-lowering-fails? 'row-missing '(skicu) '(gerku skicu)))

(define-values (generated-status _generated-attempts _generated-detail)
  (generated-redex-check 1))
(check-not-false (member generated-status '(passed unavailable)))

(define-values (parse-for-missing _rr-for-missing) (case-input "samples.md" 1))
(define missing-result (lower parse-for-missing (hash 'parse '(fixture 1))))
(check-true (no-lowering? missing-result))
(check-equal? (no-lowering-cause missing-result) 'rr-missing)
(check-not-false (member 'rows (no-lowering-detail missing-result)))

;; Input mutations must affect or block lowering: neither parse structure nor
;; RR fields are decorative fixture metadata.
(define-values (sample-1-parse sample-1-rr) (case-input "samples.md" 1))
(define sample-1-assert (lower sample-1-parse sample-1-rr))
(define sample-1-mention-rr
  (struct-copy rr-case sample-1-rr
               [fields (hash-set (rr-case-fields sample-1-rr)
                                 'force '(mention))]))
(define sample-1-mention (lower sample-1-parse sample-1-mention-rr))
(check-true (lowered? sample-1-assert))
(check-true (lowered? sample-1-mention))
(when (and (lowered? sample-1-assert) (lowered? sample-1-mention))
  (check-equal? (first (plain (lowered-term sample-1-assert))) 'Assert)
  (check-equal? (first (plain (lowered-term sample-1-mention))) 'Mention))

(define (rr-with rr . updates)
  (struct-copy
   rr-case rr
   [fields
    (for/fold ([fields (rr-case-fields rr)])
              ([entry (in-list updates)])
      (hash-set fields (car entry) (cdr entry)))]))

(define (check-mention-force source ordinal [index 1])
  (define-values (parse-case rr) (case-input source ordinal index))
  (define result (lower parse-case (rr-with rr (cons 'force '(mention)))))
  (check-true (lowered? result)
              (format "~a#~a.~a accepts Mention force" source ordinal index))
  (when (lowered? result)
    (define symbols (flatten (plain (lowered-term result))))
    (check-not-false (member 'Mention symbols))
    (check-false (member 'Assert symbols))))

;; Every sentence-category special path consumes RR.force; none retains an
;; example-specific Assert.
(check-mention-force "samples.md" 46)   ; termset
(check-mention-force "samples.md" 48)   ; many threshold
(check-mention-force "samples.md" 59)   ; scalar
(check-mention-force "samples.md" 63 1) ; grade
(check-mention-force "samples.md" 63 3) ; co'e

;; L5.2's frozen case is Content. Reclassifying that same parse as a sentence
;; exercises the general sentence consumer without adding a corpus fixture.
(define-values (cardinal-content-parse cardinal-content-rr)
  (case-input "spec.md" 9))
(define cardinal-sentence-result
  (lower (hash-set cardinal-content-parse 'category "sentence")
         (rr-with cardinal-content-rr
                  (cons 'readings '(actual witness-set))
                  (cons 'force '(mention)))))
(check-true (lowered? cardinal-sentence-result))
(when (lowered? cardinal-sentence-result)
  (check-not-false
   (member 'Mention (flatten (plain (lowered-term cardinal-sentence-result))))))
(define cardinal-content-with-force
  (lower cardinal-content-parse
         (rr-with cardinal-content-rr (cons 'force '(assert)))))
(check-true (no-lowering? cardinal-content-with-force))
(check-equal? (no-lowering-cause cardinal-content-with-force) 'rr-missing)

(define capable-result
  (lower sample-1-parse
         (rr-with sample-1-rr (cons 'readings '(capable)))))
(check-true (no-lowering? capable-result))
(check-equal? (no-lowering-cause capable-result) 'rr-missing)
(define unused-attach-result
  (lower sample-1-parse
         (rr-with sample-1-rr (cons 'attach '(unconsumed)))))
(check-true (no-lowering? unused-attach-result))
(check-equal? (no-lowering-cause unused-attach-result) 'rr-missing)

(define-values (description-row-parse description-row-rr)
  (case-input "samples.md" 19))
(define missing-restrictor-row
  (lower description-row-parse
         (rr-with description-row-rr (cons 'rows '(blabi)))))
(check-true (no-lowering? missing-restrictor-row))
(check-equal? (no-lowering-cause missing-restrictor-row) 'rr-missing)

(define-values (grade-parse grade-rr) (case-input "samples.md" 63 1))
(define bogus-grade-sites
  (lower grade-parse
         (rr-with grade-rr
                  (cons 'sites '((bogus barda (deps ())))))))
(check-true (no-lowering? bogus-grade-sites))
(check-equal? (no-lowering-cause bogus-grade-sites) 'rr-missing)

;; Candidate-visible semantic gaps are reported only after their declared RR
;; inputs validate. Malformed global-reading data is rr-missing, never the same
;; non-failing gap result as a valid but unsupported reading.
(for ([mutation
       (in-list
        (list (rr-with spec-10-rr (cons 'sites '()))
              (rr-with spec-10-rr (cons 'attach '(unconsumed)))
              (rr-with spec-10-rr
                       (cons 'readings '(global-exact extra)))))] )
  (define result (lower spec-10-parse mutation))
  (check-true (no-lowering? result))
  (check-equal? (no-lowering-cause result) 'rr-missing))

(define (rename-json-key value old new)
  (cond
    [(hash? value)
     (for/hasheq ([(key child) (in-hash value)])
       (values (if (eq? key old) new key)
               (rename-json-key child old new)))]
    [(list? value) (map (lambda (child) (rename-json-key child old new)) value)]
    [else value]))

(define (rename-json-text value old new)
  (cond
    [(hash? value)
     (for/hasheq ([(key child) (in-hash value)])
       (values key (rename-json-text child old new)))]
    [(list? value) (map (lambda (child) (rename-json-text child old new)) value)]
    [(and (string? value) (string=? value old)) new]
    [else value]))

(define (update-first-json-tag value wanted update)
  (define changed? #f)
  (define (walk node)
    (cond
      [(hash? node)
       (for/hasheq ([(key child) (in-hash node)])
         (cond
           [(and (not changed?) (eq? key wanted))
            (set! changed? #t)
            (values key (update child))]
           [else (values key (walk child))]))]
      [(list? node) (map walk node)]
      [else node]))
  (define result (walk value))
  (unless changed? (error 'update-first-json-tag "tag not found: ~a" wanted))
  result)

(define (synthetic-terminal kind text [start 0])
  (hasheq kind (hasheq 'phonemes text 'span (list start (add1 start)))))

(define (synthetic-pro text [start 0])
  (hasheq 'ConnectedTerm
          (hasheq 'ProSumti (synthetic-terminal 'Cmavo text start))))

(define synthetic-mi (synthetic-pro "mi"))
(define synthetic-do (synthetic-pro "do" 12))
(define synthetic-ti (synthetic-pro "ti"))
(define synthetic-zio (synthetic-pro "zi'o" 10))
(define synthetic-zio-2 (synthetic-pro "zi'o" 11))
(define synthetic-fa-mi
  (hasheq
   'ConnectedTerm
   (hasheq 'PlaceTaggedSumtiTerm
           (hasheq 'fa (synthetic-terminal 'Cmavo "fa")
                   'sumti (hasheq 'ProSumti
                                  (synthetic-terminal 'Cmavo "mi"))))))
(define synthetic-fe-ti
  (hasheq
   'ConnectedTerm
   (hasheq 'PlaceTaggedSumtiTerm
           (hasheq 'fa (synthetic-terminal 'Cmavo "fe" 13)
                   'sumti (hasheq 'ProSumti
                                  (synthetic-terminal 'Cmavo "ti" 14))))))

;; Increment-2 structural lead classifier: one minimal positive per exhaustive
;; rule id, with locus-sensitive connectives and no reliance on citations.
(define (lead-cmavo word [start 20])
  (synthetic-terminal 'Cmavo word start))
(define (minimal-description gadri #:quantifier [quantifier #f]
                             #:possessor? [possessor? #f])
  (hasheq
   'DescriptorWithGadriSumti
   (hasheq
    'description (lead-cmavo gadri)
    'tail
    (hasheq
     'leading_tail_elements
     (if possessor? (hasheq 'tail_sumti (synthetic-pro "mi" 21)) #hasheq())
     'tail
     (hasheq
      (if quantifier 'QuantifierRelationDescriptionTail
          'RelationDescriptionTail)
      (if quantifier
          (hasheq 'quantifier
                  (hasheq 'PaRunQuantifier (lead-cmavo quantifier 22)))
          #hasheq()))))))

(define structural-lead-positives
  (list
   (cons "L1.7" (lead-cmavo "fi'a"))
   (cons "L3.10" (minimal-description "lo" #:quantifier "no"))
   (cons "L3.11" (minimal-description "le" #:possessor? #t))
   (cons "L3.12" (minimal-description "lei"))
   (cons "L3.13" (minimal-description "lai"))
   (cons "L5.4" (lead-cmavo "da'a"))
   (cons "L5.5" (lead-cmavo "bu'a"))
   (cons "L5.6" (lead-cmavo "cei"))
   (cons "L5.10" (lead-cmavo "ja'a"))
   (cons "L5.13"
         (hasheq 'IStatementConnection
                 (hasheq 'JoiConnective (lead-cmavo "joi"))))
   (cons "L5.15"
         (hasheq 'IStatementConnection (lead-cmavo "bo")))
   (cons "L5.16"
         (hasheq 'CoSelbri
                 (hasheq 'JekConnective (lead-cmavo "je"))))
   (cons "L5.17"
         (hasheq 'CoSelbri
                 (hasheq 'JoiConnective (lead-cmavo "joi"))))
   (cons "L5.19" (lead-cmavo "bi'o"))
   (cons "L5.22" (hasheq 'JoiConnective (lead-cmavo "joi")))
   (cons "L5.23"
         (hasheq 'chain
                 (list (hasheq 'JoiConnective (lead-cmavo "joi" 23))
                       (hasheq 'JoiConnective (lead-cmavo "joi" 24)))))
   (cons "L5.27" (lead-cmavo "ku'a"))))
(define increment-2-rule-ids
  '("L1.7" "L3.10" "L3.11" "L3.12" "L3.13"
    "L5.4" "L5.5" "L5.6" "L5.10" "L5.13" "L5.15" "L5.16"
    "L5.17" "L5.19" "L5.22" "L5.23" "L5.27"))
(check-equal? (sort (map car structural-lead-positives) string<?)
              (sort increment-2-rule-ids string<?))
(for ([entry (in-list structural-lead-positives)])
  (check-not-false
   (member (car entry) (structural-rule-leads (cdr entry)))
   (format "classifier positive for ~a" (car entry))))

;; Wrong loci and quoted material do not become structural leads.
(define i-jek
  (hasheq 'IStatementConnection
          (hasheq 'JekConnective (lead-cmavo "je" 25))))
(check-false (member "L5.16" (structural-rule-leads i-jek)))
(define i-joi
  (hasheq 'IStatementConnection
          (hasheq 'JoiConnective (lead-cmavo "joi" 26))))
(check-false (member "L5.17" (structural-rule-leads i-joi)))
(check-false (member "L5.22" (structural-rule-leads i-joi)))
(check-false (member "L5.15" (structural-rule-leads (lead-cmavo "bo" 27))))
(for ([entry (in-list structural-lead-positives)])
  (define quoted
    (hasheq 'QuotedSumti (hasheq 'TextQuote (cdr entry))))
  (check-false
   (member (car entry) (structural-rule-leads quoted))
   (format "quoted classifier negative for ~a" (car entry))))
(define se-joi
  (hasheq 'sumti
          (hasheq 'JoiConnective
                  (list (lead-cmavo "se" 29)
                        (lead-cmavo "joi" 30)))))
(check-not-false (member "L5.23" (structural-rule-leads se-joi)))

(define real-jbotci
  (or (find-executable-path "jbotci")
      (error 'lower-test "jbotci is required for real-parse regressions")))
(define (real-parse text)
  (define out (open-output-string))
  (define err (open-output-string))
  (define ok?
    (parameterize ([current-output-port out]
                   [current-error-port err])
      (system* real-jbotci "gentufa" "--format" "json" text)))
  (unless ok?
    (error 'lower-test "gentufa failed for ~s: ~a" text
           (get-output-string err)))
  (call-with-input-string (get-output-string out) read-json))
(define (real-leads text)
  (structural-rule-leads (real-parse text)))

(check-false (member "L3.10" (real-leads "lu lo no prenu cu jmaji li'u")))
(check-false (member "L5.22" (real-leads "lu mi joi do li'u")))
(check-false (member "L5.23" (real-leads "se klama mi .i mi joi do")))
(check-false (member "L5.23" (real-leads "mi joi do .i ti joi ta")))
(check-false
 (member "L5.23"
         (real-leads "mi tavla fe do joi ti fi ta joi tu")))
(check-not-false (member "L5.23" (real-leads "mi joi do joi ti")))
(check-not-false (member "L3.11" (real-leads "lo nu ta du lo mi zdani")))

;; The probe's exception boundary classifies only parser failures. A defect in
;; any post-parse stage must escape and fail the probe instead of weakening an
;; absence claim through a false parse-error record.
(check-equal?
 (call-with-probe-parse
  (lambda () (error 'parser "synthetic parse failure"))
  (lambda (_) 'parse-error)
  (lambda (_) 'parsed))
 'parse-error)
(check-exn
 #rx"synthetic post-parse failure"
 (lambda ()
   (call-with-probe-parse
    (lambda () #hasheq())
    (lambda (_) 'parse-error)
    (lambda (_) (error 'skeleton "synthetic post-parse failure")))))

;; A handled bridi must account for every direct semantic term. Adding a
;; second term beside the formerly sole description is refused, not silently
;; converted to a tavla/blabi application with the description erased.
(define nonsole-description-parse
  (hash-set
   description-row-parse 'parse
   (update-first-json-tag
    (hash-ref description-row-parse 'parse) 'SelbriSimpleBridiTail
    (lambda (tail)
      (hash-set tail 'terms
                (append (hash-ref tail 'terms (lambda () '()))
                        (list synthetic-mi)))))))
(define nonsole-description-sigma
  (parse-case->sigma nonsole-description-parse
                     (rr-case-fields description-row-rr)))
(check-true (no-lowering? nonsole-description-sigma))
(check-equal? (no-lowering-cause nonsole-description-sigma)
              'rule-underspecified)

;; Recursive descendant search may not substitute a possessor or relative
;; clause for its containing description.
(define possessive-description-parse
  (hash-set
   description-row-parse 'parse
   (update-first-json-tag
    (hash-ref description-row-parse 'parse) 'DescriptorWithGadriSumti
    (lambda (descriptor)
      (hash-update
       descriptor 'tail
       (lambda (tail)
         (hash-set tail 'leading_tail_elements
                   (hasheq 'tail_sumti
                           (hasheq 'ProSumti
                                   (synthetic-terminal 'Cmavo "mi"))))))))))
(define possessive-description-sigma
  (parse-case->sigma possessive-description-parse
                     (rr-case-fields description-row-rr)))
(check-true (no-lowering? possessive-description-sigma))
(check-equal? (no-lowering-rule possessive-description-sigma) "L3.11")

(define relative-description-parse
  (hash-set
   description-row-parse 'parse
   (update-first-json-tag
    (hash-ref description-row-parse 'parse) 'DescriptorWithGadriSumti
    (lambda (descriptor)
      (hash-set descriptor 'probe-relative
                (hasheq 'RestrictiveBridiRelativeClause
                        (synthetic-terminal 'Cmavo "poi")))))))
(define relative-description-sigma
  (parse-case->sigma relative-description-parse
                     (rr-case-fields description-row-rr)))
(check-true (no-lowering? relative-description-sigma))
(check-equal? (no-lowering-cause relative-description-sigma)
              'out-of-fragment)

(define (add-inner-count parse-case word)
  (hash-set
   parse-case 'parse
   (update-first-json-tag
    (hash-ref parse-case 'parse) 'DescriptorWithGadriSumti
    (lambda (descriptor)
      (hash-update
       descriptor 'tail
       (lambda (tail)
         (define relation-node
           (hash-ref (hash-ref tail 'tail) 'RelationDescriptionTail))
         (hash-set
          tail 'tail
          (hasheq
           'QuantifierRelationDescriptionTail
           (hash-set
            relation-node 'quantifier
            (hasheq 'PaRunQuantifier
                    (hasheq 'number
                            (hasheq 'first_number
                                    (synthetic-terminal 'Cmavo word 15)))))))))))))

;; Inner PA is computed by sumti-view and therefore must either contribute a
;; selection or block the path. Ordinary descriptions and collections do not
;; currently compose it, so both refuse instead of becoming uncounted.
(define-values (le-parse le-rr) (case-input "samples.md" 22))
(define counted-le-sigma
  (parse-case->sigma (add-inner-count le-parse "ci")
                     (rr-case-fields le-rr)))
(check-true (no-lowering? counted-le-sigma))
(check-equal? (no-lowering-rule counted-le-sigma) "L3.9")
(define no-le-sigma
  (parse-case->sigma (add-inner-count le-parse "no")
                     (rr-case-fields le-rr)))
(check-true (no-lowering? no-le-sigma))
(check-equal? (no-lowering-rule no-le-sigma) "L3.10")

(define explicit-zero-lo-result
  (lower (add-inner-count description-row-parse "no") description-row-rr))
(check-true (lowered? explicit-zero-lo-result))
(when (lowered? explicit-zero-lo-result)
  (check-true
   (redex-alpha-equivalent?
    (plain (lowered-term explicit-zero-lo-result))
    '(Assert
      (No (λ ($x :: Entity) (mlatu $x))
          (λ ($w :: Referents Entity) (Close (blabi $w))))))))

(define-values (collection-parse collection-rr)
  (case-input "samples.md" 30))
(define counted-collection-sigma
  (parse-case->sigma (add-inner-count collection-parse "ci")
                     (rr-case-fields collection-rr)))
(check-true (no-lowering? counted-collection-sigma))
(check-equal? (no-lowering-rule counted-collection-sigma) "L3.9")

;; Place labels are routed through conversion before application. Surface fa
;; under se is base x2, even when it is the only fill.
(define-values (conversion-parse conversion-rr) (case-input "samples.md" 5))
(define se-fa-parse
  (hash-set
   conversion-parse 'parse
   (update-first-json-tag
    (hash-ref conversion-parse 'parse) 'BridiWithLeadingTerms
    (lambda (bridi)
      (hash-set
       (hash-set bridi 'leading_terms (list synthetic-fa-mi))
       'bridi_tail
       (update-first-json-tag
        (hash-ref bridi 'bridi_tail) 'SelbriSimpleBridiTail
        (lambda (tail) (hash-set tail 'terms '()))))))))
(check-equal?
 (parse-case->sigma se-fa-parse (rr-case-fields conversion-rr))
 '(force assert
    (close shorthand
           (omit (route (application klama :2 Speaker))))))

;; Every zi'o remains a distinct DropPlace and later positional terms advance
;; past both deleted labels.
(define-values (deletion-parse deletion-rr) (case-input "samples.md" 4))
(define repeated-deletion-parse
  (hash-set
   deletion-parse 'parse
   (update-first-json-tag
    (hash-ref deletion-parse 'parse) 'SelbriSimpleBridiTail
    (lambda (tail)
      (hash-set tail 'terms
                (list synthetic-zio synthetic-zio-2 synthetic-ti))))))
(check-equal?
 (parse-case->sigma repeated-deletion-parse (rr-case-fields deletion-rr))
 '(force assert
    (close shorthand
           (omit (drop klama (2 3) Speaker This)))))

(define-values (tanru-parse tanru-rr) (case-input "samples.md" 58))
(define (tanru-with-terms leading trailing)
  (hash-set
   tanru-parse 'parse
   (update-first-json-tag
    (hash-ref tanru-parse 'parse) 'BridiWithLeadingTerms
    (lambda (bridi)
      (hash-set
       (hash-set bridi 'leading_terms leading)
       'bridi_tail
       (update-first-json-tag
        (hash-ref bridi 'bridi_tail) 'SelbriSimpleBridiTail
        (lambda (tail) (hash-set tail 'terms trailing))))))))

;; A tanru former may not disappear behind the routing/deletion branches.
;; These combinations are not implemented, so the complete view is refused.
(define tanru-fa-sigma
  (parse-case->sigma (tanru-with-terms (list synthetic-fe-ti) '())
                     (rr-case-fields tanru-rr)))
(check-true (no-lowering? tanru-fa-sigma))
(check-equal? (no-lowering-rule tanru-fa-sigma) "L1.10")

(define tanru-delete-sigma
  (parse-case->sigma (tanru-with-terms (list synthetic-mi)
                                      (list synthetic-zio))
                     (rr-case-fields tanru-rr)))
(check-true (no-lowering? tanru-delete-sigma))
(check-equal? (no-lowering-rule tanru-delete-sigma) "L1.10")

(define tanru-converted-parse
  (hash-set
   (tanru-with-terms (list synthetic-mi) (list synthetic-do)) 'parse
   (update-first-json-tag
    (hash-ref (tanru-with-terms (list synthetic-mi) (list synthetic-do))
              'parse)
    'SelbriSimpleBridiTail
    (lambda (tail)
      (hash-update
       tail 'selbri
       (lambda (selbri)
         (hash-set selbri 'conversions
                   (list (synthetic-terminal 'Cmavo "se" 16)))))))))
(define tanru-converted-sigma
  (parse-case->sigma tanru-converted-parse (rr-case-fields tanru-rr)))
(check-true (no-lowering? tanru-converted-sigma))
(check-equal? (no-lowering-rule tanru-converted-sigma) "L1.10")

(define bogus-parse
  (hash-set sample-1-parse 'parse
            (rename-json-key (hash-ref sample-1-parse 'parse)
                             'BridiStatement 'BogusStatement)))
(define bogus-result (lower bogus-parse sample-1-rr))
(check-true (no-lowering? bogus-result))

(define-values (tagged-parse tagged-rr) (case-input "samples.md" 3))
(define unknown-tag-wrapper-parse
  (hash-set tagged-parse 'parse
            (rename-json-key (hash-ref tagged-parse 'parse)
                             'PlaceTaggedSumtiTerm
                             'UnknownTermWrapper)))
(define unknown-tag-wrapper-result
  (lower unknown-tag-wrapper-parse tagged-rr))
(check-true (no-lowering? unknown-tag-wrapper-result))
(check-equal? (no-lowering-cause unknown-tag-wrapper-result)
              'rule-underspecified)

(define-values (zip-parse zip-rr) (case-input "spec.md" 19))
(define unknown-joi-wrapper-result
  (lower
   (hash-set zip-parse 'parse
             (rename-json-key (hash-ref zip-parse 'parse)
                              'JoikConnective 'UnknownJoiWrapper))
   zip-rr))
(check-true (no-lowering? unknown-joi-wrapper-result))
(check-equal? (no-lowering-cause unknown-joi-wrapper-result)
              'rule-underspecified)

(define unknown-selbri-wrapper-result
  (lower
   (hash-set sample-1-parse 'parse
             (rename-json-key (hash-ref sample-1-parse 'parse)
                              'WordTanruUnit 'UnknownSelbriWrapper))
   sample-1-rr))
(check-true (no-lowering? unknown-selbri-wrapper-result))
(check-equal? (no-lowering-cause unknown-selbri-wrapper-result)
              'rule-underspecified)

(define unknown-descriptor-child-result
  (lower
   (hash-set
    description-row-parse 'parse
    (update-first-json-tag
     (hash-ref description-row-parse 'parse) 'DescriptorWithGadriSumti
     (lambda (descriptor)
       (rename-json-key descriptor 'WordTanruUnit
                        'UnknownDescriptorLexicalWrapper))))
   description-row-rr))
(check-true (no-lowering? unknown-descriptor-child-result))
(check-equal? (no-lowering-cause unknown-descriptor-child-result)
              'rule-underspecified)

(define unknown-fahu-operand-result
  (lower
   (hash-set zip-parse 'parse
             (rename-json-key (hash-ref zip-parse 'parse)
                              'SimpleSumti 'UnknownFahuOperandWrapper))
   zip-rr))
(check-true (no-lowering? unknown-fahu-operand-result))
(check-equal? (no-lowering-cause unknown-fahu-operand-result)
              'rule-underspecified)

;; Fresh child values flow through the recursive decoder; the wrapper sweeps
;; establish refusal, while these probes establish non-fixture value transport.
(define descriptor-value-flow-result
  (lower
   (hash-set description-row-parse 'parse
             (rename-json-text (hash-ref description-row-parse 'parse)
                               "mlátu" "gérku"))
   (rr-with description-row-rr (cons 'rows '(gerku blabi)))))
(check-true (lowered? descriptor-value-flow-result))
(when (lowered? descriptor-value-flow-result)
  (check-true
   (redex-alpha-equivalent?
    (plain (lowered-term descriptor-value-flow-result))
    '(Bind ($referent :: Referents Entity)
           (Refer (λ ($unit :: Referents Entity) (gerku $unit)))
       (Assert (Close (blabi $referent)))))))

(define (rename-terminal-at-start value start replacement)
  (cond
    [(hash? value)
     (define terminal?
       (and (hash-has-key? value 'phonemes)
            (equal? (hash-ref value 'span #f)
                    (list start (+ start 2)))))
     (for/hasheq ([(key child) (in-hash value)])
       (values key
               (cond [(and terminal? (eq? key 'phonemes)) replacement]
                     [else (rename-terminal-at-start child start replacement)])))]
    [(list? value)
     (map (lambda (child)
            (rename-terminal-at-start child start replacement)) value)]
    [else value]))

(define fahu-value-flow-result
  (lower
   (hash-set zip-parse 'parse
             (rename-terminal-at-start (hash-ref zip-parse 'parse) 0 "ti"))
   zip-rr))
(check-true (lowered? fahu-value-flow-result))
(when (lowered? fahu-value-flow-result)
  (check-true
   (redex-alpha-equivalent?
    (plain (lowered-term fahu-value-flow-result))
    '(ZipWith
      (λ ($speaker $listener :: Referents Entity)
        (Close (tavla $speaker $listener)))
      (List This Audience)
      (List Audience Speaker)))))

;; M4 increment 1: unseen rows/arity and the complete L0.1 dependency graph.
(define (replace-parse-strings parse-case replacements)
  (hash-set
   parse-case 'parse
   (for/fold ([raw (hash-ref parse-case 'parse)])
             ([replacement (in-list replacements)])
     (rename-json-text raw (car replacement) (cdr replacement)))))

(define unseen-global-parse
  (replace-parse-strings
   spec-10-parse
   (list (cons "ci" "re")
         (cons "gérku" "prénu")
         (cons "bájra" "kláma"))))
(define unseen-global-rr
  (rr-with
   spec-10-rr
   (cons 'rows '(prenu klama))
   (cons 'sites
         '((omit nuclear-klama-2 (deps ()))
           (omit nuclear-klama-3 (deps ()))
           (omit nuclear-klama-4 (deps ()))
           (omit nuclear-klama-5 (deps ()))))))
(define unseen-global-result (lower unseen-global-parse unseen-global-rr))
(check-true (lowered? unseen-global-result))
(when (lowered? unseen-global-result)
  (define datum (plain (lowered-term unseen-global-result)))
  (check-equal? (count (lambda (item) (eq? item 'Context)) (flatten datum)) 4)
  (check-not-false (member 2 (flatten datum)))
  (check-not-false (member 'GlobalExactly (flatten datum))))

;; A multi-place restrictor and nuclear predicate both contribute hoisted
;; sites; neither operand receives privileged treatment.
(define multi-restrictor-parse
  (replace-parse-strings spec-10-parse (list (cons "gérku" "kláma"))))
(define multi-restrictor-rr
  (rr-with
   spec-10-rr
   (cons 'rows '(klama bajra))
   (cons 'sites
         '((omit restrictor-klama-2 (deps ()))
           (omit restrictor-klama-3 (deps ()))
           (omit restrictor-klama-4 (deps ()))
           (omit restrictor-klama-5 (deps ()))
           (omit nuclear-bajra-2 (deps ()))
           (omit nuclear-bajra-3 (deps ()))
           (omit nuclear-bajra-4 (deps ()))))))
(define multi-restrictor-result
  (lower multi-restrictor-parse multi-restrictor-rr))
(check-true (lowered? multi-restrictor-result))
(when (lowered? multi-restrictor-result)
  (check-equal?
   (count (lambda (item) (eq? item 'Context))
          (flatten (plain (lowered-term multi-restrictor-result))))
   7))

;; Role qualification keeps two occurrences of the same row distinct.
(define same-row-global-parse
  (replace-parse-strings
   spec-10-parse
   (list (cons "gérku" "kláma") (cons "bájra" "kláma"))))
(define same-row-global-rr
  (rr-with
   spec-10-rr
   (cons 'rows '(klama))
   (cons 'sites
         '((omit restrictor-klama-2 (deps ()))
           (omit restrictor-klama-3 (deps ()))
           (omit restrictor-klama-4 (deps ()))
           (omit restrictor-klama-5 (deps ()))
           (omit nuclear-klama-2 (deps ()))
           (omit nuclear-klama-3 (deps ()))
           (omit nuclear-klama-4 (deps ()))
           (omit nuclear-klama-5 (deps ()))))))
(define same-row-global-result
  (lower same-row-global-parse same-row-global-rr))
(check-true (lowered? same-row-global-result))
(when (lowered? same-row-global-result)
  (check-equal?
   (count (lambda (item) (eq? item 'Context))
          (flatten (plain (lowered-term same-row-global-result))))
   8))

;; Dependency order is topological, with declaration order breaking ties, and
;; the dependent Context computation names the already-bound value.
(define dependent-global-rr
  (rr-with
   spec-10-rr
   (cons 'sites
         '((omit nuclear-bajra-3 (deps (nuclear-bajra-2)))
           (omit nuclear-bajra-2 (deps ()))
           (omit nuclear-bajra-4 (deps ()))))))
(define dependent-global-result (lower spec-10-parse dependent-global-rr))
(check-true (lowered? dependent-global-result))
(when (lowered? dependent-global-result)
  (match (plain (lowered-term dependent-global-result))
    [`(Bind (,first-var :: Referents Entity) (Context)
            (,second-var :: Referents Entity) (Context ,dependency)
            (,_third-var :: Referents Entity) (Context)
        ,_body)
     (check-equal? first-var '$nuclear_bajra_2)
     (check-equal? second-var '$nuclear_bajra_3)
     (check-equal? dependency first-var)]
    [other (fail-check (format "unexpected dependent hoist: ~e" other))]))

(define invalid-global-site-lists
  (list
   '((omit nuclear-bajra-2 (deps ((member nuclear))))
     (omit nuclear-bajra-3 (deps ()))
     (omit nuclear-bajra-4 (deps ())))
   '((omit nuclear-bajra-2 (deps (missing-site)))
     (omit nuclear-bajra-3 (deps ()))
     (omit nuclear-bajra-4 (deps ())))
   '((omit nuclear-bajra-2 (deps (nuclear-bajra-3)))
     (omit nuclear-bajra-3 (deps (nuclear-bajra-2)))
     (omit nuclear-bajra-4 (deps ())))
   '((omit nuclear-bajra-2 (deps ()))
     (omit nuclear-bajra-2 (deps ()))
     (omit nuclear-bajra-4 (deps ())))
   '((omit nuclear-bajra-2 (deps ()))
     (omit nuclear-bajra-3 (deps ()))
     (omit nuclear-bajra-4 (deps ()))
     (omit unknown-9 (deps ())))))
(for ([sites (in-list invalid-global-site-lists)])
  (define result
    (lower spec-10-parse (rr-with spec-10-rr (cons 'sites sites))))
  (check-true (no-lowering? result))
  (check-equal? (no-lowering-cause result) 'rr-missing))

;; Outer binders are a separate namespace from comprehension members. The
;; reading is semantically licensed but environment threading is deferred, so
;; it reports an honest rule gap rather than member-dependent ill-formation.
(define outer-dependent-global
  (lower
   spec-10-parse
   (rr-with
    spec-10-rr
    (cons 'sites
          '((omit nuclear-bajra-2 (deps ((outer $topic))))
            (omit nuclear-bajra-3 (deps ()))
            (omit nuclear-bajra-4 (deps ())))))))
(check-true (no-lowering? outer-dependent-global))
(check-equal? (no-lowering-cause outer-dependent-global)
              'rule-underspecified)
(define ambiguous-bare-variable-dependency
  (lower
   spec-10-parse
   (rr-with
    spec-10-rr
    (cons 'sites
          '((omit nuclear-bajra-2 (deps ($topic)))
            (omit nuclear-bajra-3 (deps ()))
            (omit nuclear-bajra-4 (deps ())))))))
(check-true (no-lowering? ambiguous-bare-variable-dependency))
(check-equal? (no-lowering-cause ambiguous-bare-variable-dependency)
              'rr-missing)

(define-values (termset-parse termset-rr) (case-input "samples.md" 46))
(define unknown-termset-wrapper-result
  (lower
   (hash-set termset-parse 'parse
             (rename-json-key (hash-ref termset-parse 'parse)
                              'continuations 'UnknownTermsetWrapper))
   termset-rr))
(check-true (no-lowering? unknown-termset-wrapper-result))
(check-equal? (no-lowering-cause unknown-termset-wrapper-result)
              'rule-underspecified)

(define-values (connection-parse connection-rr) (case-input "samples.md" 17))
(define unknown-connection-wrapper-result
  (lower
   (hash-set connection-parse 'parse
             (rename-json-key (hash-ref connection-parse 'parse)
                              'IStandardStatementConnective
                              'UnknownConnectionWrapper))
   connection-rr))
(check-true (no-lowering? unknown-connection-wrapper-result))
(check-equal? (no-lowering-cause unknown-connection-wrapper-result)
              'rule-underspecified)

(define-values (fragment-parse fragment-rr) (case-input "samples.md" 30))
(define unknown-fragment-wrapper-result
  (lower
   (hash-set fragment-parse 'parse
             (rename-json-key (hash-ref fragment-parse 'parse)
                              'ConnectedTerm 'UnknownFragmentTermWrapper))
   fragment-rr))
(check-true (no-lowering? unknown-fragment-wrapper-result))
(check-equal? (no-lowering-cause unknown-fragment-wrapper-result)
              'rule-underspecified)

;; The mechanism is not restricted to the frozen surface corpus: a lexical
;; terminal never seen at this tree position flows through the same construct
;; translation, with its independently selected RR row.
(define unseen-lexical-parse
  (hash-set*
   sample-1-parse
   'surface "mi tavla"
   'source_comment "mi tavla"
   'parse (rename-json-text (hash-ref sample-1-parse 'parse)
                            "kláma" "távla")))
(define unseen-lexical-rr
  (struct-copy rr-case sample-1-rr
               [fields (hash-set (rr-case-fields sample-1-rr)
                                 'rows '(tavla))]))
(define unseen-lexical-result (lower unseen-lexical-parse unseen-lexical-rr))
(check-true (lowered? unseen-lexical-result))
(when (lowered? unseen-lexical-result)
  (check-equal? (plain (lowered-term unseen-lexical-result))
                '(Assert (Close (tavla Speaker)))))

(define no-row-rr
  (struct-copy rr-case sample-1-rr
               [fields (hash-set (rr-case-fields sample-1-rr) 'rows '())]))
(define no-row-result (lower sample-1-parse no-row-rr))
(check-true (no-lowering? no-row-result))
(check-equal? (no-lowering-cause no-row-result) 'rr-missing)

(define-values (negative-parse negative-rr) (case-input "samples.md" 16))
(define no-reading-rr
  (struct-copy rr-case negative-rr
               [fields (hash-set (rr-case-fields negative-rr) 'readings '())]))
(check-equal? (no-lowering-cause (lower negative-parse no-reading-rr))
              'rr-missing)

(define-values (cohe-parse cohe-rr) (case-input "samples.md" 63 3))
(define no-sites-rr
  (struct-copy rr-case cohe-rr
               [fields (hash-set (rr-case-fields cohe-rr) 'sites '())]))
(check-equal? (no-lowering-cause (lower cohe-parse no-sites-rr))
              'rr-missing)

(displayln "lowering fixture tests: ok")
