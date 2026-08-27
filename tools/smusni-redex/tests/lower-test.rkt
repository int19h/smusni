#lang racket

(require rackunit
         racket/list
         racket/set
         redex/reduction-semantics
         "../elaborate.rkt"
         "../lower.rkt"
         "../syntax.rkt")

(define manifest (load-lowering-manifest))
(check-equal? (lowering-manifest-families manifest) '("L0" "L1" "L3" "L5"))
(check-equal? (lowering-manifest-rule-count manifest) 46)
(check-equal? (length (lowering-manifest-candidates manifest)) 25)
(check-equal?
 (for/sum ([candidate (in-list (lowering-manifest-candidates manifest))])
   (length (lowering-candidate-cases candidate)))
 28)

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
(check-equal? (length redex-rule-names) 29)
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
(check-false (lowering-case-surface spec-10-case))
(check-true (string-contains? (lowering-case-unresolved spec-10-case)
                              "missing Lojban surface"))
(check-false
 (hash-ref (first (hash-ref (load-parse-fixture spec-10) 'cases)) 'parse))
(check-true
 (string-prefix?
  (hash-ref (first (hash-ref (load-parse-fixture spec-10) 'cases))
            'source_comment)
  "surface/limbs/gait sites"))

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
(check-does-not-lower "samples.md" 58 'rule-underspecified "L1.10")
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
(check-true (no-lowering? spec-10-result))
(check-equal? (no-lowering-cause spec-10-result) 'rule-underspecified)

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
   (m3-lower rr (gentufa parse (pure lexical $x)) e_output)
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

;; Full candidate run: structurally formed cases match; the honest unformed
;; and missing-surface dispositions remain visible/non-failing.
(define-values (gate-ok? reports fence-reports)
  (run-lowering-gate #:print? #f))
(check-true gate-ok?)
(check-equal? (count (lambda (report)
                       (eq? (case-report-disposition report)
                            'in-fragment/matched))
                     reports)
              26)
(check-equal? (count (lambda (report)
                       (eq? (case-report-disposition report) 'unresolved))
                     reports)
              1)
(check-equal? (count (lambda (report)
                       (eq? (case-report-disposition report)
                            'in-fragment/no-lowering))
                     reports)
              1)
(check-equal? (count (lambda (report)
                       (eq? (case-report-disposition report)
                            'out-of-fragment))
                     reports)
              0)
(check-equal? (length reports) 28)
(check-equal? (length fence-reports) 25)
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

(define bogus-parse
  (hash-set sample-1-parse 'parse
            (rename-json-key (hash-ref sample-1-parse 'parse)
                             'BridiStatement 'BogusStatement)))
(define bogus-result (lower bogus-parse sample-1-rr))
(check-true (no-lowering? bogus-result))

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
