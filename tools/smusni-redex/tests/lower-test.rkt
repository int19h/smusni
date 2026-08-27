#lang racket

(require rackunit
         racket/list
         racket/set
         redex/reduction-semantics
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
    (check-equal? (plain (lowered-term result)) expected)
    (for ([rule (in-list rules)])
      (check-not-false
       (member rule (lowered-rules result))
       (format "~a#~a.~a derivation contains ~a; got ~e"
               source ordinal index rule (lowered-rules result))))))

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
              '("L1.10"))
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
 '("L5.9" "L5.8"))
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

;; Full candidate run: all parseable cases match; the one filed missing-surface
;; document defect remains visible and non-failing.
(define-values (gate-ok? reports fence-reports)
  (run-lowering-gate #:print? #f))
(check-true gate-ok?)
(check-equal? (count (lambda (report)
                       (eq? (case-report-disposition report)
                            'in-fragment/matched))
                     reports)
              27)
(check-equal? (count (lambda (report)
                       (eq? (case-report-disposition report) 'unresolved))
                     reports)
              1)
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

(displayln "lowering fixture tests: ok")
