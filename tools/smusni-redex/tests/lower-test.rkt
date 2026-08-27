#lang racket

(require rackunit
         racket/list
         racket/set
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
      (check-not-false (member rule (lowered-rules result))))))

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
          (Context (GroupBasisConstraint lu'o Entity) deps…)
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

(define-values (parse-for-missing _rr-for-missing) (case-input "samples.md" 1))
(define missing-result (lower parse-for-missing (hash 'parse '(fixture 1))))
(check-true (no-lowering? missing-result))
(check-equal? (no-lowering-cause missing-result) 'rr-missing)
(check-not-false (member 'rows (no-lowering-detail missing-result)))

(displayln "lowering fixture tests: ok")
