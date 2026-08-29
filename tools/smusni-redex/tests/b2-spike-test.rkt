#lang racket

(require rackunit
         racket/list
         racket/match
         racket/runtime-path
         racket/set
         redex/reduction-semantics
         "../port-a0.rkt"
         "../port-b2-spike.rkt")

(define (check-round-trip datum)
  (define-values (root count) (b2-compile-term datum))
  (check-equal? (b2-node->datum root) datum)
  (check-equal? count (b2-raw-occurrence-count datum))
  (values root count))

(define-runtime-path b2-profile-path
  "../inventory/b2-representation-spike.sexp")
(check-match
 (call-with-input-file b2-profile-path read)
 `(smusni-b2-representation-spike 1
    (base-head ,(? string?))
    (scope A0-Synth A0-T-Natural A0-T-Top A0-T-Let)
    (cache-controls ,_ ...)
    (identity-micro ,_ ... (result pass))
    (public-compile-and-judge ,_ ... (result pass))
    (disposition ,(? string?))))

;; C3: direct lexical/occurrence coverage beyond the current generator's
;; binder-depth-zero output. The compiler is generic over the complete raw
;; datum tree; execution remains deliberately limited to the four-rule slice.
(define targeted-terms
  '((λ (($x Entity)) (λ (($x Entity)) $x))
    (λ (($x Entity) ($y Entity)) (= $x $y))
    (Let ($alpha0 Entity) Speaker
      (Let ($x Entity) $alpha0 (= $x $alpha0)))
    (Bind (($x (Referents Entity) (Context))
           ($y (Referents Entity) (Context $x)))
      (Among $x $y))
    (∧ (Presuppose (= $x $x) ⊤)
       (Presuppose (= $x $alpha0) ⊤))
    (∧ ⊤ ⊤)
    (Quote (Some P Q))
    (Syntax (AtLeast 2 P Q))))

(for ([datum (in-list targeted-terms)])
  (check-round-trip datum))

;; Shadowing is preserved by opaque environment snapshots and extension.
(define shadow-env
  (b2-compile-env '(($x Entity) ($x Natural) ($free Entity))))
(check-equal? (b2-env->datum shadow-env)
              '(($x Entity) ($x Natural) ($free Entity)))
(check-equal? (b2-env-lookup shadow-env '$x) 'Entity)
(define extended-shadow (b2-env-extend shadow-env '(($x Content) ($y Natural))))
(check-equal? (b2-env-lookup extended-shadow '$x) 'Content)
(check-equal? (b2-env-lookup extended-shadow '$y) 'Natural)
(check-equal? (b2-env->datum extended-shadow)
              '(($x Content) ($y Natural)
                ($x Entity) ($x Natural) ($free Entity)))

;; Equal source subtrees remain distinct occurrences, never globally
;; hash-consed. Quote/Syntax are one opaque node with no traversable children.
(define-values (equal-root equal-count) (check-round-trip '(∧ ⊤ ⊤)))
(define equal-left (b2-node-at-path equal-root '(1)))
(define equal-right (b2-node-at-path equal-root '(2)))
(check-equal? (b2-node->datum equal-left) '⊤)
(check-equal? (b2-node->datum equal-right) '⊤)
(check-false (eq? equal-left equal-right))
(check-false (equal? equal-left equal-right))

(for ([datum (in-list '((Quote (Some P Q))
                         (Syntax (AtLeast 2 P Q))))])
  (define-values (root count) (check-round-trip datum))
  (check-equal? (b2-node-kind root) 'opaque)
  (check-equal? (b2-node-children root) '())
  (check-equal? count 1)
  (check-false (b2-node-at-path root '(1))))

(random-seed 520)
(define generated-terms
  (for/list ([attempt (in-range 160)])
    (generate-term SmusniA0 t 6 #:attempt-num attempt)))
(for ([datum (in-list generated-terms)])
  (check-round-trip datum))

;; R2 descriptors are complete, one-to-one, and mutation-sensitive.
(check-equal? (b2-descriptor-findings) '())
(check-not-equal? (b2-descriptor-findings (rest b2-rule-descriptors)) '())
(check-not-equal?
 (b2-descriptor-findings
  (cons (first b2-rule-descriptors) b2-rule-descriptors))
 '())
(define stale-descriptor
  (struct-copy b2-rule-descriptor (first b2-rule-descriptors)
               [raw-production '(a0-synth Γ ignored R)]))
(check-not-equal?
 (b2-descriptor-findings
  (cons stale-descriptor (rest b2-rule-descriptors)))
 '())

;; R3: execution identities are rejected recursively in every representative
;; container shape, including a derivation projection. Ordinary outputs pass.
(define-values (sentinel-node _) (b2-compile-term '⊤))
(define sentinel-env (b2-compile-env '()))
(check-false
 (b2-execution-identity-free?
  `(typing Natural () (,sentinel-node))))
(check-false
 (b2-execution-identity-free?
  (hash 'manifest (vector (box sentinel-env)))))
(check-false
 (b2-execution-identity-free?
  (b2-proof `(a0-type synth () ⊤ ,sentinel-node) "sentinel" '())))
(check-exn exn:fail?
           (lambda ()
             (b2-assert-no-execution-identities
              `(lowering-output ,sentinel-node))))
(check-true
 (b2-execution-identity-free?
  '(typing Content (projective) ((presuppose ⊤ Content)))))

;; R4/C2/C4: memoization changes neither the relation nor its complete proof
;; projection. The four-rule oracle statements are reconstructed with source
;; binder spellings, avoiding Redex-internal guillemet freshness noise.
(define slice-cases
  '((() 7)
    (() ⊤)
    (() (Let ($x Natural) 1 ⊤))
    (() (Let ($x Number) 1 2))
    (() (Let ($x Content) ⊤ (Let ($y Natural) 2 ⊤)))
    (() (Let ($x Natural) 1
          (Let ($x Natural) 2
            (Let ($y Number) 3 ⊤))))))

(for ([case (in-list slice-cases)])
  (match-define (list environment datum) case)
  (define memo-on (b2-spike-run-synth environment datum #:memo? #t))
  (define memo-off (b2-spike-run-synth environment datum #:memo? #f))
  (check-equal? (b2-spike-run-records memo-on)
                (b2-spike-run-records memo-off))
  (check-equal? (b2-spike-run-proofs memo-on)
                (b2-spike-run-proofs memo-off))
  (check-equal? (b2-spike-run-proofs memo-on)
                (b2-reference-proofs environment datum))
  (check-equal? (b2-spike-run-compile-count memo-on) 1)
  (check-equal? (b2-spike-run-node-count memo-on)
                (b2-raw-occurrence-count datum)))

(define exact-let-run
  (b2-spike-run-synth '() '(Let ($x Natural) 1 ⊤)))
(define exact-let-type-proof
  (first (b2-proof-subs
          (first (b2-spike-run-proofs exact-let-run)))))
(check-equal?
 (b2-proof-statement
  (first (b2-proof-subs exact-let-type-proof)))
 '(a0-type synth () 1 (typing Natural () ())))

;; Zero derivations are ordinary outcomes, never host exceptions.
(define unsupported '(λ (($x Entity)) ⊤))
(check-equal? (b2-spike-run-proofs
               (b2-spike-run-synth '() unsupported #:memo? #t))
              '())
(check-equal? (b2-spike-run-proofs
               (b2-spike-run-synth '() unsupported #:memo? #f))
              '())

;; A test-only ambiguous judgment proves that Redex memoization preserves two
;; derivations rather than deduplicating them. It is not an execution rule.
(define-judgment-form SmusniB2Spike
  #:mode (b2-ambiguity-probe I)
  #:contract (b2-ambiguity-probe N)
  [(side-condition ,(b2-node? (term N)))
   ----------------------------------------------- "B2-Ambiguity-Left"
   (b2-ambiguity-probe N)]
  [(side-condition ,(b2-node? (term N)))
   ----------------------------------------------- "B2-Ambiguity-Right"
   (b2-ambiguity-probe N)])

(define (ambiguity-derivations memo?)
  (parameterize ([caching-enabled? memo?])
    (build-derivations (b2-ambiguity-probe ,sentinel-node))))
(define ambiguity-on (ambiguity-derivations #t))
(define ambiguity-off (ambiguity-derivations #f))
(check-equal? (length ambiguity-on) 2)
(check-equal? (length ambiguity-off) 2)
(check-equal? (sort (map derivation-name ambiguity-on) string<?)
              (sort (map derivation-name ambiguity-off) string<?))

;; Every generated term compiles without a host exception. Memo on/off is
;; observationally identical for successes and failures; supported slice terms
;; additionally equal the raw A0 proof oracle.
(define generated-zero-count 0)
(for ([datum (in-list generated-terms)])
  (define memo-on (b2-spike-run-synth '() datum #:memo? #t))
  (define memo-off (b2-spike-run-synth '() datum #:memo? #f))
  (check-equal? (b2-spike-run-records memo-on)
                (b2-spike-run-records memo-off))
  (check-equal? (b2-spike-run-proofs memo-on)
                (b2-spike-run-proofs memo-off))
  (when (null? (b2-spike-run-proofs memo-on))
    (set! generated-zero-count (add1 generated-zero-count)))
  (when (b2-spike-supported? datum)
    (check-equal? (b2-spike-run-proofs memo-on)
                  (b2-reference-proofs '() datum))))
(check-true (positive? generated-zero-count))

;; R1 and K1/C1 hard stops are executable. Timing begins outside the public raw
;; API; each query compiles once and reports exact occurrence counts.
(define identity-report (run-b2-identity-micro))
(check-true (b2-identity-micro-passed? identity-report))
(define growth-report (run-b2-spike-growth))
(check-true (b2-spike-growth-passed? growth-report))
(check-true
 (andmap (lambda (ratio) (< ratio 4.0))
         (b2-spike-growth-ratios growth-report)))
(for ([depth (in-list (b2-spike-growth-depths growth-report))]
      [nodes (in-list (b2-spike-growth-node-count growth-report))])
  (check-equal? nodes (b2-raw-occurrence-count
                       (for/fold ([body '⊤]) ([index (in-range depth)])
                         `(Let (,(string->symbol
                                  (format "$test_growth_~a" index)) Natural)
                            ,index ,body)))))

(displayln "B2 opaque representation spike: ok")
