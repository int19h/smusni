#lang racket

(require rackunit
         racket/file
         racket/list
         racket/match
         racket/runtime-path
         racket/set
         racket/string
         "../inventory.rkt"
         "../port-phase0.rkt"
         "../syntax.rkt"
         "../types.rkt")

(define-runtime-path live-spec-path "../../../spec.md")

;; P0.1: the live extractor, not a recorded glyph count, supplies the gate's
;; denominator. The current counts are ratchets, while mutation checks prove
;; that a newly added head is detected rather than silently absorbed.
(define observations (extract-definition-observations))
(define definitions (load-definition-ledger))
(check-equal? (length observations) 85)
(check-equal? (apply + (map (compose length definition-observation-lines)
                            observations))
              94)
(check-equal? (length definitions) 85)
(check-equal? (definition-ledger-findings observations definitions) '())
(define added-observation
  (definition-observation 'NewTomorrowDefinition "12" '(9999)
                          '("(NewTomorrowDefinition x)")))
(check-not-false
 (findf (lambda (message)
          (string-contains? message "NewTomorrowDefinition"))
        (definition-ledger-findings (cons added-observation observations)
                                    definitions)))
(define tomorrow-spec (make-temporary-file "smusni-spec-tomorrow-~a.md"))
(dynamic-wind
  (lambda ()
    (call-with-output-file tomorrow-spec
      (lambda (out)
        (display (file->string live-spec-path) out)
        (display "\n(NewTomorrowDefinition x) ≝ x\n" out))
      #:exists 'truncate/replace))
  (lambda ()
    (define tomorrow-observations
      (extract-definition-observations tomorrow-spec))
    (check-not-false
     (findf (lambda (item)
              (eq? (definition-observation-head item)
                   'NewTomorrowDefinition))
            tomorrow-observations))
    (check-not-false
     (findf (lambda (message)
              (string-contains? message "NewTomorrowDefinition"))
            (definition-ledger-findings tomorrow-observations definitions))))
  (lambda () (delete-file tomorrow-spec)))
(define first-definition (first definitions))
(define falsely-executable
  (struct-copy definition-entry first-definition
               [status 'executable] [issue #f] [port-state 'ported]
               [implementations '()]))
(check-not-false
 (findf (lambda (message) (string-contains? message "names no implementing"))
        (definition-ledger-findings
         observations (cons falsely-executable (rest definitions)))))
(define falsely-implemented
  (struct-copy definition-entry first-definition
               [status 'executable] [issue #f] [port-state 'ported]
               [implementations '((metafunction missing-definition
                                    (cases missing-case)))]))
(check-not-false
 (findf (lambda (message) (string-contains? message "missing implementation"))
        (definition-ledger-findings
         observations (cons falsely-implemented (rest definitions)))))
(check-equal? (count (lambda (entry)
                       (eq? (definition-entry-status entry) 'executable))
                     definitions)
              75)
(check-equal? (count (lambda (entry)
                       (eq? (definition-entry-port-state entry) 'none))
                     definitions)
              83)
(check-equal? (count (lambda (entry)
                       (eq? (definition-entry-port-state entry) 'legacy-hybrid))
                     definitions)
              2)
(check-equal? (count (lambda (entry)
                       (member (definition-entry-port-state entry)
                               '(a0 ported)))
                     definitions)
              0)
(define zipwith
  (findf (lambda (entry) (string=? (definition-entry-id entry) "D12.ZipWith"))
         definitions))
(check-equal? (map definition-domain-name (definition-entry-domains zipwith))
              '(equal-length unequal-length))
(check-equal? (map definition-domain-issue (definition-entry-domains zipwith))
              '(#f "#41"))
(check-equal? (map definition-domain-port-state
                   (definition-entry-domains zipwith))
              '(none none))

;; P0.2: every live dispatch branch has one tracked class and exact source
;; range. A synthetic branch and a shifted source range both fail the gate.
(define live-branches (extract-infer-branches))
(define branch-ledger (load-infer-branches))
(check-equal? (length live-branches) 91)
(check-equal? (length branch-ledger) 91)
(check-equal? (infer-branch-findings live-branches branch-ledger) '())
(check-equal? (count (lambda (entry)
                       (eq? (branch-entry-class entry) 'semantic-clause))
                     branch-ledger)
              72)
(check-equal? (count (lambda (entry)
                       (eq? (branch-entry-class entry) 'auxiliary))
                     branch-ledger)
              14)
(check-equal? (count (lambda (entry)
                       (eq? (branch-entry-class entry)
                            'external-gap-or-diagnostic))
                     branch-ledger)
              5)
(define synthetic-branch
  (branch-observation 'infer-application '(eq? head 'Tomorrow) 999 1000
                      "synthetic"))
(check-not-false
 (findf (lambda (message) (string-contains? message "unclassified"))
        (infer-branch-findings (cons synthetic-branch live-branches)
                               branch-ledger)))
(define shifted-entry
  (struct-copy branch-entry (first branch-ledger)
               [start-line (add1 (branch-entry-start-line
                                  (first branch-ledger)))]))
(check-not-false
 (findf (lambda (message) (string-contains? message "source range is stale"))
        (infer-branch-findings
         live-branches (cons shifted-entry (rest branch-ledger)))))
(define stale-digest-entry
  (struct-copy branch-entry (first branch-ledger)
               [source-sha1 "stale-source-digest"]))
(check-not-false
 (findf (lambda (message) (string-contains? message "source digest is stale"))
        (infer-branch-findings
         live-branches (cons stale-digest-entry (rest branch-ledger)))))
(define noncanonical-id-entry
  (struct-copy branch-entry (first branch-ledger) [id "B.not-canonical"]))
(check-not-false
 (findf (lambda (message) (string-contains? message "canonical stable id"))
        (infer-branch-findings
         live-branches (cons noncanonical-id-entry (rest branch-ledger)))))
(check-equal? (diagnostic-taxonomy-findings) '())

;; The observer is inert by default and records only externally requested
;; roots, never recursive subterms.
(define observed-roots '())
(parameterize ([current-infer-core-observer
                (lambda (node _env _inv)
                  (set! observed-roots
                        (cons (core->plain-datum node) observed-roots)))])
  (void
   (infer-core (read-core-specimen "(Close (gerku Speaker))"
                                   'phase0-observer))))
(check-equal? (length observed-roots) 1)

;; P0.3: the frozen replay corpus includes both live fences and executed test
;; roots. Phase 0's new side is deliberately the old engine again, proving the
;; oracle plumbing with zero implicit differences and an empty waiver ledger.
(define corpus (load-port-corpus))
(check-equal? (length corpus) 337)
(check-true
 (for*/or ([item (in-list corpus)]
           [provenance (in-list (port-case-provenance item))])
   (and (pair? provenance) (eq? (first provenance) 'fence))))
(check-true
 (for*/or ([item (in-list corpus)]
           [provenance (in-list (port-case-provenance item))])
   (and (pair? provenance) (eq? (first provenance) 'test))))
(check-equal? (load-port-waivers) '())
(define-values (differential-ok? differences stale-waivers)
  (run-differential corpus '() #:print? #f))
(check-true differential-ok?)
(check-equal? differences '())
(check-equal? stale-waivers '())

;; The identity run is not the only oracle test: inject a mismatch in every
;; compared field, multiple derivations, and an incorrectly scoped waiver.
(define oracle-case
  (port-case "oracle-self-test" '((test "phase0-test.rkt"))
             '(Close (gerku Speaker)) '() '(core fixture)))
(define success-record
  (port-record 'success 'Content '() '() '() #f #f #f 1))
(define rejection-record
  (port-record 'rejection #f '() '() '() 'typing-failure 'Close "failed" 0))
(define gap-record
  (port-record 'gap 'Unknown '() '() '(known-gap) #f #f #f 1))
(define (constant-engine record) (lambda (_item) record))
(define (oracle-rejects? old new [waivers '()])
  (define-values (ok? found _stale)
    (run-differential (list oracle-case) waivers
                      #:old-engine (constant-engine old)
                      #:new-engine (constant-engine new)
                      #:print? #f))
  (and (not ok?) (pair? found)))
(check-true
 (oracle-rejects? success-record
                  (struct-copy port-record success-record [type 'Natural])))
(check-true
 (oracle-rejects? success-record
                  (struct-copy port-record success-record [effects '(refer)])))
(check-true
 (oracle-rejects? success-record
                  (struct-copy port-record success-record
                               [obligations '(definedness)])))
(check-true
 (oracle-rejects? rejection-record
                  (struct-copy port-record rejection-record
                               [failure-class 'checker-error])))
(check-true
 (oracle-rejects? rejection-record
                  (struct-copy port-record rejection-record
                               [source-rule 'DifferentConstructor])))
(check-true
 (oracle-rejects? gap-record
                  (struct-copy port-record gap-record [gaps '(other-gap)])))
(check-true
 (oracle-rejects? success-record
                  (struct-copy port-record success-record [derivations 2])))
(define type-only-waiver
  '((waiver (case "oracle-self-test") (fields type)
            (finding "self-test") (reason "This waiver is deliberately narrow."))))
(check-true
 (oracle-rejects? success-record
                  (struct-copy port-record success-record [effects '(refer)])
                  type-only-waiver))
(define-values (waived-ok? waived-differences waived-stale)
  (run-differential
   (list oracle-case) type-only-waiver
   #:old-engine (constant-engine success-record)
   #:new-engine
   (constant-engine (struct-copy port-record success-record [type 'Natural]))
   #:print? #f))
(check-true waived-ok?)
(check-equal? waived-differences '())
(check-equal? waived-stale '())

;; P0.4: the tracked baseline names the exact pre-port head, 96 specimen-term
;; executions, five warm runs, and every pre-registered trigger.
(match (load-port-baseline)
  [`(smusni-port-baseline 1
     (head ,head) (corpus-sha1 ,_) (terms 96) (runs 5)
     (full-gate-ms ,(? real? full-gate))
     (triggers ,triggers ...) (modes ,modes ...))
   (check-equal? head "ad46048d7ac9b496c7a404a00258ac210988681a")
   (check-equal? full-gate 36900)
   (check-equal? (map second triggers)
                 '(5.0 2000.0 250.0 500.0 2.0 3.0 1.5 4.0))
   (check-equal? (map second modes) '(old-only new-only side-by-side))]
  [other (fail-check (format "unexpected baseline: ~e" other))])

(displayln "phase 0 port instruments: ok")
