#lang racket
(require json rackunit racket/list racket/runtime-path
         "../lower.rkt" "../reference-scopes.rkt")

(define-runtime-path probe-path "../inventory/parses/in-place-probes.json")
(define probes (hash-ref (call-with-input-file probe-path read-json) 'cases))
(define (probe surface)
  (findf (lambda (p) (equal? surface (hash-ref p 'surface))) probes))
(define (rr parse profiles rows [readings '(actual)])
  (rr-case 1 (hash 'parse '("regression" 1) 'attach '() 'readings readings
                   'rows rows 'stores '() 'sites '() 'references profiles
                   'anaphora '() 'force '(assert))))

;; E01-C02, constructed by Astra, 2026-09-10: two actual descriptions cannot
;; each be inside the other's binding scope. Type checks cannot catch this.
(define pair-parse (probe "lo gerku cu tavla lo mlatu"))
(define pair-starts (reference-occurrences pair-parse))
(define a (first pair-starts))
(define b (second pair-starts))
(define cycle `((,a (dependent (governors ,b) (scope ,b)))
                (,b (dependent (governors ,a) (scope ,a)))))
(check-true (lowered? (lower pair-parse
                            (rr pair-parse `((,a invariant) (,b invariant)) '(gerku mlatu tavla)))))
(define bad-cycle (lower pair-parse (rr pair-parse cycle '(gerku mlatu tavla))))
(check-equal? (no-lowering-cause bad-cycle) 'rr-missing)
(check-regexp-match #rx"cyclic" (no-lowering-premise bad-cycle))

;; A later source offset can be an outer governor on a declared reading.
(define valid-later `((,a (dependent (governors ,b) (scope ,b))) (,b invariant)))
(define unsupported (lower pair-parse (rr pair-parse valid-later '(gerku mlatu tavla))))
(check-equal? (no-lowering-cause unsupported) 'rule-underspecified)
(define malformed-fields
  (struct-copy rr-case (rr pair-parse valid-later '(gerku mlatu tavla))
               [fields (hash-set (rr-case-fields (rr pair-parse valid-later '(gerku mlatu tavla)))
                                  'stores '(unexpected))]))
(check-equal? (no-lowering-cause (lower pair-parse malformed-fields)) 'rr-missing)

(define triple-parse (probe "lo prenu cu klama lo gerku lo mlatu"))
(define triple-starts (reference-occurrences triple-parse))
(define larger-cycle
  (for/list ([id triple-starts] [governor (append (rest triple-starts) (list (first triple-starts)))])
    `(,id (dependent (governors ,governor) (scope ,governor)))))
(check-equal? (no-lowering-cause (lower triple-parse
                                       (rr triple-parse larger-cycle '(prenu gerku mlatu klama))))
              'rr-missing)

;; Acyclic is not enough: the chosen outer scope cannot see a required inner
;; quantifier. Quantifier order comes from the parsed clause, not all offsets.
(define-runtime-path crossing-path "fixtures/reference-scope-crossing.json")
(define crossing-parse (call-with-input-file crossing-path read-json))
(define ref-start (first (reference-occurrences crossing-parse)))
;; The two ro positions are extracted from this fixture's declared surface;
;; they identify actual parsed quantifier sources validated by the adapter.
(define ro-starts (map car (regexp-match-positions* #rx"ro" (hash-ref crossing-parse 'surface))))
(define outer (first ro-starts))
(define inner (second ro-starts))
(define crossing `((,ref-start (dependent (governors ,outer ,inner) (scope ,outer)))))
(define crossed (lower crossing-parse
                        (rr crossing-parse crossing '(gerku mlatu prenu tavla) '(actual non-importing))))
(check-equal? (no-lowering-cause crossed) 'rr-missing)
(check-regexp-match #rx"crosses outside" (no-lowering-premise crossed))
(define nested `((,ref-start (dependent (governors ,outer ,inner) (scope ,inner)))))
(check-equal? (no-lowering-cause
               (lower crossing-parse
                      (rr crossing-parse nested '(gerku mlatu prenu tavla) '(actual non-importing))))
              'rule-underspecified)

;; Independent lexical clauses are not made one quantifier chain by sorting
;; their offsets. A quantifier local to a sibling clause cannot be captured.
(check-regexp-match
 #rx"separate lexical clause"
 (reference-scope-error
  (list (scope-site 0 'quantifier '(left)) (scope-site 20 'reference '(right)))
  '((20 (dependent (governors 0) (scope 0))))))

(define nested-sites
  (list (scope-site 0 'reference '(clause))
        (scope-site 10 'quantifier '(clause))
        (scope-site 20 'reference '(clause (binding 0)))))
(check-regexp-match
 #rx"containing property scope"
 (reference-scope-error nested-sites
                        '((0 invariant) (20 (dependent (governors 10) (scope 10))))))
(check-false
 (reference-scope-error nested-sites
                        '((0 (dependent (governors 10) (scope 10)))
                          (20 (dependent (governors 10) (scope 10))))))

;; Check the containing-property boundary through a real nested gentufa tree,
;; not only through the graph representation above.
(define-runtime-path nested-path "fixtures/reference-scope-nested.json")
(define nested-parse (call-with-input-file nested-path read-json))
(define nested-starts (reference-occurrences nested-parse))
(define main-q (caar (regexp-match-positions* #rx"ro" (hash-ref nested-parse 'surface))))
(define nested-bad
  (lower nested-parse
         (rr nested-parse
             `((,(first nested-starts) invariant)
               (,(second nested-starts) (dependent (governors ,main-q) (scope ,main-q))))
             '(prenu gerku mlatu tavla) '(actual non-importing))))
(check-equal? (no-lowering-cause nested-bad) 'rr-missing)
(check-regexp-match #rx"containing property scope" (no-lowering-premise nested-bad))

;; E01-RR-TRANSITIVE-01, Astra's second E01 gate, 2026-09-10. A reference
;; carries its governor availability; naming it cannot hide a local quantifier.
(define transitive-sites
  (list (scope-site 0 'quantifier '(left))
        (scope-site 18 'reference '(left))
        (scope-site 32 'reference '(right))))
(define indirect
  '((18 (dependent (governors 0) (scope 0)))
    (32 (dependent (governors 18) (scope 18)))))
(check-regexp-match #rx"separate lexical clause"
                    (reference-scope-error transitive-sites indirect))
(check-false (reference-scope-error transitive-sites
              '((18 invariant) (32 (dependent (governors 18) (scope 18))))))
(check-false (reference-scope-error transitive-sites
              '((18 (dependent (governors 0) (scope 0))) (32 invariant))))

(define nested-chain-sites
  (list (scope-site 0 'reference '(clause))
        (scope-site 10 'quantifier '(clause (binding 0)))
        (scope-site 20 'reference '(clause (binding 0)))))
(check-regexp-match #rx"separate lexical clause"
  (reference-scope-error nested-chain-sites
    '((0 (dependent (governors 20) (scope 20)))
      (20 (dependent (governors 10) (scope 10))))))
;; The quantifier ordered after invariant20 is not one of20's dependencies.
(check-false (reference-scope-error nested-chain-sites
              '((0 (dependent (governors 20) (scope 20))) (20 invariant))))
(check-false (reference-scope-error nested-chain-sites
              '((0 invariant) (20 (dependent (governors 10) (scope 10))))))

;; Apply transitive requirements to the containing-property check too, even
;; when the intervening reference is in another nested region.
(define boundary-chain-sites
  (list (scope-site 0 'reference '(clause))
        (scope-site 10 'quantifier '(clause))
        (scope-site 20 'reference '(clause branch))
        (scope-site 30 'reference '(clause (binding 0)))))
(check-regexp-match #rx"containing property scope"
  (reference-scope-error boundary-chain-sites
    '((0 invariant) (20 (dependent (governors 10) (scope 10)))
      (30 (dependent (governors 20) (scope 20))))))
(check-false (reference-scope-error boundary-chain-sites
              '((0 (dependent (governors 10) (scope 10)))
                (20 (dependent (governors 10) (scope 10)))
                (30 (dependent (governors 20) (scope 20))))))

;; Vary chain length: closure is over requirements, not fixture IDs or the
;; binding-order graph. Only removing the actual quantifier dependency frees
;; the final reference from its region requirement.
(for ([length '(1 3 6)])
  (define ids (range 10 (+ 10 length)))
  (define chain-sites
    (append (list (scope-site 0 'quantifier '(left)))
            (map (lambda (id) (scope-site id 'reference '(left))) ids)
            (list (scope-site 100 'reference '(right)))))
  (define chain
    (append (for/list ([id ids] [parent (cons 0 ids)])
              `(,id (dependent (governors ,parent) (scope ,parent))))
            `((100 (dependent (governors ,(last ids)) (scope ,(last ids)))))))
  (check-regexp-match #rx"separate lexical clause" (reference-scope-error chain-sites chain))
  (check-false (reference-scope-error chain-sites (cons `(,(first ids) invariant) (rest chain)))))

;; The real parsed sentence previously reached a separate L5.12 refusal.
;; Require the failure to come from scope legality at L5.30, so that unrelated
;; lowering refusal cannot make this regression pass.
(define-runtime-path transitive-path "fixtures/reference-scope-transitive.json")
(define transitive-parse (call-with-input-file transitive-path read-json))
(check-equal? (reference-occurrences transitive-parse) '(18 32))
(define parsed-transitive-error
  (lower transitive-parse
         (rr transitive-parse indirect '(prenu mlatu gerku tavla sipna) '(actual non-importing))))
(check-equal? (no-lowering-cause parsed-transitive-error) 'rr-missing)
(check-equal? (no-lowering-rule parsed-transitive-error) "L5.30")
(check-regexp-match #rx"separate lexical clause" (no-lowering-premise parsed-transitive-error))
