#lang racket

(require racket/list racket/match racket/set)
(provide (struct-out scope-site) reference-scope-error)

;; Source regions identify clause/property bodies, not numerical offset ranges.
;; A scope selects a cut in that region's fixed in-situ quantifier nesting.
;; References at the same cut can be sequenced without becoming dependencies
;; of one another; only explicit governors create those dependency edges.
(struct scope-site (id kind region) #:transparent)

(define (reference-scope-error sites profiles)
  ;; The adapter has already checked profile shape, unique coverage, and
  ;; target membership. This pass checks whether those targets can be in scope.
  (let/ec fail
    (define by-id (for/hash ([s sites]) (values (scope-site-id s) s)))
    (unless (= (hash-count by-id) (length sites))
      (fail "binding-source offsets are not unambiguous"))
    (define declarations (for/hash ([p profiles]) (values (first p) (second p))))
    (define edges (for/hash ([s sites]) (values (scope-site-id s) (mutable-set))))
    ;; Ordering constrains a possible binding sequence. Required availability
    ;; is a different relation: an invariant reference ordered before a
    ;; quantifier does not thereby depend on that quantifier (or vice versa).
    (define direct-requirements (make-hash))
    (define (edge outer inner) (set-add! (hash-ref edges outer) inner))
    (define ranks (make-hash))
    (for ([region (remove-duplicates (map scope-site-region sites))])
      (define local (sort (filter (lambda (s) (equal? (scope-site-region s) region)) sites)
                          < #:key scope-site-id))
      (define quantifiers (filter (lambda (s) (eq? (scope-site-kind s) 'quantifier)) local))
      (define invariant
        (filter (lambda (s) (and (eq? (scope-site-kind s) 'reference)
                                 (eq? (hash-ref declarations (scope-site-id s)) 'invariant))) local))
      (for ([q quantifiers] [rank (in-naturals 1)]) (hash-set! ranks (scope-site-id q) rank))
      ;; L5.30 fixes invariant references outside quantifiers, and the order
      ;; within both sequences. A later *dependent* reference is not forced
      ;; outside its required governor by its source position.
      (define fixed (append invariant quantifiers))
      (for ([a fixed] [b (if (null? fixed) '() (rest fixed))])
        (edge (scope-site-id a) (scope-site-id b))))
    (define (region-prefix? outer inner)
      (and (<= (length outer) (length inner))
           (equal? outer (take inner (length outer)))))
    (for ([p profiles])
      (match p
        [`(,id (dependent (governors ,governors ...) (scope ,scope)))
         (define target (hash-ref by-id id))
         (unless (eq? (scope-site-kind target) 'reference)
           (fail "a reference profile cannot move a fixed quantified-sumti binder"))
         (define needed (remove-duplicates (cons scope governors)))
         (hash-set! direct-requirements id needed)
         (for ([g needed]) (edge g id))]
        [_ (void)]))
    (define visiting (mutable-set))
    (define visited (mutable-set))
    (define (visit id)
      (when (set-member? visiting id) (fail "cyclic reference dependency/scope graph"))
      (unless (set-member? visited id)
        (set-add! visiting id)
        (for ([child (in-set (hash-ref edges id))]) (visit child))
        (set-remove! visiting id)
        (set-add! visited id)))
    (for ([id (hash-keys by-id)]) (visit id))
    ;; The cycle check above establishes well-founded recursion. Follow only
    ;; declared governor/scope requirements, never the fixed ordering edges.
    ;; A reference cannot hide the availability needed by its own governors.
    (define requirement-cache (make-hash))
    (define (requirements id)
      (hash-ref!
       requirement-cache id
       (lambda ()
         (for/fold ([needed (set)]) ([g (hash-ref direct-requirements id '())])
           (set-union needed (set-add (requirements g) g))))))
    (define levels (make-hash))
    ;; Same-region scope recursion is well-founded by that same cycle check:
    ;; every declared scope target was added as an edge before visiting.
    (define (level id)
      (hash-ref!
       levels id
       (lambda ()
         (define site (hash-ref by-id id))
         (cond
           [(eq? (scope-site-kind site) 'quantifier) (hash-ref ranks id)]
           [else
            (match (hash-ref declarations id)
              ['invariant 0]
              [`(dependent (governors ,_ ...) (scope ,scope))
               (if (equal? (scope-site-region site)
                           (scope-site-region (hash-ref by-id scope)))
                   (level scope)
                   0)])]))))
    (for ([p profiles])
      (match p
        [`(,id (dependent (governors ,governors ...) (scope ,scope)))
         (define target (hash-ref by-id id))
         (for ([g (in-set (requirements id))])
           (define governor (hash-ref by-id g))
           (when (and (eq? (scope-site-kind governor) 'quantifier)
                      (not (region-prefix? (scope-site-region governor)
                                           (scope-site-region target))))
             (fail "reference captures a quantifier from a separate lexical clause"))
           (when (and (equal? (scope-site-region target)
                              (scope-site-region (hash-ref by-id g)))
                      (> (level g) (level id)))
             (fail "reference binding scope crosses outside a required governor"))
           ;; A nested description stays in its containing property's lexical
           ;; scope. It cannot obtain a variable unavailable where that outer
           ;; property is formed, even if the offset names a real binder.
           (for ([part (scope-site-region target)]
                 #:when (and (list? part) (equal? (first part) 'binding)))
             (define owner (second part))
             (when (and (equal? (scope-site-region (hash-ref by-id owner))
                                (scope-site-region (hash-ref by-id g)))
                        (> (level g) (level owner)))
               (fail "nested reference captures a governor outside its containing property scope"))))]
        [_ (void)]))
    #f))
