#lang racket

(require racket/list
         racket/match
         racket/port
         racket/runtime-path
         racket/set
         racket/string
         racket/system
         redex/reduction-semantics
         "port-a0.rkt")

(provide SmusniB2Spike
         (struct-out b2-node)
         (struct-out b2-env)
         (struct-out b2-binding-group)
         (struct-out b2-binding)
         (struct-out b2-proof)
         (struct-out b2-spike-run)
         (struct-out b2-identity-micro)
         (struct-out b2-spike-growth)
         (struct-out b2-rule-descriptor)
         b2-spike-type
         b2-spike-synth
         b2-identity-probe
         b2-compile-term
         b2-node->datum
         b2-node->alpha-datum
         b2-node-at-path
         b2-raw-occurrence-count
         b2-compile-env
         b2-env->datum
         b2-env-extend
         b2-env-extend-binding
         b2-env-lookup
         b2-env-lookup-binding
         b2-env-lookup-node
         b2-node-head
         b2-rule-input-matches?
         b2-rule-descriptors
         b2-descriptor-findings
         b2-execution-identity-free?
         b2-assert-no-execution-identities
         b2-project-derivation
         b2-project-raw-derivation
         b2-spike-query-synth
         b2-spike-run-synth
         b2-reference-proofs
         b2-spike-supported?
         run-b2-identity-trial
         run-b2-identity-micro
         run-b2-spike-growth)

;; These structures intentionally omit #:transparent and any equal+hash
;; implementation. Racket therefore compares and hashes them by identity,
;; without traversing descendants or environment bindings. They are an
;; execution representation only; b2-node->datum and b2-env->datum are the
;; sole projection boundary back to semantic data.
(struct b2-binding-group (ordinal))
(struct b2-binding (scope-group position source-symbol))
(struct b2-node
  (kind atom children path value-form? expected-only? binding binding-role))
(struct b2-env (bindings resolved-bindings))

(struct b2-proof (statement name subs) #:transparent)
(struct b2-spike-run
  (records proofs compile-ms judge-ms node-count compile-count)
  #:transparent)
(struct b2-identity-micro
  (depths per-call-ms max-min-ratio monotone-growth? passed?)
  #:transparent)
(struct b2-spike-growth
  (depths total-ms compile-ms judge-ms node-count ratios passed?)
  #:transparent)
(struct b2-rule-descriptor (name accessor-shape raw-production)
  #:transparent)

(define (quoted-head? datum)
  (and (pair? datum) (member (first datum) '(Quote Syntax))))

(define (node-atom=? node expected)
  (and (b2-node? node)
       (eq? (b2-node-kind node) 'atom)
       (equal? (b2-node-atom node) expected)))

(define (b2-node-head node)
  (and (b2-node? node)
       (eq? (b2-node-kind node) 'list)
       (pair? (b2-node-children node))
       (let ([head (first (b2-node-children node))])
         (and (eq? (b2-node-kind head) 'atom)
              (symbol? (b2-node-atom head))
              (b2-node-atom head)))))

(define (list-node-value-form? children)
  (define head
    (and (pair? children)
         (let ([candidate (first children)])
           (and (eq? (b2-node-kind candidate) 'atom)
                (b2-node-atom candidate)))))
  (or (eq? head 'λ)
      (and (eq? head 'List)
           (andmap b2-node-value-form? (rest children)))))

(define (list-node-expected-only? children)
  (define head
    (and (pair? children)
         (let ([candidate (first children)])
           (and (eq? (b2-node-kind candidate) 'atom)
                (b2-node-atom candidate)))))
  (cond
    [(member head
             '(Context Vague Refer SelectExactly SelectAtLeast SelectSome
                       SelectAllBut Massify MaxRefer))
     #t]
    [(and (eq? head 'Presuppose) (= (length children) 3))
     (b2-node-expected-only? (third children))]
    [else #f]))

(define (fresh-binding-group! next-group)
  (define group (b2-binding-group (unbox next-group)))
  (set-box! next-group (add1 (unbox next-group)))
  group)

(define (scope-binding scope datum)
  (and (symbol? datum)
       (match (assoc datum scope)
         [(cons _ binding) binding]
         [_ #f])))

(define (compile-atom datum path scope [binding #f])
  ;; Every atomic term in the closed grammar is a value. Atomic metadata is
  ;; compiled by the same generic datum traversal but is never independently
  ;; submitted to the typing judgment.
  (define resolved-binding (or binding (scope-binding scope datum)))
  (values (b2-node 'atom datum '() path #t #f resolved-binding
                   (cond [binding 'declaration]
                         [resolved-binding 'reference]
                         [else #f]))
          1))

(define (make-list-node children path)
  (b2-node 'list #f children path
           (list-node-value-form? children)
           (list-node-expected-only? children)
           #f #f))

(define (compile-sequence datums path scope next-group)
  (define-values (reversed count)
    (for/fold ([compiled '()] [count 0])
              ([value (in-list datums)] [index (in-naturals)])
      (define-values (node node-count)
        (compile-datum value (append path (list index)) scope next-group))
      (values (cons node compiled) (+ count node-count))))
  (values (reverse reversed) count))

(define (compile-binder-list binders path scope next-group)
  (define group (fresh-binding-group! next-group))
  (define bindings
    (for/list ([binder (in-list binders)] [position (in-naturals)])
      (match binder
        [(list (? symbol? variable) _)
         (b2-binding group position variable)])))
  (define-values (entries-reversed entry-count)
    (for/fold ([entries '()] [count 0])
              ([binder (in-list binders)]
               [binding (in-list bindings)]
               [index (in-naturals)])
      (match-define (list variable type) binder)
      (define entry-path (append path (list index)))
      (define-values (variable-node variable-count)
        (compile-atom variable (append entry-path '(0)) scope binding))
      (define-values (type-node type-count)
        (compile-datum type (append entry-path '(1)) scope next-group))
      (values
       (cons (make-list-node (list variable-node type-node) entry-path)
             entries)
       (+ count 1 variable-count type-count))))
  (values (make-list-node (reverse entries-reversed) path)
          (add1 entry-count)
          (map cons (map first binders) bindings)))

(define (compile-lambda datum path scope next-group)
  (match-define `(λ ,binders ,body) datum)
  (define-values (head head-count)
    (compile-atom 'λ (append path '(0)) scope))
  (define-values (binder-node binder-count new-bindings)
    (compile-binder-list binders (append path '(1)) scope next-group))
  (define body-scope (append new-bindings scope))
  (define-values (body-node body-count)
    (compile-datum body (append path '(2)) body-scope next-group))
  (values (make-list-node (list head binder-node body-node) path)
          (+ 1 head-count binder-count body-count)))

(define (compile-let datum path scope next-group)
  (match-define `(Let (,variable ,type) ,active ,body) datum)
  (define group (fresh-binding-group! next-group))
  (define binding (b2-binding group 0 variable))
  (define-values (head head-count)
    (compile-atom 'Let (append path '(0)) scope))
  (define binder-path (append path '(1)))
  (define-values (variable-node variable-count)
    (compile-atom variable (append binder-path '(0)) scope binding))
  (define-values (type-node type-count)
    (compile-datum type (append binder-path '(1)) scope next-group))
  (define binder-node
    (make-list-node (list variable-node type-node) binder-path))
  (define-values (active-node active-count)
    (compile-datum active (append path '(2)) scope next-group))
  (define-values (body-node body-count)
    (compile-datum body (append path '(3))
                   (cons (cons variable binding) scope) next-group))
  (values (make-list-node
           (list head binder-node active-node body-node) path)
          (+ 2 head-count variable-count type-count
             active-count body-count)))

(define (compile-bind datum path scope next-group)
  (match-define `(Bind ,bindings ,body) datum)
  (define-values (head head-count)
    (compile-atom 'Bind (append path '(0)) scope))
  (define bindings-path (append path '(1)))
  (define-values (entries-reversed entry-count final-scope)
    (for/fold ([entries '()] [count 0] [current-scope scope])
              ([binder (in-list bindings)] [index (in-naturals)])
      (match-define (list variable type computation) binder)
      (define group (fresh-binding-group! next-group))
      (define binding (b2-binding group 0 variable))
      (define entry-path (append bindings-path (list index)))
      (define-values (variable-node variable-count)
        (compile-atom variable (append entry-path '(0)) current-scope binding))
      (define-values (type-node type-count)
        (compile-datum type (append entry-path '(1)) current-scope next-group))
      (define-values (computation-node computation-count)
        (compile-datum computation (append entry-path '(2))
                       current-scope next-group))
      (values
       (cons (make-list-node
              (list variable-node type-node computation-node) entry-path)
             entries)
       (+ count 1 variable-count type-count computation-count)
       (cons (cons variable binding) current-scope))))
  (define bindings-node
    (make-list-node (reverse entries-reversed) bindings-path))
  (define-values (body-node body-count)
    (compile-datum body (append path '(2)) final-scope next-group))
  (values (make-list-node (list head bindings-node body-node) path)
          (+ 2 head-count entry-count body-count)))

(define (compile-datum datum path scope next-group)
  (cond
    [(quoted-head? datum)
     (values (b2-node 'opaque datum '() path #f #f #f #f) 1)]
    [(and (list? datum) (pair? datum) (eq? (first datum) 'λ))
     (compile-lambda datum path scope next-group)]
    [(and (list? datum) (pair? datum) (eq? (first datum) 'Let))
     (compile-let datum path scope next-group)]
    [(and (list? datum) (pair? datum) (eq? (first datum) 'Bind))
     (compile-bind datum path scope next-group)]
    [(list? datum)
     (define-values (children child-count)
       (compile-sequence datum path scope next-group))
     (values (make-list-node children path) (add1 child-count))]
    [else (compile-atom datum path scope)]))

(define (b2-raw-occurrence-count datum)
  (cond
    [(quoted-head? datum) 1]
    [(list? datum)
     (add1 (for/sum ([child (in-list datum)])
             (b2-raw-occurrence-count child)))]
    [else 1]))

(define (b2-compile-term datum)
  (unless (redex-match? SmusniA0 t datum)
    (raise-argument-error 'b2-compile-term "SmusniA0 term datum" datum))
  (define-values (root count) (compile-datum datum '() '() (box 0)))
  (unless (= count (b2-raw-occurrence-count datum))
    (error 'b2-compile-term "node/occurrence count mismatch for ~e" datum))
  (values root count))

(define (b2-node->datum node)
  (unless (b2-node? node)
    (raise-argument-error 'b2-node->datum "b2-node?" node))
  (case (b2-node-kind node)
    [(atom opaque) (b2-node-atom node)]
    [(list) (map b2-node->datum (b2-node-children node))]
    [else (error 'b2-node->datum "unknown node kind: ~e" (b2-node-kind node))]))

;; Project bound declarations/references through their resolved opaque identity.
;; References whose declarations are outside the projected subtree are named
;; first by scope-exit order (inner groups first). Declarations inside the
;; subtree are then named in ordinary left-to-right syntax traversal order,
;; exactly like alpha-normalize-datum. Truly free $alphaN spellings are reserved
;; before both classes.
(define (b2-node->alpha-datum node)
  (unless (b2-node? node)
    (raise-argument-error 'b2-node->alpha-datum "b2-node?" node))
  (define internal-bindings-reversed '())
  (define external-bindings-reversed '())
  (define free-symbols (mutable-set))
  (define (collect current)
    (unless (eq? (b2-node-kind current) 'opaque)
      (define binding (b2-node-binding current))
      (cond
        [(eq? (b2-node-binding-role current) 'declaration)
         (set! internal-bindings-reversed
               (cons binding internal-bindings-reversed))]
        [(eq? (b2-node-binding-role current) 'reference)
         (set! external-bindings-reversed
               (cons binding external-bindings-reversed))]
        [(and (eq? (b2-node-kind current) 'atom)
              (symbol? (b2-node-atom current))
              (string-prefix? (symbol->string (b2-node-atom current)) "$"))
         (set-add! free-symbols (b2-node-atom current))])
      (for ([child (in-list (b2-node-children current))])
        (collect child))))
  (collect node)
  (define internal-bindings
    (remove-duplicates (reverse internal-bindings-reversed) eq?))
  (define internal-groups
    (for/seteq ([binding (in-list internal-bindings)])
      (b2-binding-scope-group binding)))
  (define external-bindings
    (filter
     (lambda (binding)
       (not (set-member? internal-groups (b2-binding-scope-group binding))))
     (remove-duplicates (reverse external-bindings-reversed) eq?)))
  (define ordered-external-bindings
    (sort external-bindings
          (lambda (left right)
            (define left-group
              (b2-binding-group-ordinal (b2-binding-scope-group left)))
            (define right-group
              (b2-binding-group-ordinal (b2-binding-scope-group right)))
            (or (> left-group right-group)
                (and (= left-group right-group)
                     (< (b2-binding-position left)
                        (b2-binding-position right)))))))
  (define ordered-bindings
    (append ordered-external-bindings internal-bindings))
  (define names (make-hasheq))
  (define used (set-copy free-symbols))
  (define counter 0)
  (define (fresh-name)
    (let loop ()
      (define candidate (string->symbol (format "$alpha~a" counter)))
      (set! counter (add1 counter))
      (if (set-member? used candidate)
          (loop)
          (begin (set-add! used candidate) candidate))))
  (for ([binding (in-list ordered-bindings)])
    (hash-set! names binding (fresh-name)))
  (define (project current)
    (case (b2-node-kind current)
      [(opaque) (b2-node-atom current)]
      [(atom)
       (define binding (b2-node-binding current))
       (if binding (hash-ref names binding) (b2-node-atom current))]
      [(list) (map project (b2-node-children current))]
      [else
       (error 'b2-node->alpha-datum
              "unknown node kind: ~e" (b2-node-kind current))]))
  (project node))

(define (b2-node-at-path node path)
  (cond
    [(null? path) node]
    [(or (not (b2-node? node))
         (not (eq? (b2-node-kind node) 'list)))
     #f]
    [else
     (define index (first path))
     (and (exact-nonnegative-integer? index)
          (< index (length (b2-node-children node)))
          (b2-node-at-path (list-ref (b2-node-children node) index)
                           (rest path)))]))

(define (b2-compile-env environment)
  (unless (redex-match? SmusniA0 Γ environment)
    (raise-argument-error 'b2-compile-env "SmusniA0 environment datum"
                          environment))
  (b2-env environment '()))

(define (b2-env->datum environment)
  (unless (b2-env? environment)
    (raise-argument-error 'b2-env->datum "b2-env?" environment))
  (b2-env-bindings environment))

(define (b2-env-extend environment bindings)
  (unless (and (b2-env? environment)
               (andmap (lambda (binding)
                         (match binding [(list (? symbol?) _) #t] [_ #f]))
                       bindings))
    (raise-arguments-error 'b2-env-extend "invalid environment extension"
                           "environment" environment "bindings" bindings))
  (b2-env (foldr cons (b2-env-bindings environment) bindings)
          (b2-env-resolved-bindings environment)))

(define (b2-env-extend-binding environment binding type)
  (unless (and (b2-env? environment) (b2-binding? binding))
    (raise-arguments-error
     'b2-env-extend-binding "invalid resolved binding extension"
     "environment" environment "binding" binding))
  (b2-env
   (cons (list (b2-binding-source-symbol binding) type)
         (b2-env-bindings environment))
   (cons (cons binding type) (b2-env-resolved-bindings environment))))

(define (b2-env-lookup environment variable)
  (match (assoc variable (b2-env-bindings environment))
    [(list _ type) type]
    [_ 'not-found]))

(define (b2-env-lookup-binding environment binding)
  (match (assq binding (b2-env-resolved-bindings environment))
    [(cons _ type) type]
    [_ 'not-found]))

(define (b2-env-lookup-node environment node)
  (unless (and (b2-env? environment)
               (b2-node? node)
               (eq? (b2-node-kind node) 'atom))
    (raise-arguments-error 'b2-env-lookup-node "invalid variable lookup"
                           "environment" environment "node" node))
  (define binding (b2-node-binding node))
  (if binding
      (b2-env-lookup-binding environment binding)
      (b2-env-lookup environment (b2-node-atom node))))

(define (b2-let-shape node)
  (and (eq? (b2-node-head node) 'Let)
       (= (length (b2-node-children node)) 4)
       (let* ([children (b2-node-children node)]
              [binder-datum (b2-node->datum (second children))])
         (match binder-datum
           [(list (? symbol? variable) type)
            (define binding
              (b2-node-binding
               (first (b2-node-children (second children)))))
            (and binding
                 (list variable type binding
                       (third children) (fourth children)))]
           [_ #f]))))

(define-extended-language SmusniB2Spike SmusniA0
  [N any]
  [E any])

(define (b2-rule-input-matches? accessor environment node)
  (and
   (b2-env? environment)
   (b2-node? node)
   (case accessor
     [(node:any) #t]
     [(node:atom-natural)
      (and (eq? (b2-node-kind node) 'atom)
           (exact-nonnegative-integer? (b2-node-atom node)))]
     [(node:atom-top) (node-atom=? node '⊤)]
     [(node:list-let) (and (b2-let-shape node) #t)]
     [else #f])))

(define-syntax-rule
  (define-b2-spike-judgment
    language name descriptor-name mode contract (environment-var node-var)
    (rule rule-name accessor production (premise ...) conclusion) ...)
  (begin
    ;; The executable clause and its accessor/raw-production descriptor are one
    ;; generating form. A code-side rule edit cannot leave a detached descriptor
    ;; table green.
    (define-judgment-form language
      #:mode mode
      #:contract contract
      [(side-condition
        ,(b2-rule-input-matches?
          accessor (term environment-var) (term node-var)))
       premise ...
       ----------------------------------------------- rule-name
       conclusion] ...)
    (define descriptor-name
      (list (b2-rule-descriptor rule-name accessor production) ...))))

(define-b2-spike-judgment
  SmusniB2Spike b2-spike-type b2-spike-type-descriptors
  (b2-spike-type I I I O)
  (b2-spike-type direction E N R)
  (E N)

  (rule "A0-T-Natural" 'node:atom-natural
        '(a0-type synth Γ n (typing Natural () ()))
        ()
        (b2-spike-type synth E N (typing Natural () ())))

  (rule "A0-T-Top" 'node:atom-top
        '(a0-type synth Γ ⊤ (typing Content () ()))
        ()
        (b2-spike-type synth E N (typing Content () ())))

  (rule "A0-T-Let" 'node:list-let
        '(a0-type synth Γ (Let (x τ) t_value t_body) R_out)
        ((where (x τ N_binding N_value N_body) ,(b2-let-shape (term N)))
         (side-condition ,(b2-node-value-form? (term N_value)))
         (b2-spike-type synth E N_value (typing τ_value () ()))
         (side-condition ,(a0-compatible? (term τ_value) (term τ)))
         (where E_body
                ,(b2-env-extend-binding
                  (term E) (term N_binding) (term τ)))
         (b2-spike-type synth E_body N_body R_body))
        (b2-spike-type synth E N R_body)))

(define-b2-spike-judgment
  SmusniB2Spike b2-spike-synth b2-spike-synth-descriptors
  (b2-spike-synth I I O)
  (b2-spike-synth E N R)
  (E N)
  (rule "A0-Synth" 'node:any '(a0-synth Γ t R)
        ((b2-spike-type synth E N R))
        (b2-spike-synth E N R)))

;; R1 exercises the exact Redex judgment input path with distinct opaque roots.
(define-judgment-form SmusniB2Spike
  #:mode (b2-identity-probe I I)
  #:contract (b2-identity-probe E N)
  [(side-condition ,(and (b2-env? (term E)) (b2-node? (term N))))
   ----------------------------------------------- "B2-Identity-Probe"
   (b2-identity-probe E N)])

(define b2-rule-descriptors
  (append b2-spike-synth-descriptors b2-spike-type-descriptors))

(define descriptor-production-by-accessor
  (for/hash ([descriptor (in-list b2-rule-descriptors)])
    (values (b2-rule-descriptor-accessor-shape descriptor)
            (b2-rule-descriptor-raw-production descriptor))))

(define (b2-descriptor-findings [descriptors b2-rule-descriptors])
  (define findings '())
  (define (note! format-string . values)
    (set! findings (cons (apply format format-string values) findings)))
  (define expected-rules
    (list->set
     (map ~a
          (append (judgment-form->rule-names b2-spike-synth)
                  (judgment-form->rule-names b2-spike-type)))))
  (define names (map b2-rule-descriptor-name descriptors))
  (unless (= (length names) (set-count (list->set names)))
    (note! "B2 descriptors contain duplicate rule names"))
  (define actual-rules (list->set names))
  (unless (set=? expected-rules actual-rules)
    (note! "B2 descriptor rules differ: missing=~s extra=~s"
           (sort (set->list (set-subtract expected-rules actual-rules)) string<?)
           (sort (set->list (set-subtract actual-rules expected-rules)) string<?)))
  (define accessors (map b2-rule-descriptor-accessor-shape descriptors))
  (unless (= (length accessors) (set-count (list->set accessors)))
    (note! "B2 descriptors contain duplicate accessor shapes"))
  (define productions (map b2-rule-descriptor-raw-production descriptors))
  (unless (= (length productions) (set-count (list->set productions)))
    (note! "B2 descriptors contain duplicate raw productions"))
  (for ([descriptor (in-list descriptors)])
    (define accessor (b2-rule-descriptor-accessor-shape descriptor))
    (define expected (hash-ref descriptor-production-by-accessor accessor #f))
    (unless (equal? expected (b2-rule-descriptor-raw-production descriptor))
      (note! "B2 descriptor ~a has missing or stale accessor/production mapping"
             (b2-rule-descriptor-name descriptor))))
  (reverse findings))

(define (b2-execution-identity-free? value)
  (define seen (make-hasheq))
  (define (walk item)
    (cond
      [(or (b2-node? item) (b2-env? item)
           (b2-binding? item) (b2-binding-group? item))
       #f]
      [(or (symbol? item) (number? item) (string? item) (boolean? item)
           (char? item) (keyword? item) (bytes? item) (null? item)
           (void? item) (eof-object? item))
       #t]
      ;; A closure can capture an execution identity, and Racket provides no
      ;; sound general environment inspector. Fail closed even for a closure
      ;; that happens not to capture one.
      [(procedure? item) #f]
      [(hash-ref seen item #f) #t]
      [else
       (hash-set! seen item #t)
       (cond
         [(pair? item) (and (walk (car item)) (walk (cdr item)))]
         [(vector? item) (for/and ([part (in-vector item)]) (walk part))]
         [(box? item) (walk (unbox item))]
         [(hash? item)
          (for/and ([(key datum) (in-hash item)])
            (and (walk key) (walk datum)))]
         [(struct? item)
          (with-handlers ([exn:fail? (lambda (_) #f)])
            (define parts (struct->vector item))
            (and (> (vector-length parts) 1)
                 (not (for/or ([part (in-vector parts)]) (eq? part '...)))
                 (for/and ([part (in-vector parts)]
                           [index (in-naturals)]
                           #:unless (zero? index))
                   (walk part))))]
         ;; Unknown containers cannot be proven identity-free.
         [else #f])]))
  (walk value))

(define (b2-assert-no-execution-identities value [who 'b2-identity-gate])
  (unless (b2-execution-identity-free? value)
    (error who "execution node/environment identity escaped: ~e" value))
  value)

(define (project-internal-statement statement)
  (match statement
    [`(b2-spike-synth ,(? b2-env? environment) ,(? b2-node? node) ,record)
     `(a0-synth ,(b2-env->datum environment) ,(b2-node->datum node) ,record)]
    [`(b2-spike-type ,direction ,(? b2-env? environment)
                     ,(? b2-node? node) ,record)
     `(a0-type ,direction ,(b2-env->datum environment)
               ,(b2-node->datum node) ,record)]
    [_ (error 'b2-project-derivation
              "unrecognized internal judgment statement: ~e" statement)]))

(define (b2-project-derivation derivation)
  (define proof
    (b2-proof
     (project-internal-statement (derivation-term derivation))
     (derivation-name derivation)
     (map b2-project-derivation (derivation-subs derivation))))
  (b2-assert-no-execution-identities proof 'b2-project-derivation))

(define (b2-project-raw-derivation derivation)
  (define proof
    (b2-proof (derivation-term derivation)
              (derivation-name derivation)
              (map b2-project-raw-derivation (derivation-subs derivation))))
  (b2-assert-no-execution-identities proof 'b2-project-raw-derivation))

(define (proof-record proof)
  (match (b2-proof-statement proof)
    [`(a0-synth ,_ ,_ ,record) record]
    [_ (error 'proof-record "not a synthesis proof: ~e" proof)]))

(define (b2-spike-run-synth environment datum #:memo? [memo? #t])
  (define compile-start (current-inexact-monotonic-milliseconds))
  ;; K1/C1: exactly one term compilation and one environment compilation per
  ;; public query; both are inside the reported compile interval.
  (define-values (root node-count) (b2-compile-term datum))
  (define compiled-environment (b2-compile-env environment))
  (define compile-ms
    (- (current-inexact-monotonic-milliseconds) compile-start))
  (define judge-start (current-inexact-monotonic-milliseconds))
  (define derivations
    (parameterize ([caching-enabled? memo?])
      (build-derivations
       (b2-spike-synth ,compiled-environment ,root R))))
  (define proofs (map b2-project-derivation derivations))
  (define records (map proof-record proofs))
  (b2-assert-no-execution-identities records 'b2-spike-run-synth)
  (b2-assert-no-execution-identities proofs 'b2-spike-run-synth)
  (define judge-ms (- (current-inexact-monotonic-milliseconds) judge-start))
  (b2-spike-run records proofs compile-ms judge-ms node-count 1))

;; This is the public raw record query measured by the unchanged size-growth
;; procedure. It compiles once, calls judgment-holds once, and checks the
;; returned semantic records. Full proof construction/projection remains a
;; separate fidelity gate through b2-spike-run-synth.
(define (b2-spike-query-synth environment datum #:memo? [memo? #t])
  (define compile-start (current-inexact-monotonic-milliseconds))
  (define-values (root node-count) (b2-compile-term datum))
  (define compiled-environment (b2-compile-env environment))
  (define compile-ms
    (- (current-inexact-monotonic-milliseconds) compile-start))
  (define judge-start (current-inexact-monotonic-milliseconds))
  (define records
    (parameterize ([caching-enabled? memo?])
      (judgment-holds
       (b2-spike-synth ,compiled-environment ,root R) R)))
  (b2-assert-no-execution-identities records 'b2-spike-query-synth)
  (define judge-ms (- (current-inexact-monotonic-milliseconds) judge-start))
  (b2-spike-run records '() compile-ms judge-ms node-count 1))

(define (derivation-record derivation)
  (last (derivation-term derivation)))

;; Redex may freshen a raw binder in a premise statement even though its
;; conclusion retains the source spelling. Reconstruct the four-rule oracle
;; statements from the source term/environment so comparison is complete and
;; stable rather than dependent on Redex's generated guillemet suffixes.
(define (canonical-slice-reference-proof derivation environment datum)
  (define name (derivation-name derivation))
  (define record (derivation-record derivation))
  (define subs (derivation-subs derivation))
  (match name
    ["A0-Synth"
     (unless (= (length subs) 1)
       (error 'b2-reference-proofs "A0-Synth oracle shape changed"))
     (b2-proof `(a0-synth ,environment ,datum ,record) name
                (list (canonical-slice-reference-proof
                       (first subs) environment datum)))]
    [(or "A0-T-Natural" "A0-T-Top")
     (unless (null? subs)
       (error 'b2-reference-proofs "leaf oracle shape changed"))
     (b2-proof `(a0-type synth ,environment ,datum ,record) name '())]
    ["A0-T-Let"
     (unless (= (length subs) 2)
       (error 'b2-reference-proofs "A0-T-Let oracle shape changed"))
     (match datum
       [`(Let (,variable ,type) ,active ,body)
        (define body-environment (cons (list variable type) environment))
        (b2-proof
         `(a0-type synth ,environment ,datum ,record) name
         (list (canonical-slice-reference-proof
                (first subs) environment active)
               (canonical-slice-reference-proof
                (second subs) body-environment body)))]
       [_ (error 'b2-reference-proofs "Let proof has non-Let source ~e" datum)])]
    [_ (error 'b2-reference-proofs "oracle left the four-rule slice: ~e" name)]))

(define (b2-reference-proofs environment datum)
  (define proofs
    (for/list ([derivation
                (in-list (build-derivations
                          (a0-synth ,environment ,datum R)))])
      (canonical-slice-reference-proof derivation environment datum)))
  (b2-assert-no-execution-identities proofs 'b2-reference-proofs))

(define (b2-spike-supported? datum)
  (with-handlers ([exn:fail? (lambda (_) #f)])
    (define-values (root _) (b2-compile-term datum))
    (define (walk node)
      (cond
        [(and (eq? (b2-node-kind node) 'atom)
              (or (exact-nonnegative-integer? (b2-node-atom node))
                  (equal? (b2-node-atom node) '⊤)))
         #t]
        [else
         (match (b2-let-shape node)
           [(list _ _ _ active body)
            (and (b2-node-value-form? active) (walk active) (walk body))]
           [_ #f])]))
    (walk root)))

(define (median values)
  (define sorted (sort values <))
  (list-ref sorted (quotient (length sorted) 2)))

(define (micro-descendant-root depth serial)
  (define descendant
    (for/fold ([child (b2-node 'atom serial '() '(leaf) #t #f #f #f)])
              ([index (in-range depth)])
      (b2-node 'list #f (list child)
               (list 'descendant index) #f #f #f #f)))
  (b2-node 'list #f (list descendant)
           (list 'root serial depth) #f #f #f #f))

(define (run-b2-identity-trial depths repetitions trial)
  (define order
    (append (drop depths (modulo trial (length depths)))
            (take depths (modulo trial (length depths)))))
  (for/list ([depth (in-list order)])
    (define environment
        (b2-env
         (for/list ([index (in-range depth)])
           (list (string->symbol (format "$micro_~a" index)) 'Natural))
         '()))
    (define roots
      (for/list ([serial (in-range repetitions)])
        (micro-descendant-root depth (+ (* trial repetitions) serial))))
    (for ([root (in-list (take roots (min 20 (length roots))))])
      (void (judgment-holds (b2-identity-probe ,environment ,root))))
    (collect-garbage)
    (define started (current-inexact-monotonic-milliseconds))
    (for ([root (in-list roots)])
      (unless (judgment-holds
               (b2-identity-probe ,environment ,root))
        (error 'run-b2-identity-trial "identity probe failed")))
    (list depth
          (/ (- (current-inexact-monotonic-milliseconds) started)
             repetitions))))

(define-runtime-path identity-worker-path "port-b2-identity-worker.rkt")

(define (run-isolated-identity-trial depths repetitions trial)
  (define racket
    (or (find-executable-path "racket")
        (error 'run-b2-identity-micro "racket executable not found")))
  (define-values (process stdout stdin stderr)
    (subprocess #f #f #f racket identity-worker-path
                (format "~s" depths)
                (number->string repetitions)
                (number->string trial)))
  (close-output-port stdin)
  (define result (read stdout))
  (define error-output (port->string stderr))
  (subprocess-wait process)
  (unless (and (zero? (subprocess-status process))
               (list? result)
               (= (length result) (length depths)))
    (error 'run-b2-identity-micro
           "isolated trial ~a failed: result=~e stderr=~a"
           trial result error-output))
  result)

(define (run-b2-identity-micro #:depths [depths '(16 32 64)]
                               #:repetitions [repetitions 1200]
                               #:trials [trials 5]
                               #:limit [limit 1.5]
                               #:print? [print? #t])
  (define samples (make-hash))
  ;; Each trial is a fresh Racket process, so all Redex caches and runtime state
  ;; are isolated. The worker rotates depth order so drift cannot consistently
  ;; favor one descendant count; process startup is outside the timed region.
  (for ([trial (in-range trials)])
    (for ([sample
           (in-list (run-isolated-identity-trial
                     depths repetitions trial))])
      (match-define (list depth per-call) sample)
      (hash-update! samples depth (lambda (values) (cons per-call values)) '())))
  (define per-call-ms
    (for/list ([depth (in-list depths)])
      (median (hash-ref samples depth))))
  (define max-min-ratio
    (/ (apply max per-call-ms) (max 0.000001 (apply min per-call-ms))))
  ;; Treat a consistently ordered change as a descendant-count slope only when
  ;; it exceeds a 10% endpoint noise allowance. Strict ordering by a few timer
  ;; ticks (for example 1.014x end to end) is not structural growth.
  (define monotone-growth?
    (and (for/and ([left (in-list per-call-ms)]
                   [right (in-list (rest per-call-ms))])
           (< left right))
         (> (/ (last per-call-ms) (max 0.000001 (first per-call-ms)))
            1.1)))
  (define passed? (and (<= max-min-ratio limit) (not monotone-growth?)))
  (define report
    (b2-identity-micro depths per-call-ms max-min-ratio
                       monotone-growth? passed?))
  (when print?
    (printf "B2 identity micro: depths=~s per-call-ms=~s max/min=~a monotone-growth=~a limit=~ax result=~a\n"
            depths
            (map (lambda (value) (~r value #:precision '(= 6))) per-call-ms)
            (~r max-min-ratio #:precision '(= 3))
            monotone-growth? limit (if passed? 'pass 'FAIL)))
  report)

(define (b2-growth-term depth salt)
  (for/fold ([body '⊤]) ([index (in-range depth)])
    (define value (+ salt index))
    `(Let (,(string->symbol (format "$b2_growth_~a_~a" salt index)) Natural)
       ,value
       ,body)))

(struct growth-sample (total run) #:transparent)

(define (run-b2-spike-growth #:depths [depths '(16 32 64)]
                             #:factor [factor 4.0]
                             #:print? [print? #t])
  (unless (and (= (length depths) 3)
               (andmap exact-positive-integer? depths)
               (= (second depths) (* 2 (first depths)))
               (= (third depths) (* 2 (second depths))))
    (raise-argument-error
     'run-b2-spike-growth
     "three positive depths, each twice its predecessor" depths))
  (for ([depth (in-list depths)] [salt '(810000 820000 830000)])
    (define warm (b2-spike-query-synth '() (b2-growth-term depth salt)))
    (unless (= (length (b2-spike-run-records warm)) 1)
      (error 'run-b2-spike-growth "warm query has wrong result count")))
  (define medians
    (for/list ([depth (in-list depths)] [size-index (in-naturals 1)])
      (define samples
        (for/list ([trial (in-range 3)])
          (define salt (+ 900000 (* size-index 10000) (* trial 100000)))
          (define datum (b2-growth-term depth salt))
          (define started (current-inexact-monotonic-milliseconds))
          (define run (b2-spike-query-synth '() datum))
          (define total (- (current-inexact-monotonic-milliseconds) started))
          (unless (and (= (b2-spike-run-compile-count run) 1)
                       (= (b2-spike-run-node-count run)
                          (b2-raw-occurrence-count datum))
                       (= (length (b2-spike-run-records run)) 1))
            (error 'run-b2-spike-growth
                   "compile-count/node-count/derivation invariant failed"))
          (growth-sample total run)))
      (second (sort samples < #:key growth-sample-total))))
  (define total-ms (map growth-sample-total medians))
  (define compile-ms
    (map (lambda (sample)
           (b2-spike-run-compile-ms (growth-sample-run sample)))
         medians))
  (define judge-ms
    (map (lambda (sample)
           (b2-spike-run-judge-ms (growth-sample-run sample)))
         medians))
  (define node-count
    (map (lambda (sample)
           (b2-spike-run-node-count (growth-sample-run sample)))
         medians))
  (define ratios
    (for/list ([smaller (in-list total-ms)] [larger (in-list (rest total-ms))])
      (/ larger (max smaller 0.001))))
  (define passed? (andmap (lambda (ratio) (< ratio factor)) ratios))
  (define report
    (b2-spike-growth depths total-ms compile-ms judge-ms node-count
                     ratios passed?))
  (when print?
    (printf "B2 public compile+judge growth: depths=~s total-ms=~s compile-ms=~s judge-ms=~s nodes=~s ratios=~s limit=~ax result=~a\n"
            depths
            (map (lambda (value) (~r value #:precision '(= 3))) total-ms)
            (map (lambda (value) (~r value #:precision '(= 3))) compile-ms)
            (map (lambda (value) (~r value #:precision '(= 3))) judge-ms)
            node-count
            (map (lambda (value) (~r value #:precision '(= 3))) ratios)
            factor (if passed? 'pass 'FAIL)))
  report)
