#lang racket

(require racket/cmdline
         racket/list
         racket/format
         racket/match
         racket/set
         redex/reduction-semantics
         "port-support.rkt")

(provide SmusniA0
         a0-expand-let
         a0-expand-exactly
         a0-expand-global-exactly
         a0-expand-too-many
         a0-expand-massify
         a0-expand-zipwith
         a0-expand-close
         a0-hoist
         site-plan
         introducing?
         hoist-ordered
         replace-site
         a0-type
         a0-synth
         a0-check
         a0-required-rules
         a0-rule-anchors
         a0-coverage-report
         run-a0-generation-measurement
         run-a0-size-growth
         run-a0-gate
         (struct-out a0-generation)
         (struct-out a0-size-growth))

;; A0 is deliberately closed over the vertical-slice vocabulary. Generic
;; application remains a core formation form, but its atoms and types are no
;; longer `any`; the typing judgment decides which applications are licensed.
(define-language SmusniA0
  [x variable-not-otherwise-mentioned]
  [n natural]
  [label natural]
  [fill-label label Eventuality]
  [event-mode holding-state direct-event]
  [effect context refer projective effectful-call performance]
  [obligation finite-set-cardinality-defined variable-not-otherwise-mentioned]
  [force Assertion Expressive]
  [τ Entity Eventuality Number Natural Cardinal Content ClauseContent
     Discourse ThresholdKind
     (Referents τ) (Group τ) (List τ) (Set τ)
     (DecompositionBasis τ τ)
     (Act force) (ActOccurrence force)
     (Fn (τ ...) τ) (EFn (τ ...) τ)
     (RefComp τ) (PerfComp τ)]
  [direction synth (check τ)]
  [Γ ((x τ) ...)]
  [R (typing τ (effect ...) (obligation ...))]
  [lookup-result τ not-found]
  [constant Speaker Audience TooManyK ⊤]
  [t x n constant
     (λ ((x τ) ...) t)
     (Let (x τ) t t)
     (Bind ((x τ t) ...) t)
     (Context t ...)
     (Vague t)
     (Refer t)
     (SelectExactly t t)
     (SelectAtLeast t t)
     (SelectSome t)
     (SelectAllBut t t)
     (Exactly t t t)
     (No t t)
     (GlobalExactly t t t)
     (TooMany t t)
     (MoreThan t t t)
     (Massify t t)
     (Perform t)
     (CanonicalAggregateAt t t t)
     (AdmissibleThreshold t t t)
     (SetOf t)
     (Card t)
     (= t t)
     (∧ t t)
     (List t ...)
     (ZipWith t t t)
     (CoRef t t)
     (CloseClause t)
     (ActualClause t)
     (DirectClause t)
     (StateClause t)
     (Quote t)
     (Syntax t)
     (CloseWith ρdecl fills)
     (Site variable-not-otherwise-mentioned)
     (SiteValue variable-not-otherwise-mentioned)
     (t t ...)]
  [ρdecl (row variable-not-otherwise-mentioned n event-mode (label ...))]
  [fills ((fill-label t) ...)]
  [fill-result missing (found t)]
  [binding (x τ t)]
  [close-result (values (t ...) (binding ...))]
  [site-id variable-not-otherwise-mentioned]
  [dep (site site-id) (outer x τ) (member)]
  [role (context t ...) (vague t)]
  [width pure]
  [site-record (site site-id role τ width (deps dep ...))]
  [Σsites (sites site-record ...)]
  [bound-site (bound site-id x)]
  [hoist-result (ok t)
                (refusal member-dependent)
                (refusal introduction)
                (refusal malformed-metadata)]
  #:binding-forms
  (λ ((x τ) ...) t #:refers-to (shadow x ...))
  (Let (x τ) t_rhs t_body #:refers-to x)
  (Bind ((x τ t_rhs) #:...bind (clauses x (shadow clauses x)))
        t_body #:refers-to clauses))

(define-definition-metafunction SmusniA0
  a0-expand-let : x τ t t -> t
  (definition-case beta
    [(a0-expand-let x τ t_value t_body)
     ((λ ((x τ)) t_body) t_value)]))

(define-definition-metafunction SmusniA0
  a0-expand-exactly : n τ t t -> t
  (definition-case zero
    [(a0-expand-exactly 0 τ t_P t_Q)
     (No t_P t_Q)])
  (definition-case positive
    [(a0-expand-exactly n τ t_P t_Q)
     (Bind ((x_w (Referents τ) (SelectExactly n t_P)))
       (t_Q x_w))
     (side-condition (positive? (term n)))
     (where x_w ,(variable-not-in (term (τ t_P t_Q)) '$w))]))

(define-definition-metafunction SmusniA0
  a0-expand-global-exactly : n τ t t -> t
  (definition-case comprehension
    [(a0-expand-global-exactly n τ t_P t_Q)
     (= (Card
         (SetOf
          (λ ((x_member τ))
            (∧ (t_P x_member) (t_Q x_member)))))
        n)
     (where x_member
            ,(variable-not-in (term (n τ t_P t_Q)) '$global_member))]))

(define-definition-metafunction SmusniA0
  a0-expand-too-many : τ t t -> t
  (definition-case dependent-threshold
    [(a0-expand-too-many τ t_P t_Q)
     (Bind ((x_purpose (Referents Entity) (Context))
            (x_threshold Natural
                         (Vague
                          (AdmissibleThreshold TooManyK t_P x_purpose))))
       (MoreThan x_threshold t_P t_Q))
     (where x_purpose
            ,(variable-not-in (term (τ t_P t_Q)) '$purpose))
     (where x_threshold
            ,(variable-not-in (term (τ t_P t_Q x_purpose)) '$threshold))]))

(define-definition-metafunction SmusniA0
  a0-expand-massify : τ t t -> t
  (definition-case canonical-selection
    [(a0-expand-massify τ t_basis t_cover)
     (SelectExactly
      1
      (λ ((x_group (Group τ)))
        (CanonicalAggregateAt t_basis x_group t_cover)))
     (where x_group
            ,(variable-not-in (term (τ t_basis t_cover)) '$group))]))

(define-definition-metafunction SmusniA0
  a0-expand-zipwith : t t t -> t
  (definition-case empty
    [(a0-expand-zipwith t_f (List) (List)) ⊤])
  (definition-case paired-step
    [(a0-expand-zipwith t_f (List t_a t_as ...) (List t_b t_bs ...))
     (∧ (t_f t_a t_b)
        (ZipWith t_f (List t_as ...) (List t_bs ...)))]))

(define-metafunction SmusniA0
  fill-lookup : label fills -> fill-result
  [(fill-lookup label ()) missing]
  [(fill-lookup label ((label t_value) (fill-label_rest t_rest) ...))
   (found t_value)]
  [(fill-lookup label_1 ((fill-label_2 t_value)
                         (fill-label_rest t_rest) ...))
   (fill-lookup label_1 ((fill-label_rest t_rest) ...))
   (side-condition
    (not (equal? (term label_1) (term fill-label_2))))])

(define-metafunction SmusniA0
  event-fill : fills -> fill-result
  [(event-fill ()) missing]
  [(event-fill ((Eventuality t_event) (fill-label_rest t_rest) ...))
   (found t_event)]
  [(event-fill ((label t_value) (fill-label_rest t_rest) ...))
   (event-fill ((fill-label_rest t_rest) ...))])

(define-metafunction SmusniA0
  close-values : (label ...) fills (t ...) -> close-result
  [(close-values () fills (t_avoid ...)) (values () ())]
  [(close-values (label_0 label_rest ...) fills (t_avoid ...))
   (values (t_value t_values ...)
           (binding_rest ...))
   (where (found t_value) (fill-lookup label_0 fills))
   (where (values (t_values ...) (binding_rest ...))
          (close-values (label_rest ...) fills (t_avoid ...)))]
  [(close-values (label_0 label_rest ...) fills (t_avoid ...))
   (values (x_fresh t_values ...)
           ((x_fresh (Referents Entity) (Context)) binding_rest ...))
   (where missing (fill-lookup label_0 fills))
   (where x_fresh
          ,(variable-not-in (term (label_0 label_rest ... fills t_avoid ...))
                            (string->symbol
                             (format "$ctx~a" (term label_0)))))
   (where (values (t_values ...) (binding_rest ...))
          (close-values (label_rest ...) fills (t_avoid ... x_fresh)))])

(define-metafunction SmusniA0
  wrap-bindings : (binding ...) t -> t
  [(wrap-bindings () t_body) t_body]
  [(wrap-bindings (binding_0 binding_rest ...) t_body)
   (Bind (binding_0 binding_rest ...) t_body)])

(define (close-input-kind arity labels fills event-mode)
  (define fill-labels (map first fills))
  (define event-count (count (lambda (item) (eq? item 'Eventuality))
                             fill-labels))
  (define ordinary-fill-labels
    (filter exact-nonnegative-integer? fill-labels))
  (if (and (= arity (length labels))
           (andmap exact-positive-integer? labels)
           (= (length labels) (set-count (list->set labels)))
           (= (length fill-labels) (set-count (list->set fill-labels)))
           (= (length fill-labels)
              (+ event-count (length ordinary-fill-labels)))
           (andmap (lambda (item) (member item labels))
                   ordinary-fill-labels))
      (match* (event-mode event-count)
        [('holding-state 0) 'implicit]
        [('direct-event 0) 'implicit]
        [('direct-event 1) 'explicit]
        [(_ _) 'invalid])
      'invalid))

(define-definition-metafunction SmusniA0
  a0-expand-close : ρdecl fills -> t
  (definition-case holding-state
    [(a0-expand-close
      (row x_predicate n holding-state (label ...)) fills)
     (wrap-bindings
      (binding ...)
      (CloseClause
       (ActualClause
        (StateClause (x_predicate t_argument ...)))))
     (side-condition
      (equal? 'implicit
              (close-input-kind (term n) (term (label ...)) (term fills)
                                'holding-state)))
     (where (values (t_argument ...) (binding ...))
            (close-values (label ...) fills (x_predicate)))])
  (definition-case direct-event-implicit
    [(a0-expand-close
      (row x_predicate n direct-event (label ...)) fills)
     (wrap-bindings
      (binding ...)
      (CloseClause
       (ActualClause
        (DirectClause
         (λ ((x_event (Referents Eventuality)))
           (x_predicate t_argument ... x_event))))))
     (side-condition
      (equal? 'implicit
              (close-input-kind (term n) (term (label ...)) (term fills)
                                'direct-event)))
     (where x_event
            ,(variable-not-in (term (x_predicate fills label ...)) '$event))
     (where (values (t_argument ...) (binding ...))
            (close-values (label ...) fills (x_predicate x_event)))])
  (definition-case direct-event-explicit
    [(a0-expand-close
      (row x_predicate n direct-event (label ...)) fills)
     (wrap-bindings
      (binding ...)
      (CloseClause
       (λ ((x_clause_event (Referents Eventuality)))
         (∧ (CoRef x_clause_event t_supplied_event)
            ((ActualClause
              (DirectClause
               (λ ((x_lexical_event (Referents Eventuality)))
                 (x_predicate t_argument ... x_lexical_event))))
             t_supplied_event)))))
     (side-condition
      (equal? 'explicit
              (close-input-kind (term n) (term (label ...)) (term fills)
                                'direct-event)))
     (where (found t_supplied_event) (event-fill fills))
     (where x_lexical_event
            ,(variable-not-in
              (term (x_predicate fills label ... t_supplied_event))
              '$lexical_event))
     (where x_clause_event
            ,(variable-not-in
              (term (x_predicate fills label ... t_supplied_event
                                 x_lexical_event))
              '$clause_event))
     (where (values (t_argument ...) (binding ...))
            (close-values
             (label ...) fills
             (x_predicate t_supplied_event x_lexical_event x_clause_event)))])
  )

;; --------------------------------------------------------------------------
;; A0 L0.1 hoisting over adapter-supplied site data

(define (quoted-head? value)
  (and (pair? value) (member (first value) '(Quote Syntax))))

(define (executed-site-ids datum)
  (cond
    [(not (list? datum)) '()]
    [(quoted-head? datum) '()]
    [(match datum [`(Site ,(? symbol? id)) #t] [_ #f]) (list (second datum))]
    [else (append-map executed-site-ids datum)]))

(define (site-value-ids datum)
  (cond
    [(not (list? datum)) '()]
    [(quoted-head? datum) '()]
    [(match datum [`(SiteValue ,(? symbol? id)) #t] [_ #f]) (list (second datum))]
    [else (append-map site-value-ids datum)]))

(define (environment-has? environment variable type)
  (member (list variable type) environment))

(define (site-plan environment term-datum sites-datum)
  (match sites-datum
    [`(sites ,records ...)
     (define parsed
       (for/list ([record (in-list records)])
         (match record
           [`(site ,(? symbol? id) ,role ,type pure (deps ,deps ...))
            (list id role type deps record)]
           [_ #f])))
     (cond
       [(member #f parsed) 'malformed-metadata]
       [else
        (define ids (map first parsed))
        (define id-set (list->set ids))
        (define used-sites (remove-duplicates (executed-site-ids term-datum)))
        (cond
          [(not (= (length ids) (set-count id-set))) 'malformed-metadata]
          [(not (set=? id-set (list->set used-sites))) 'malformed-metadata]
          [(for/or ([item (in-list parsed)])
             (member '(member) (fourth item)))
           'member-dependent]
          [(for/or ([item (in-list parsed)])
             (for/or ([dependency (in-list (fourth item))])
               (match dependency
                 [`(site ,id) (not (set-member? id-set id))]
                 [`(outer ,variable ,type)
                  (not (environment-has? environment variable type))]
                 [`(member) #f]
                 [_ #t])))
           'malformed-metadata]
          [(for/or ([item (in-list parsed)])
             (define declared-site-deps
               (for/list ([dependency (in-list (fourth item))]
                          #:when (match dependency [`(site ,_) #t] [_ #f]))
                 (second dependency)))
             (not (subset? (list->set (site-value-ids (second item)))
                           (list->set declared-site-deps))))
           'malformed-metadata]
          [else
           (let loop ([remaining parsed] [bound (set)] [ordered '()])
             (cond
               [(null? remaining) `(ordered ,@(reverse ordered))]
               [else
                (define ready
                  (sort
                   (filter
                    (lambda (item)
                      (for/and ([dependency (in-list (fourth item))])
                        (match dependency
                          [`(site ,id) (set-member? bound id)]
                          [_ #t])))
                    remaining)
                   symbol<? #:key first))
                (if (null? ready)
                    'malformed-metadata
                    (let ([selected (first ready)])
                      (loop (remove selected remaining)
                            (set-add bound (first selected))
                            (cons (fifth selected) ordered))))]))])])]
    [_ 'malformed-metadata]))

(define (replace-marker-datum datum marker wanted replacement)
  (cond
    [(not (list? datum)) datum]
    [(quoted-head? datum) datum]
    [(and (= (length datum) 2)
          (eq? (first datum) marker)
          (equal? (second datum) wanted))
     replacement]
    [else
     (map (lambda (child)
            (replace-marker-datum child marker wanted replacement))
          datum)]))

(define-metafunction SmusniA0
  any-introducing? : (t ...) -> any
  [(any-introducing? ()) #f]
  [(any-introducing? (t_0 t_rest ...)) #t
   (where #t (introducing? t_0))]
  [(any-introducing? (t_0 t_rest ...))
   (any-introducing? (t_rest ...))
   (where #f (introducing? t_0))])

(define-metafunction SmusniA0
  introducing? : t -> any
  [(introducing? (Refer t)) #t]
  [(introducing? (SelectExactly t_1 t_2)) #t]
  [(introducing? (SelectAtLeast t_1 t_2)) #t]
  [(introducing? (SelectSome t)) #t]
  [(introducing? (SelectAllBut t_1 t_2)) #t]
  [(introducing? (Quote t)) #f]
  [(introducing? (Syntax t)) #f]
  [(introducing? (λ ((x τ) ...) t_body)) (introducing? t_body)]
  [(introducing? (Let (x τ) t_value t_body))
   (any-introducing? (t_value t_body))]
  [(introducing? (Bind ((x τ t_comp) ...) t_body))
   (any-introducing? (t_comp ... t_body))]
  [(introducing? (t_head t_arg ...))
   (any-introducing? (t_head t_arg ...))]
  [(introducing? t_atom) #f])

(define-metafunction SmusniA0
  replace-site : site-id x t -> t
  [(replace-site site-id x t)
   ,(replace-marker-datum (term t) 'Site (term site-id) (term x))])

(define-metafunction SmusniA0
  replace-site-values : (bound-site ...) t -> t
  [(replace-site-values () t) t]
  [(replace-site-values ((bound site-id x) bound-site_rest ...) t)
   (replace-site-value
    site-id x
    (replace-site-values (bound-site_rest ...) t))])

(define-metafunction SmusniA0
  replace-site-value : site-id x t -> t
  [(replace-site-value site-id x t)
   ,(replace-marker-datum (term t) 'SiteValue (term site-id) (term x))])

(define-metafunction SmusniA0
  site-computation : role (bound-site ...) -> t
  [(site-computation (context t_arg ...) (bound-site ...))
   (Context (replace-site-values (bound-site ...) t_arg) ...)]
  [(site-computation (vague t_constraint) (bound-site ...))
   (Vague (replace-site-values (bound-site ...) t_constraint))])

(define-metafunction SmusniA0
  hoist-ordered : (site-record ...) t (bound-site ...) -> t
  [(hoist-ordered () t_body (bound-site ...)) t_body]
  [(hoist-ordered
    ((site site-id role τ pure (deps dep ...)) site-record_rest ...)
    t_body (bound-site ...))
   (Bind ((x_site τ (site-computation role (bound-site ...))))
     (hoist-ordered
      (site-record_rest ...)
      (replace-site site-id x_site t_body)
      (bound-site ... (bound site-id x_site))))
   (where x_site
          ,(variable-not-in
            (term (site-id role τ dep ... site-record_rest ... t_body bound-site ...))
            (string->symbol
             (format "$site_~a" (term site-id)))))])

(define-definition-metafunction SmusniA0
  a0-hoist : Γ t Σsites -> hoist-result
  (definition-case introduction-refusal
    [(a0-hoist Γ t_body Σsites)
     (refusal introduction)
     (where #t (introducing? t_body))])
  (definition-case member-refusal
    [(a0-hoist Γ t_body Σsites)
     (refusal member-dependent)
     (where #f (introducing? t_body))
     (where member-dependent
            ,(site-plan (term Γ) (term t_body) (term Σsites)))])
  (definition-case malformed-refusal
    [(a0-hoist Γ t_body Σsites)
     (refusal malformed-metadata)
     (where #f (introducing? t_body))
     (where malformed-metadata
            ,(site-plan (term Γ) (term t_body) (term Σsites)))])
  (definition-case successful-hoist
    [(a0-hoist Γ t_body Σsites)
     (ok (hoist-ordered (site-record_1 ...) t_body ()))
     (where #f (introducing? t_body))
     (where (ordered site-record_1 ...)
            ,(site-plan (term Γ) (term t_body) (term Σsites)))]))

;; --------------------------------------------------------------------------
;; A0 two-mode typing judgment

(define (canonical-symbol-set values)
  (sort (remove-duplicates values) symbol<?))

(define (a0-compatible? actual expected)
  (or (equal? actual expected)
      (and (equal? actual 'Cardinal)
           (member expected '(Natural Number)))
      (and (equal? actual 'Natural) (equal? expected 'Number))
      (and (equal? actual 'ClauseContent)
           (member expected
                   '((Fn ((Referents Eventuality)) Content)
                     (EFn ((Referents Eventuality)) Content))
                   equal?))
      (and (equal? expected 'ClauseContent)
           (member actual
                   '((Fn ((Referents Eventuality)) Content)
                     (EFn ((Referents Eventuality)) Content))
                   equal?))
      (match expected
        [`(Referents ,inner) (a0-compatible? actual inner)]
        [_ #f])
      (match* (actual expected)
        [(`(,actual-arrow ,params ,result)
          `(,expected-arrow ,expected-params ,expected-result))
         #:when (and (member actual-arrow '(Fn EFn))
                     (member expected-arrow '(Fn EFn)))
         (and (or (equal? actual-arrow expected-arrow)
                  (and (equal? actual-arrow 'Fn)
                       (equal? expected-arrow 'EFn)))
              (= (length params) (length expected-params))
              (for/and ([actual-param (in-list params)]
                        [expected-param (in-list expected-params)])
                (a0-compatible? expected-param actual-param))
              (a0-compatible? result expected-result))]
        [(_ _) #f])))

(define (record-type datum)
  (match datum [`(typing ,type ,_ ,_) type]))
(define (record-effects datum)
  (match datum [`(typing ,_ ,effects ,_) effects]))
(define (record-obligations datum)
  (match datum [`(typing ,_ ,_ ,obligations) obligations]))

(define (merge-record-datums output records extra-effects extra-obligations)
  `(typing
    ,output
    ,(canonical-symbol-set
      (append extra-effects (append-map record-effects records)))
    ,(canonical-symbol-set
      (append extra-obligations (append-map record-obligations records)))))

(define (gq-extra-effects nuclear-type exports?)
  (canonical-symbol-set
   (append
    (if (match nuclear-type [`(EFn ,_ Content) #t] [_ #f])
        '(effectful-call) '())
    (if exports? '(refer) '()))))

(define-metafunction SmusniA0
  env-lookup : Γ x -> lookup-result
  [(env-lookup () x) not-found]
  [(env-lookup ((x τ) (x_rest τ_rest) ...) x) τ]
  [(env-lookup ((x_other τ_other) (x_rest τ_rest) ...) x)
   (env-lookup ((x_rest τ_rest) ...) x)
   (side-condition (not (equal? (term x_other) (term x))))])

(define-metafunction SmusniA0
  record-type-of : R -> τ
  [(record-type-of (typing τ (effect ...) (obligation ...))) τ])

(define-metafunction SmusniA0
  merge-records : τ (R ...) (effect ...) (obligation ...) -> R
  [(merge-records τ (R ...) (effect ...) (obligation ...))
   ,(merge-record-datums (term τ) (term (R ...))
                         (term (effect ...)) (term (obligation ...)))])

(define-metafunction SmusniA0
  nest-bind : (binding ...) t -> t
  [(nest-bind () t_body) t_body]
  [(nest-bind (binding_0) t_body) (Bind (binding_0) t_body)]
  [(nest-bind (binding_0 binding_1 binding_rest ...) t_body)
   (Bind (binding_0)
     (nest-bind (binding_1 binding_rest ...) t_body))])

(define-judgment-form SmusniA0
  #:mode (a0-type I I I O)
  #:contract (a0-type direction Γ t R)

  [----------------------------------------------- "A0-T-Natural"
   (a0-type synth Γ n (typing Natural () ()))]

  [----------------------------------------------- "A0-T-Speaker"
   (a0-type synth Γ Speaker (typing (Referents Entity) () ()))]

  [----------------------------------------------- "A0-T-Audience"
   (a0-type synth Γ Audience (typing (Referents Entity) () ()))]

  [----------------------------------------------- "A0-T-ThresholdKind"
   (a0-type synth Γ TooManyK (typing ThresholdKind () ()))]

  [----------------------------------------------- "A0-T-Top"
   (a0-type synth Γ ⊤ (typing Content () ()))]

  [(where τ (env-lookup Γ x))
   ----------------------------------------------- "A0-T-Variable"
   (a0-type synth Γ x (typing τ () ()))]

  [(a0-type synth ((x τ) (x_env τ_env) ...) t_body
            (typing τ_body () (obligation ...)))
   ----------------------------------------------- "A0-T-Lambda-Pure"
   (a0-type synth ((x_env τ_env) ...)
            (λ ((x τ)) t_body)
            (typing (Fn (τ) τ_body) () (obligation ...)))]

  [(a0-type synth ((x τ) (x_env τ_env) ...) t_body
            (typing τ_body (effect_0 effect_rest ...) (obligation ...)))
   ----------------------------------------------- "A0-T-Lambda-Effectful"
   (a0-type synth ((x_env τ_env) ...)
            (λ ((x τ)) t_body)
            (typing (EFn (τ) τ_body) () (obligation ...)))]

  [(a0-type synth
            ((x_0 τ_0) (x_1 τ_1) (x_rest τ_rest) ...
             (x_env τ_env) ...)
            t_body
            (typing τ_body () (obligation ...)))
   ----------------------------------------------- "A0-T-Lambda-Multi-Pure"
   (a0-type synth ((x_env τ_env) ...)
            (λ ((x_0 τ_0) (x_1 τ_1) (x_rest τ_rest) ...) t_body)
            (typing (Fn (τ_0 τ_1 τ_rest ...) τ_body)
                    () (obligation ...)))]

  [(a0-type synth
            ((x_0 τ_0) (x_1 τ_1) (x_rest τ_rest) ...
             (x_env τ_env) ...)
            t_body
            (typing τ_body (effect_0 effect_rest ...) (obligation ...)))
   ----------------------------------------------- "A0-T-Lambda-Multi-Effectful"
   (a0-type synth ((x_env τ_env) ...)
            (λ ((x_0 τ_0) (x_1 τ_1) (x_rest τ_rest) ...) t_body)
            (typing (EFn (τ_0 τ_1 τ_rest ...) τ_body)
                    () (obligation ...)))]

  [(a0-type (check τ) ((x_env τ_env) ...) t_value R_value)
   (a0-type synth ((x τ) (x_env τ_env) ...) t_body R_body)
   (where τ_body (record-type-of R_body))
   (where R_out (merge-records τ_body (R_value R_body) () ()))
   ----------------------------------------------- "A0-T-Let"
   (a0-type synth ((x_env τ_env) ...) (Let (x τ) t_value t_body) R_out)]

  [(where t_nested
          (nest-bind (binding_0 binding_1 binding_rest ...) t_body))
   (a0-type synth Γ t_nested R_out)
   ----------------------------------------------- "A0-T-Bind-Nest"
   (a0-type synth Γ
            (Bind (binding_0 binding_1 binding_rest ...) t_body)
            R_out)]

  [(a0-type (check (RefComp τ)) ((x_env τ_env) ...) t_comp R_comp)
   (a0-type synth ((x τ) (x_env τ_env) ...) t_body R_body)
   (where τ_body (record-type-of R_body))
   (where R_out (merge-records τ_body (R_comp R_body) () ()))
   ----------------------------------------------- "A0-T-Bind-Reference"
   (a0-type synth ((x_env τ_env) ...)
            (Bind ((x τ t_comp)) t_body) R_out)]

  [(a0-type (check (PerfComp τ)) ((x_env τ_env) ...) t_comp R_comp)
   (a0-type synth ((x τ) (x_env τ_env) ...) t_body
            (typing (Act force) (effect_body ...) (obligation_body ...)))
   (where R_out
          (merge-records Discourse
                         (R_comp
                          (typing (Act force)
                                  (effect_body ...) (obligation_body ...)))
                         (performance) ()))
   ----------------------------------------------- "A0-T-Bind-Performance-Act"
   (a0-type synth ((x_env τ_env) ...)
            (Bind ((x τ t_comp)) t_body) R_out)]

  [(a0-type (check (PerfComp τ)) ((x_env τ_env) ...) t_comp R_comp)
   (a0-type synth ((x τ) (x_env τ_env) ...) t_body
            (typing (PerfComp τ_body) (effect_body ...) (obligation_body ...)))
   (where R_out
          (merge-records (PerfComp τ_body)
                         (R_comp
                          (typing (PerfComp τ_body)
                                  (effect_body ...) (obligation_body ...)))
                         () ()))
   ----------------------------------------------- "A0-T-Bind-Performance-Comp"
   (a0-type synth ((x_env τ_env) ...)
            (Bind ((x τ t_comp)) t_body) R_out)]

  [(a0-type (check (PerfComp τ)) ((x_env τ_env) ...) t_comp R_comp)
   (a0-type synth ((x τ) (x_env τ_env) ...) t_body
            (typing Discourse (effect_body ...) (obligation_body ...)))
   (where R_out
          (merge-records Discourse
                         (R_comp
                          (typing Discourse
                                  (effect_body ...) (obligation_body ...)))
                         () ()))
   ----------------------------------------------- "A0-T-Bind-Performance-Discourse"
   (a0-type synth ((x_env τ_env) ...)
            (Bind ((x τ t_comp)) t_body) R_out)]

  [(a0-type synth Γ t_actual R_actual)
   (where τ_actual (record-type-of R_actual))
   (side-condition
    ,(a0-compatible? (term τ_actual) (term τ_expected)))
   ----------------------------------------------- "A0-T-Check-Synth"
   (a0-type (check τ_expected) Γ t_actual R_actual)]

  [(a0-type synth Γ t_argument R_argument) ...
   (where R_out
          (merge-records (RefComp τ) (R_argument ...) (context) ()))
   ----------------------------------------------- "A0-T-Context"
   (a0-type (check (RefComp τ)) Γ (Context t_argument ...) R_out)]

  [(a0-type synth Γ t_property
            (typing (Fn (τ) Content) () (obligation ...)))
   ----------------------------------------------- "A0-T-Vague"
   (a0-type (check (RefComp τ)) Γ (Vague t_property)
            (typing (RefComp τ) (context) (obligation ...)))]

  [(a0-type synth Γ t_property
            (typing (Fn ((Referents τ)) Content) () (obligation ...)))
   (where R_out
          (merge-records
           (RefComp (Referents τ))
           ((typing (Fn ((Referents τ)) Content) () (obligation ...)))
           (refer) ()))
   ----------------------------------------------- "A0-T-Refer-Reference"
   (a0-type (check (RefComp (Referents τ))) Γ (Refer t_property) R_out)]

  [(a0-type synth Γ t_property
            (typing (Fn (τ) Content) () (obligation ...)))
   (where R_out
          (merge-records
           (RefComp (Referents τ))
           ((typing (Fn (τ) Content) () (obligation ...)))
           (refer) ()))
   ----------------------------------------------- "A0-T-Refer-Member"
   (a0-type (check (RefComp (Referents τ))) Γ (Refer t_property) R_out)]

  [(a0-type (check Natural) Γ t_count R_count)
   (a0-type synth Γ t_property
            (typing (Fn (τ) Content) () (obligation ...)))
   (where R_out
          (merge-records (RefComp (Referents τ))
                         (R_count
                          (typing (Fn (τ) Content) () (obligation ...)))
                         (refer) ()))
   ----------------------------------------------- "A0-T-SelectExactly"
   (a0-type (check (RefComp (Referents τ))) Γ
            (SelectExactly t_count t_property) R_out)]

  [(a0-type synth Γ t_property
            (typing (Fn (τ) Content) () (obligation ...)))
   (where R_out
          (merge-records
           (RefComp (Referents τ))
           ((typing (Fn (τ) Content) () (obligation ...)))
           (refer) ()))
   ----------------------------------------------- "A0-T-SelectSome"
   (a0-type (check (RefComp (Referents τ))) Γ
            (SelectSome t_property) R_out)]

  [(a0-type synth Γ t_basis
            (typing (DecompositionBasis (Group τ) τ)
                    (effect_basis ...) (obligation_basis ...)))
   (a0-type (check (Referents τ)) Γ t_cover R_cover)
   (where R_out
          (merge-records
           (RefComp (Referents (Group τ)))
           ((typing (DecompositionBasis (Group τ) τ)
                    (effect_basis ...) (obligation_basis ...))
            R_cover)
           (refer) ()))
   ----------------------------------------------- "A0-T-Massify"
   (a0-type (check (RefComp (Referents (Group τ)))) Γ
            (Massify t_basis t_cover) R_out)]

  [(a0-type synth Γ t_act
            (typing (Act force) (effect ...) (obligation ...)))
   ----------------------------------------------- "A0-T-Perform"
   (a0-type synth Γ (Perform t_act)
            (typing (PerfComp (ActOccurrence force))
                    (performance) (obligation ...)))]

  [(a0-type synth Γ t_P R_P)
   (where (Fn (τ) Content) (record-type-of R_P))
   (a0-type (check (EFn ((Referents τ)) Content)) Γ t_Q R_Q)
   (where R_n (typing Natural () ()))
   (where (effect_extra ...)
          ,(gq-extra-effects (term (record-type-of R_Q)) #f))
   (where R_out
          (merge-records Content (R_n R_P R_Q) (effect_extra ...) ()))
   ----------------------------------------------- "A0-T-Exactly-Zero"
   (a0-type synth Γ (Exactly 0 t_P t_Q) R_out)]

  [(a0-type (check Natural) Γ n_1 R_n)
   (side-condition ,(positive? (term n_1)))
   (a0-type synth Γ t_P R_P)
   (where (Fn (τ) Content) (record-type-of R_P))
   (a0-type (check (EFn ((Referents τ)) Content)) Γ t_Q R_Q)
   (where (effect_extra ...)
          ,(gq-extra-effects (term (record-type-of R_Q)) #t))
   (where R_out
          (merge-records Content (R_n R_P R_Q) (effect_extra ...) ()))
   ----------------------------------------------- "A0-T-Exactly-Positive"
   (a0-type synth Γ (Exactly n_1 t_P t_Q) R_out)]

  [(a0-type synth Γ t_P R_P)
   (where (Fn (τ) Content) (record-type-of R_P))
   (a0-type (check (EFn ((Referents τ)) Content)) Γ t_Q R_Q)
   (where (effect_extra ...)
          ,(gq-extra-effects (term (record-type-of R_Q)) #f))
   (where R_out (merge-records Content (R_P R_Q) (effect_extra ...) ()))
   ----------------------------------------------- "A0-T-No"
   (a0-type synth Γ (No t_P t_Q) R_out)]

  [(a0-type (check Natural) Γ t_n R_n)
   (a0-type synth Γ t_P R_P)
   (where (Fn (τ) Content) (record-type-of R_P))
   (a0-type (check (EFn ((Referents τ)) Content)) Γ t_Q R_Q)
   (where (effect_extra ...)
          ,(gq-extra-effects (term (record-type-of R_Q)) #t))
   (where R_out
          (merge-records Content (R_n R_P R_Q) (effect_extra ...) ()))
   ----------------------------------------------- "A0-T-MoreThan"
   (a0-type synth Γ (MoreThan t_n t_P t_Q) R_out)]

  [(a0-type (check Natural) Γ t_n R_n)
   (a0-type synth Γ t_P R_P)
   (where (Fn (τ) Content) (record-type-of R_P))
   (a0-type (check (Fn (τ) Content)) Γ t_Q R_Q)
   (where R_out
          (merge-records Content (R_n R_P R_Q)
                         (projective) (finite-set-cardinality-defined)))
   ----------------------------------------------- "A0-T-GlobalExactly"
   (a0-type synth Γ (GlobalExactly t_n t_P t_Q) R_out)]

  [(a0-type synth Γ t_P R_P)
   (where (Fn (τ) Content) (record-type-of R_P))
   (a0-type (check (EFn ((Referents τ)) Content)) Γ t_Q R_Q)
   (where (effect_extra ...)
          ,(canonical-symbol-set
            (append '(context refer)
                    (gq-extra-effects (term (record-type-of R_Q)) #f))))
   (where R_out (merge-records Content (R_P R_Q) (effect_extra ...) ()))
   ----------------------------------------------- "A0-T-TooMany"
   (a0-type synth Γ (TooMany t_P t_Q) R_out)]

  [(a0-type (check ThresholdKind) Γ t_kind R_kind)
   (a0-type synth Γ t_P R_P)
   (where (Fn (τ) Content) (record-type-of R_P))
   (a0-type (check (Referents Entity)) Γ t_purpose R_purpose)
   (where R_out
          (merge-records (Fn (Natural) Content)
                         (R_kind R_P R_purpose) () ()))
   ----------------------------------------------- "A0-T-AdmissibleThreshold"
   (a0-type synth Γ
            (AdmissibleThreshold t_kind t_P t_purpose) R_out)]

  [(a0-type synth Γ t_basis R_basis)
   (where (DecompositionBasis (Group τ) τ) (record-type-of R_basis))
   (a0-type (check (Group τ)) Γ t_group R_group)
   (a0-type (check (Referents τ)) Γ t_cover R_cover)
   (where R_out
          (merge-records Content (R_basis R_group R_cover) () ()))
   ----------------------------------------------- "A0-T-CanonicalAggregateAt"
   (a0-type synth Γ
            (CanonicalAggregateAt t_basis t_group t_cover) R_out)]

  [(a0-type synth Γ t_P R_P)
   (where (Fn (τ) Content) (record-type-of R_P))
   (where R_out (merge-records (Set τ) (R_P) () ()))
   ----------------------------------------------- "A0-T-SetOf"
   (a0-type synth Γ (SetOf t_P) R_out)]

  [(a0-type synth Γ t_set R_set)
   (where (Set τ) (record-type-of R_set))
   (where R_out
          (merge-records Cardinal (R_set) (projective)
                         (finite-set-cardinality-defined)))
   ----------------------------------------------- "A0-T-Card"
   (a0-type synth Γ (Card t_set) R_out)]

  [(a0-type synth Γ t_left R_left)
   (a0-type synth Γ t_right R_right)
   (where τ_left (record-type-of R_left))
   (where τ_right (record-type-of R_right))
   (side-condition
    ,(or (a0-compatible? (term τ_left) (term τ_right))
         (a0-compatible? (term τ_right) (term τ_left))))
   (where R_out
          (merge-records Content (R_left R_right) () ()))
   ----------------------------------------------- "A0-T-Equality"
   (a0-type synth Γ (= t_left t_right) R_out)]

  [(a0-type (check Content) Γ t_left R_left)
   (a0-type (check Content) Γ t_right R_right)
   (where R_out (merge-records Content (R_left R_right) () ()))
   ----------------------------------------------- "A0-T-And"
   (a0-type synth Γ (∧ t_left t_right) R_out)]

  [(a0-type (check (Referents Eventuality)) Γ t_left R_left)
   (a0-type (check (Referents Eventuality)) Γ t_right R_right)
   (where R_out (merge-records Content (R_left R_right) () ()))
   ----------------------------------------------- "A0-T-CoRef"
   (a0-type synth Γ (CoRef t_left t_right) R_out)]

  [(a0-type (check τ) Γ t_item R_item) ...
   (where R_out (merge-records (List τ) (R_item ...) () ()))
   ----------------------------------------------- "A0-T-List-Check"
   (a0-type (check (List τ)) Γ (List t_item ...) R_out)]

  [(a0-type synth Γ t_f
            (typing (Fn (τ_left τ_right) Content)
                    (effect_f ...) (obligation_f ...)))
   (a0-type (check (List τ_left)) Γ t_left R_left)
   (a0-type (check (List τ_right)) Γ t_right R_right)
   (where R_out
          (merge-records Content
                         ((typing (Fn (τ_left τ_right) Content)
                                  (effect_f ...) (obligation_f ...))
                          R_left R_right)
                         () ()))
   ----------------------------------------------- "A0-T-ZipWith-Pure"
   (a0-type synth Γ (ZipWith t_f t_left t_right) R_out)]

  [(a0-type synth Γ t_f
            (typing (EFn (τ_left τ_right) Content)
                    (effect_f ...) (obligation_f ...)))
   (a0-type (check (List τ_left)) Γ t_left R_left)
   (a0-type (check (List τ_right)) Γ t_right R_right)
   (where R_out
          (merge-records Content
                         ((typing (EFn (τ_left τ_right) Content)
                                  (effect_f ...) (obligation_f ...))
                          R_left R_right)
                         (effectful-call) ()))
   ----------------------------------------------- "A0-T-ZipWith-Effectful"
   (a0-type synth Γ (ZipWith t_f t_left t_right) R_out)]

  [(a0-type (check Content) Γ t_content R_content)
   (where R_out (merge-records ClauseContent (R_content) () ()))
   ----------------------------------------------- "A0-T-StateClause"
   (a0-type synth Γ (StateClause t_content) R_out)]

  [(a0-type synth Γ t_property
            (typing (Fn ((Referents Eventuality)) Content)
                    (effect_property ...) (obligation ...)))
   (where R_out
          (merge-records
           ClauseContent
           ((typing (Fn ((Referents Eventuality)) Content)
                    (effect_property ...) (obligation ...)))
           () ()))
   ----------------------------------------------- "A0-T-DirectClause-Pure"
   (a0-type synth Γ (DirectClause t_property) R_out)]

  [(a0-type synth Γ t_property
            (typing (EFn ((Referents Eventuality)) Content)
                    (effect_property ...) (obligation ...)))
   (where R_out
          (merge-records
           ClauseContent
           ((typing (EFn ((Referents Eventuality)) Content)
                    (effect_property ...) (obligation ...)))
           () ()))
   ----------------------------------------------- "A0-T-DirectClause-Effectful"
   (a0-type synth Γ (DirectClause t_property) R_out)]

  [(a0-type synth Γ t_clause
            (typing ClauseContent (effect_clause ...) (obligation ...)))
   (where R_out
          (merge-records
           ClauseContent
           ((typing ClauseContent (effect_clause ...) (obligation ...)))
           () ()))
   ----------------------------------------------- "A0-T-ActualClause-State"
   (a0-type synth Γ (ActualClause t_clause) R_out)]

  [(a0-type synth Γ t_property R_property)
   (where (Fn ((Referents Eventuality)) Content)
          (record-type-of R_property))
   (where R_out (merge-records ClauseContent (R_property) () ()))
   ----------------------------------------------- "A0-T-ActualClause-Event-Pure"
   (a0-type synth Γ (ActualClause t_property) R_out)]

  [(a0-type synth Γ t_property R_property)
   (where (EFn ((Referents Eventuality)) Content)
          (record-type-of R_property))
   (where R_out (merge-records ClauseContent (R_property) () ()))
   ----------------------------------------------- "A0-T-ActualClause-Event-Effectful"
   (a0-type synth Γ (ActualClause t_property) R_out)]

  [(a0-type (check ClauseContent) Γ t_clause R_clause)
   (where R_out (merge-records Content (R_clause) () ()))
   ----------------------------------------------- "A0-T-CloseClause"
   (a0-type synth Γ (CloseClause t_clause) R_out)]

  [(where t_expanded (a0-expand-close ρdecl fills))
   (a0-type synth Γ t_expanded R_out)
   ----------------------------------------------- "A0-T-CloseWith"
   (a0-type synth Γ (CloseWith ρdecl fills) R_out)]

  [(a0-type synth Γ t_function
            (typing ClauseContent
                    (effect_function ...) (obligation_function ...)))
   (a0-type (check (Referents Eventuality)) Γ t_argument R_argument)
   (where R_out
          (merge-records
           Content
           ((typing ClauseContent
                    (effect_function ...) (obligation_function ...))
            R_argument)
           (effectful-call) ()))
   ----------------------------------------------- "A0-T-Apply-ClauseContent"
   (a0-type synth Γ (t_function t_argument) R_out)]

  [(a0-type synth Γ t_function
            (typing (Fn (τ_arg ...) τ_result)
                    (effect_function ...) (obligation_function ...)))
   (a0-type (check τ_arg) Γ t_argument R_argument) ...
   (where R_out
          (merge-records τ_result
                         ((typing (Fn (τ_arg ...) τ_result)
                                  (effect_function ...)
                                  (obligation_function ...))
                          R_argument ...)
                         () ()))
   ----------------------------------------------- "A0-T-Apply-Pure"
   (a0-type synth Γ (t_function t_argument ...) R_out)]

  [(a0-type synth Γ t_function
            (typing (EFn (τ_arg ...) τ_result)
                    (effect_function ...) (obligation_function ...)))
   (a0-type (check τ_arg) Γ t_argument R_argument) ...
   (where R_out
          (merge-records τ_result
                         ((typing (EFn (τ_arg ...) τ_result)
                                  (effect_function ...)
                                  (obligation_function ...))
                          R_argument ...)
                         (effectful-call) ()))
   ----------------------------------------------- "A0-T-Apply-Effectful"
   (a0-type synth Γ (t_function t_argument ...) R_out)])

(define-judgment-form SmusniA0
  #:mode (a0-synth I I O)
  #:contract (a0-synth Γ t R)
  [(a0-type synth Γ t R)
   ----------------------------------------------- "A0-Synth"
   (a0-synth Γ t R)])

(define-judgment-form SmusniA0
  #:mode (a0-check I I I O)
  #:contract (a0-check Γ t τ R)
  [(a0-type (check τ) Γ t R)
   ----------------------------------------------- "A0-Check"
   (a0-check Γ t τ R)])

;; --------------------------------------------------------------------------
;; A0 verification reports

(define a0-required-rules
  '("A0-Synth" "A0-Check"
    "A0-T-Natural" "A0-T-Speaker" "A0-T-Audience"
    "A0-T-ThresholdKind" "A0-T-Top" "A0-T-Variable"
    "A0-T-Lambda-Pure" "A0-T-Lambda-Effectful"
    "A0-T-Lambda-Multi-Pure" "A0-T-Lambda-Multi-Effectful" "A0-T-Let"
    "A0-T-Bind-Nest" "A0-T-Bind-Reference"
    "A0-T-Bind-Performance-Act" "A0-T-Bind-Performance-Comp"
    "A0-T-Bind-Performance-Discourse" "A0-T-Check-Synth"
    "A0-T-Context" "A0-T-Vague" "A0-T-Refer-Reference"
    "A0-T-Refer-Member" "A0-T-SelectExactly" "A0-T-SelectSome"
    "A0-T-Massify" "A0-T-Perform" "A0-T-Exactly-Zero"
    "A0-T-Exactly-Positive" "A0-T-No" "A0-T-MoreThan"
    "A0-T-GlobalExactly" "A0-T-TooMany" "A0-T-AdmissibleThreshold"
    "A0-T-CanonicalAggregateAt" "A0-T-SetOf" "A0-T-Card"
    "A0-T-Equality" "A0-T-And" "A0-T-CoRef" "A0-T-List-Check"
    "A0-T-ZipWith-Pure" "A0-T-ZipWith-Effectful"
    "A0-T-StateClause" "A0-T-DirectClause-Pure"
    "A0-T-DirectClause-Effectful" "A0-T-ActualClause-State"
    "A0-T-ActualClause-Event-Pure" "A0-T-ActualClause-Event-Effectful"
    "A0-T-CloseClause" "A0-T-CloseWith"
    "A0-T-Apply-ClauseContent"
    "A0-T-Apply-Pure" "A0-T-Apply-Effectful"))

;; Adjacent provenance table required by the A0 brief. These are normative
;; formation/typing anchors, not claims that the derived Redex rule is itself
;; semantic authority.
(define a0-rule-anchors
  '(("A0-Synth" "spec §1.6, §3")
    ("A0-Check" "spec §1.6, §3")
    ("A0-T-Check-Synth" "spec §1.6, §3")
    ("A0-T-Natural" "spec §3.1")
    ("A0-T-Speaker" "spec §5.1")
    ("A0-T-Audience" "spec §5.1")
    ("A0-T-ThresholdKind" "spec §6.4")
    ("A0-T-Top" "spec §4.5")
    ("A0-T-Variable" "spec §4.4")
    ("A0-T-Lambda-Pure" "spec §3.3, §4.4")
    ("A0-T-Lambda-Effectful" "spec §3.3, §4.4")
    ("A0-T-Lambda-Multi-Pure" "spec §3.3, §4.4")
    ("A0-T-Lambda-Multi-Effectful" "spec §3.3, §4.4")
    ("A0-T-Let" "spec §4.4; §12 Let")
    ("A0-T-Bind-Nest" "spec §4.4, §5.2")
    ("A0-T-Bind-Reference" "spec §5.2")
    ("A0-T-Bind-Performance-Act" "spec §5.2, §7.1")
    ("A0-T-Bind-Performance-Comp" "spec §5.2, §7.1")
    ("A0-T-Bind-Performance-Discourse" "spec §5.2, §7.1")
    ("A0-T-Context" "spec §5.1")
    ("A0-T-Vague" "spec §6.4–§6.5")
    ("A0-T-Refer-Reference" "spec §5.3")
    ("A0-T-Refer-Member" "spec §5.3")
    ("A0-T-SelectExactly" "spec §5.6")
    ("A0-T-SelectSome" "spec §5.6")
    ("A0-T-Massify" "spec §4.8; §12 Massify")
    ("A0-T-Perform" "spec §7.1")
    ("A0-T-Exactly-Zero" "spec §4.10; §12 Exactly")
    ("A0-T-Exactly-Positive" "spec §4.10; §12 Exactly")
    ("A0-T-No" "spec §4.10; §12 No")
    ("A0-T-MoreThan" "spec §4.10; §12 MoreThan")
    ("A0-T-GlobalExactly" "spec §4.10; §12 GlobalExactly")
    ("A0-T-TooMany" "spec §6.4; §12 TooMany")
    ("A0-T-AdmissibleThreshold" "spec §6.4")
    ("A0-T-CanonicalAggregateAt" "spec §4.8")
    ("A0-T-SetOf" "spec §4.9")
    ("A0-T-Card" "spec §4.9")
    ("A0-T-Equality" "spec §4.9")
    ("A0-T-And" "spec §4.5")
    ("A0-T-CoRef" "spec §4.5")
    ("A0-T-List-Check" "spec §4.9")
    ("A0-T-ZipWith-Pure" "spec §4.9; §12 ZipWith")
    ("A0-T-ZipWith-Effectful" "spec §4.9; §12 ZipWith")
    ("A0-T-StateClause" "spec §4.6")
    ("A0-T-DirectClause-Pure" "spec §4.6")
    ("A0-T-DirectClause-Effectful" "spec §4.6")
    ("A0-T-ActualClause-State" "spec §4.6")
    ("A0-T-ActualClause-Event-Pure" "spec §4.6")
    ("A0-T-ActualClause-Event-Effectful" "spec §4.6")
    ("A0-T-CloseClause" "spec §4.6")
    ("A0-T-CloseWith" "spec §4.6")
    ("A0-T-Apply-ClauseContent" "spec §3.4, §4.6")
    ("A0-T-Apply-Pure" "spec §3.3, §4.4")
    ("A0-T-Apply-Effectful" "spec §3.3, §4.4")))

(define a0-coverage-probes
  `((synth () 3)
    (synth () Speaker)
    (synth () Audience)
    (synth () TooManyK)
    (synth () ⊤)
    (synth (($x Entity)) $x)
    (synth () (λ (($x Entity)) ⊤))
    (synth () (λ (($x Entity))
                (Bind (($s (Referents Entity) (Context))) ⊤)))
    (synth () (λ (($x Entity) ($y Entity)) ⊤))
    (synth () (λ (($x Entity) ($y Entity))
                (Bind (($s (Referents Entity) (Context))) ⊤)))
    (synth (($v Entity)) (Let ($x Entity) $v $x))
    (synth () (Bind (($x (Referents Entity) (Context))
                     ($y (Referents Entity) (Context))) ⊤))
    (synth () (Bind (($x (Referents Entity) (Context))) ⊤))
    (synth (($act (Act Assertion)))
           (Bind (($o (ActOccurrence Assertion) (Perform $act))) $act))
    (synth (($pc (PerfComp Entity)))
           (Bind (($x Entity $pc)) $pc))
    (synth (($pc (PerfComp Entity)) ($d Discourse))
           (Bind (($x Entity $pc)) $d))
    (check () (Context) (RefComp (Referents Entity)))
    (check () (Vague (λ (($n Natural)) ⊤)) (RefComp Natural))
    (check () (Refer (λ (($r (Referents Entity))) ⊤))
           (RefComp (Referents Entity)))
    (check () (Refer (λ (($x Entity)) ⊤))
           (RefComp (Referents Entity)))
    (check () (SelectExactly 2 (λ (($x Entity)) ⊤))
           (RefComp (Referents Entity)))
    (check () (SelectSome (λ (($x Entity)) ⊤))
           (RefComp (Referents Entity)))
    (check (($basis (DecompositionBasis (Group Entity) Entity))
            ($cover (Referents Entity)))
           (Massify $basis $cover)
           (RefComp (Referents (Group Entity))))
    (synth (($act (Act Assertion))) (Perform $act))
    (synth ((P (Fn (Entity) Content))
            (Q (EFn ((Referents Entity)) Content)))
           (Exactly 0 P Q))
    (synth ((P (Fn (Entity) Content))
            (Q (EFn ((Referents Entity)) Content)))
           (Exactly 2 P Q))
    (synth ((P (Fn (Entity) Content))
            (Q (EFn ((Referents Entity)) Content)))
           (No P Q))
    (synth ((P (Fn (Entity) Content))
            (Q (EFn ((Referents Entity)) Content)))
           (MoreThan 2 P Q))
    (synth ((P (Fn (Entity) Content)) (Q (Fn (Entity) Content)))
           (GlobalExactly 2 P Q))
    (synth ((P (Fn (Entity) Content))
            (Q (EFn ((Referents Entity)) Content)))
           (TooMany P Q))
    (synth ((P (Fn (Entity) Content)))
           (AdmissibleThreshold TooManyK P Speaker))
    (synth (($basis (DecompositionBasis (Group Entity) Entity))
            ($group (Group Entity)) ($cover (Referents Entity)))
           (CanonicalAggregateAt $basis $group $cover))
    (synth () (SetOf (λ (($x Entity)) ⊤)))
    (synth () (Card (SetOf (λ (($x Entity)) ⊤))))
    (synth () (= 1 2))
    (synth () (∧ ⊤ ⊤))
    (synth (($left (Referents Eventuality))
            ($right (Referents Eventuality)))
           (CoRef $left $right))
    (check () (List Speaker Audience) (List (Referents Entity)))
    (synth ((f (Fn ((Referents Entity) (Referents Entity)) Content)))
           (ZipWith f (List Speaker) (List Audience)))
    (synth ((f (EFn ((Referents Entity) (Referents Entity)) Content)))
           (ZipWith f (List Speaker) (List Audience)))
    (synth () (StateClause ⊤))
    (synth ()
           (DirectClause (λ (($e (Referents Eventuality))) ⊤)))
    (synth (($event-property
             (EFn ((Referents Eventuality)) Content)))
           (DirectClause $event-property))
    (synth () (ActualClause (StateClause ⊤)))
    (synth () (ActualClause (λ (($e (Referents Eventuality))) ⊤)))
    (synth (($event-property
             (EFn ((Referents Eventuality)) Content)))
           (ActualClause $event-property))
    (synth () (CloseClause (StateClause ⊤)))
    (synth ((tavla
             (Fn ((Referents Entity) (Referents Entity) (Referents Entity))
                 Content)))
           (CloseWith (row tavla 3 holding-state (1 2 3))
                      ((1 Speaker) (2 Audience))))
    (synth (($clause ClauseContent)
            ($event (Referents Eventuality)))
           ($clause $event))
    (synth ((f (Fn (Natural) Content))) (f 1))
    (synth ((f (EFn (Natural) Content))) (f 1))))

(define (derivation-rule-names derivation)
  (append (if (derivation-name derivation)
              (list (derivation-name derivation)) '())
          (append-map derivation-rule-names (derivation-subs derivation))))

(define (probe-derivations probe)
  (define derivations
    (match probe
      [`(synth ,environment ,term-datum)
       (build-derivations (a0-synth ,environment ,term-datum R))]
      [`(check ,environment ,term-datum ,type)
       (build-derivations (a0-check ,environment ,term-datum ,type R))]))
  (unless (= (length derivations) 1)
    (error 'a0-coverage-report
           "coverage probe has ~a derivations: ~e"
           (length derivations) probe))
  derivations)

(define (exercise-definition-coverage)
  (define coverages
    (list (make-coverage a0-expand-let)
          (make-coverage a0-expand-exactly)
          (make-coverage a0-expand-global-exactly)
          (make-coverage a0-expand-too-many)
          (make-coverage a0-expand-massify)
          (make-coverage a0-expand-zipwith)
          (make-coverage a0-expand-close)
          (make-coverage a0-hoist)))
  (parameterize ([relation-coverage coverages])
    (term (a0-expand-let $x Entity Speaker (P $x)))
    (term (a0-expand-exactly 0 Entity P Q))
    (term (a0-expand-exactly 2 Entity P Q))
    (term (a0-expand-global-exactly 2 Entity P Q))
    (term (a0-expand-too-many Entity P Q))
    (term (a0-expand-massify Entity $basis $cover))
    (term (a0-expand-zipwith f (List) (List)))
    (term (a0-expand-zipwith f (List a) (List b)))
    (term (a0-expand-close (row p 1 holding-state (1)) ()))
    (term (a0-expand-close (row p 1 direct-event (1)) ()))
    (term (a0-expand-close (row p 1 direct-event (1))
                           ((Eventuality $shared-event))))
    (term (a0-hoist () (λ (($x Entity)) ⊤) (sites)))
    (term (a0-hoist ()
                    (λ (($x Entity)) (SelectSome (λ (($y Entity)) ⊤)))
                    (sites)))
    (term (a0-hoist () (λ (($x Entity)) (P $x (Site s)))
                    (sites (site s (context) (Referents Entity) pure
                                  (deps (member))))))
    (term (a0-hoist () (λ (($x Entity)) (P $x (Site s)))
                    (sites
                     (site s (context $missing) (Referents Entity) pure
                           (deps (outer $missing (Referents Entity))))))))
  (append-map covered-cases coverages))

(define (a0-coverage-report #:print? [print? #t])
  (define anchor-names (map first a0-rule-anchors))
  (unless (and (= (length anchor-names)
                  (length (remove-duplicates anchor-names)))
               (equal? (sort anchor-names string<?)
                       (sort a0-required-rules string<?)))
    (error 'a0-coverage-report
           "rule-anchor table does not exactly cover the required rules"))
  (define derivations (append-map probe-derivations a0-coverage-probes))
  (define witnessed
    (remove-duplicates (append-map derivation-rule-names derivations)))
  (define uncovered
    (filter (lambda (name) (not (member name witnessed))) a0-required-rules))
  (define native (exercise-definition-coverage))
  (when print?
    (printf "A0 derivation-rule coverage: witnessed=~a required=~a uncovered=~s\n"
            (length witnessed) (length a0-required-rules) uncovered)
    (printf "A0 rule anchors: recorded=~a required=~a\n"
            (length a0-rule-anchors) (length a0-required-rules))
    (printf "A0 dead-clause report: ~s\n" uncovered)
    (printf "A0 native metafunction cases: ~s\n" native))
  (values witnessed uncovered native))

(struct a0-generation
  (seed size attempts generated satisfying discard-ratio cases-per-minute
        constructors rules max-binder-depth disposition)
  #:transparent)

(struct a0-size-growth (depths milliseconds ratios triggered?)
  #:transparent)

(define (term-head datum)
  (and (pair? datum) (symbol? (first datum)) (first datum)))

(define (binder-depth datum [depth 0])
  (cond
    [(not (list? datum)) depth]
    [else
     (define next
       (+ depth (if (member (term-head datum) '(λ Let Bind)) 1 0)))
     (for/fold ([maximum next]) ([child (in-list datum)])
       (max maximum (binder-depth child next)))]))

(define (run-a0-generation-measurement #:attempts [attempts 200]
                                       #:size [size 6]
                                       #:seed [seed 520]
                                       #:print? [print? #t])
  (random-seed seed)
  (define started (current-inexact-monotonic-milliseconds))
  (define generated 0)
  (define satisfying 0)
  (define constructors (mutable-set))
  (define rules (mutable-set))
  (define max-depth 0)
  (for ([attempt (in-range attempts)])
    (with-handlers ([exn:fail? (lambda (_) (void))])
      (define candidate
        (generate-term SmusniA0 t size #:attempt-num attempt))
      (set! generated (add1 generated))
      (define derivations
        (build-derivations (a0-synth () ,candidate R)))
      (when (= (length derivations) 1)
        (set! satisfying (add1 satisfying))
        (define head (term-head candidate))
        (when head (set-add! constructors head))
        (for ([name (in-list (derivation-rule-names (first derivations)))])
          (set-add! rules name))
        (set! max-depth (max max-depth (binder-depth candidate))))))
  (define elapsed-minutes
    (/ (max 1.0 (- (current-inexact-monotonic-milliseconds) started))
       60000.0))
  (define usable-rate (if (zero? generated) 0 (/ satisfying generated)))
  (define per-minute (/ satisfying elapsed-minutes))
  (define disposition
    (if (and (>= usable-rate 0.01) (>= per-minute 100)
             (positive? (set-count constructors))
             (positive? max-depth))
        'generated 'fixture/enumeration-only))
  (define report
    (a0-generation seed size attempts generated satisfying
                   (- 1 usable-rate) per-minute
                   (sort (set->list constructors) symbol<?)
                   (sort (set->list rules) string<?)
                   max-depth disposition))
  (when print?
    (printf "A0 generation: seed=~a size=~a attempts=~a generated=~a satisfying=~a discard-ratio=~a cases/min=~a constructors=~a rules=~a binder-depth=~a disposition=~a\n"
            seed size attempts generated satisfying
            (~r (a0-generation-discard-ratio report) #:precision '(= 3))
            (~r per-minute #:precision '(= 1))
            (length (a0-generation-constructors report))
            (length (a0-generation-rules report)) max-depth disposition))
  report)

(define (a0-growth-term depth salt)
  (for/fold ([body '⊤]) ([index (in-range depth)])
    (define value (+ salt index))
    `(Let (,(string->symbol (format "$growth_~a_~a" salt index)) Content)
       (= ,value ,value)
       ,body)))

(define (run-a0-size-growth #:depths [depths '(12 24 48)]
                            #:factor [factor 4.0]
                            #:print? [print? #t])
  (unless (and (= (length depths) 3)
               (andmap exact-positive-integer? depths)
               (= (second depths) (* 2 (first depths)))
               (= (third depths) (* 2 (second depths))))
    (raise-argument-error
     'run-a0-size-growth
     "three positive depths, each twice its predecessor" depths))
  ;; Warm every structural size on different data. Each measured trial then
  ;; contains distinct numerals, so Redex's immutable-term cache cannot turn
  ;; the scaling probe into repeated lookup of one prior derivation.
  (for ([depth (in-list depths)] [salt '(610000 620000 630000)])
    (void (judgment-holds (a0-synth () ,(a0-growth-term depth salt) R) R)))
  (define milliseconds
    (for/list ([depth (in-list depths)] [size-index (in-naturals 1)])
      (define trials
        (for/list ([trial (in-range 3)])
          (define salt (+ 700000 (* size-index 10000) (* trial 100000)))
          (define started (current-inexact-monotonic-milliseconds))
          (define derivations
            (judgment-holds
             (a0-synth () ,(a0-growth-term depth salt) R) R))
          (unless (= (length derivations) 1)
            (error 'run-a0-size-growth
                   "growth term at depth ~a has ~a derivations"
                   depth (length derivations)))
          (- (current-inexact-monotonic-milliseconds) started)))
      (second (sort trials <))))
  (define ratios
    (for/list ([smaller (in-list milliseconds)]
               [larger (in-list (rest milliseconds))])
      (/ larger (max smaller 0.001))))
  (define triggered? (andmap (lambda (ratio) (> ratio factor)) ratios))
  (define report (a0-size-growth depths milliseconds ratios triggered?))
  (when print?
    (printf "A0 size-growth (report-only until B): ~a depths=~s milliseconds=~s ratios=~s limit=~ax\n"
            (if triggered? "TRIGGER" "ok") depths
            (map (lambda (value) (~r value #:precision '(= 3))) milliseconds)
            (map (lambda (value) (~r value #:precision '(= 3))) ratios)
            factor))
  report)

(define (run-a0-gate #:print? [print? #t])
  (define-values (_witnessed uncovered native)
    (a0-coverage-report #:print? print?))
  (define generation
    (run-a0-generation-measurement
     #:attempts 500 #:size 8 #:seed 520 #:print? print?))
  (and (null? uncovered)
       (andmap (lambda (entry) (positive? (cdr entry))) native)
       (= (a0-generation-generated generation) 500)
       (positive? (a0-generation-satisfying generation))))

(module+ main
  (define check? #f)
  (command-line
   #:program "port-a0.rkt"
   #:once-each
   [("--check") "run A0 coverage and generation measurements"
    (set! check? #t)])
  (when check?
    (exit (if (run-a0-gate) 0 1))))
