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
         b1-expand-at-least
         b1-expand-some
         b1-expand-every
         b1-expand-no
         b1-expand-at-most
         b1-expand-more-than
         b1-expand-fewer-than
         b1-expand-distrib
         b1-expand-overlap
         b1-expand-covered-by
         b1-expand-select-some
         b1-expand-max-refer
         a0-hoist
         site-plan
         introducing?
         hoist-ordered
         replace-site
         a0-type
         a0-compatible?
         negate-record
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
  [arrow Fn EFn]
  [effect context refer projective effectful-call performance]
  [comp-category Content ClauseContent Discourse (RefComp τ) (PerfComp τ)]
  [obligation finite-set-cardinality-defined
              (presuppose t comp-category)
              (when-positive t obligation)
              variable-not-otherwise-mentioned]
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
  [v x n constant
     (λ ((x τ) ...) t)
     (List v ...)]
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
     (AtLeast t t t)
     (Some t t)
     (Every t t)
     (No t t)
     (AtMost t t t)
     (GlobalExactly t t t)
     (TooMany t t)
     (MoreThan t t t)
     (FewerThan t t t)
     (Distrib t t)
     (MaxRefer t)
     (CoveredBy t t)
     (Overlap t t)
     (Among t t)
     (∀ t)
     (∃ t)
     (→ t t)
     (¬ t)
     (Presuppose t t)
     (Massify t t)
     (Perform t)
     (CanonicalAggregateAt t t t)
     (AdmissibleThreshold t t t)
     (SetOf t)
     (Card t)
     (= t t)
     (+ t t)
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
     (where x_w ,(variable-not-in (term (n τ t_P t_Q)) '$w))]))

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
     (CloseClause
      (ActualClause
       (DirectClause
        (λ ((x_event (Referents Eventuality)))
          (wrap-bindings
           (binding ...)
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
     (CloseClause
      (λ ((x_clause_event (Referents Eventuality)))
        (∧ (CoRef x_clause_event t_supplied_event)
           ((ActualClause
             (DirectClause
              (λ ((x_lexical_event (Referents Eventuality)))
                (wrap-bindings
                 (binding ...)
                 (x_predicate t_argument ... x_lexical_event)))))
            t_supplied_event))))
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
;; B1 quantifier/selection definitions

(define (provably-positive-count? datum)
  (or (and (exact-integer? datum) (positive? datum))
      (match datum
        [`(+ ,_ 1) #t]
        [`(+ 1 ,_) #t]
        [_ #f])))

(define-definition-metafunction SmusniA0
  b1-expand-at-least : t τ t t -> t
  (definition-case zero
    [(b1-expand-at-least 0 τ t_P t_Q) ⊤])
  (definition-case positive
    [(b1-expand-at-least t_n τ t_P t_Q)
     (Bind ((x_w (Referents τ) (SelectAtLeast t_n t_P)))
       (t_Q x_w))
     (side-condition (provably-positive-count? (term t_n)))
     (where x_w ,(variable-not-in (term (t_n τ t_P t_Q)) '$w))]))

(define-definition-metafunction SmusniA0
  b1-expand-some : τ t t -> t
  (definition-case witness
    [(b1-expand-some τ t_P t_Q)
     (Bind ((x_w (Referents τ) (SelectSome t_P)))
       (t_Q x_w))
     (where x_w ,(variable-not-in (term (τ t_P t_Q)) '$w))]))

(define-definition-metafunction SmusniA0
  b1-expand-every : τ t t -> t
  (definition-case maximal-distribution
    [(b1-expand-every τ t_P t_Q)
     (Bind ((x_w (Referents τ) (MaxRefer t_P)))
       (Distrib t_Q x_w))
     (where x_w ,(variable-not-in (term (τ t_P t_Q)) '$w))]))

(define-definition-metafunction SmusniA0
  b1-expand-no : τ t t -> t
  (definition-case negated-some
    [(b1-expand-no τ t_P t_Q)
     (¬ (Some t_P t_Q))]))

(define-definition-metafunction SmusniA0
  b1-expand-at-most : t τ t t -> t
  (definition-case negated-successor
    [(b1-expand-at-most t_n τ t_P t_Q)
     (¬ (AtLeast (+ t_n 1) t_P t_Q))]))

(define-definition-metafunction SmusniA0
  b1-expand-more-than : t τ t t -> t
  (definition-case successor
    [(b1-expand-more-than t_n τ t_P t_Q)
     (AtLeast (+ t_n 1) t_P t_Q)]))

(define-definition-metafunction SmusniA0
  b1-expand-fewer-than : t τ t t -> t
  (definition-case negated-at-least
    [(b1-expand-fewer-than t_n τ t_P t_Q)
     (¬ (AtLeast t_n t_P t_Q))]))

(define-definition-metafunction SmusniA0
  b1-expand-distrib : τ t t -> t
  (definition-case universal-members
    [(b1-expand-distrib τ t_Q t_r)
     (∀ (λ ((x_member τ))
          (→ (Among x_member t_r) (t_Q x_member))))
     (where x_member
            ,(variable-not-in (term (τ t_Q t_r)) '$member))]))

(define-definition-metafunction SmusniA0
  b1-expand-overlap : τ t t -> t
  (definition-case common-subreference
    [(b1-expand-overlap τ t_a t_b)
     (∃ (λ ((x_common (Referents τ)))
          (∧ (Among x_common t_a) (Among x_common t_b))))
     (where x_common
            ,(variable-not-in (term (τ t_a t_b)) '$common))]))

(define-definition-metafunction SmusniA0
  b1-expand-covered-by : τ t t -> t
  (definition-case no-residue
    [(b1-expand-covered-by τ t_P t_r)
     (∧ (Distrib t_P t_r)
        (∀ (λ ((x_subreference (Referents τ)))
             (→ (Among x_subreference t_r)
                (∃ (λ ((x_member τ))
                     (∧ (t_P x_member)
                        (Overlap x_member x_subreference))))))))
     (where x_subreference
            ,(variable-not-in (term (τ t_P t_r)) '$subreference))
     (where x_member
            ,(variable-not-in
              (term (τ t_P t_r x_subreference)) '$member))]))

(define-definition-metafunction SmusniA0
  b1-expand-select-some : τ t -> t
  (definition-case at-least-one
    [(b1-expand-select-some τ t_P)
     (SelectAtLeast 1 t_P)]))

(define-definition-metafunction SmusniA0
  b1-expand-max-refer : τ t -> t
  (definition-case inhabited-maximal-reference
    [(b1-expand-max-refer τ t_P)
     (Presuppose
      (∃ t_P)
      (Refer
       (λ ((x_reference (Referents τ)))
         (∧ (CoveredBy t_P x_reference)
            (∀ (λ ((x_member τ))
                 (→ (t_P x_member)
                    (Among x_member x_reference))))))))
     (where x_reference
            ,(variable-not-in (term (τ t_P)) '$reference))
     (where x_member
            ,(variable-not-in (term (τ t_P x_reference)) '$member))]))

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

(define (core-variable-symbol? value)
  (and (symbol? value)
       (string-prefix? (symbol->string value) "$")))

(define (free-core-variables datum [bound (set)])
  (cond
    [(symbol? datum)
     (if (and (core-variable-symbol? datum)
              (not (set-member? bound datum)))
         (set datum)
         (set))]
    [(not (list? datum)) (set)]
    [(quoted-head? datum) (set)]
    [else
     (match datum
       [`(Site ,_) (set)]
       [`(SiteValue ,_) (set)]
       [`(λ ,binders ,body)
        (define variables
          (for/list ([binder (in-list binders)]) (first binder)))
        (free-core-variables body
                             (set-union bound (list->set variables)))]
       [`(Let (,variable ,_) ,value ,body)
        (set-union
         (free-core-variables value bound)
         (free-core-variables body (set-add bound variable)))]
       [`(Bind ,bindings ,body)
        (let loop ([remaining bindings] [scope bound] [free (set)])
          (if (null? remaining)
              (set-union free (free-core-variables body scope))
              (match-let ([(list variable _ computation) (first remaining)])
                (loop (rest remaining)
                      (set-add scope variable)
                      (set-union
                       free (free-core-variables computation scope))))))]
       [_
        (for/fold ([free (set)]) ([child (in-list datum)])
          (set-union free (free-core-variables child bound)))])]))

(define (pure-position-member-variables term-datum)
  (match term-datum
    [`(λ ,binders ,_)
     (list->set (for/list ([binder (in-list binders)]) (first binder)))]
    [_ (set)]))

(define (environment-variable-type environment variable)
  (for/first ([entry (in-list environment)]
              #:when (equal? (first entry) variable))
    (second entry)))

(define (declares-outer? dependencies variable type)
  (member `(outer ,variable ,type) dependencies))

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
        (define member-variables
          (pure-position-member-variables term-datum))
        (cond
          [(not (= (length ids) (set-count id-set))) 'malformed-metadata]
          [(not (set=? id-set (list->set used-sites))) 'malformed-metadata]
          [(for/or ([item (in-list parsed)])
             (member '(member) (fourth item)))
           'member-dependent]
          [(for/or ([item (in-list parsed)])
             (not (set-empty?
                   (set-intersect
                    member-variables
                    (free-core-variables (second item))))))
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
             (for/or ([variable
                       (in-set (free-core-variables (second item)))])
               (define type
                 (environment-variable-type environment variable))
               (or (not type)
                   (not (declares-outer? (fourth item) variable type)))))
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

(define (alpha-normalize-datum datum)
  (define used (box (free-core-variables datum)))
  (define counter (box 0))
  (define (fresh-variable)
    (let loop ()
      (define candidate
        (string->symbol (format "$alpha~a" (unbox counter))))
      (set-box! counter (add1 (unbox counter)))
      (if (set-member? (unbox used) candidate)
          (loop)
          (begin
            (set-box! used (set-add (unbox used) candidate))
            candidate))))
  (define (walk value environment)
    (cond
      [(symbol? value) (hash-ref environment value value)]
      [(not (list? value)) value]
      [(quoted-head? value) value]
      [else
       (match value
         [`(λ ,binders ,body)
          (define-values (normalized-bindings extended)
            (for/fold ([normalized '()] [scope environment])
                      ([binder (in-list binders)])
              (match-define (list variable type) binder)
              (define replacement (fresh-variable))
              (values (append normalized (list (list replacement type)))
                      (hash-set scope variable replacement))))
          `(λ ,normalized-bindings ,(walk body extended))]
         [`(Let (,variable ,type) ,active ,body)
          (define replacement (fresh-variable))
          `(Let (,replacement ,type)
             ,(walk active environment)
             ,(walk body (hash-set environment variable replacement)))]
         [`(Bind ,bindings ,body)
          (define-values (normalized-bindings extended)
            (for/fold ([normalized '()] [scope environment])
                      ([binding (in-list bindings)])
              (match-define (list variable type computation) binding)
              (define replacement (fresh-variable))
              (values
               (append normalized
                       (list (list replacement type
                                   (walk computation scope))))
               (hash-set scope variable replacement))))
          `(Bind ,normalized-bindings ,(walk body extended))]
         [_ (map (lambda (child) (walk child environment)) value)])]))
  (walk datum (hash)))

(define (normalize-obligation obligation)
  (match obligation
    [`(presuppose ,condition ,category)
     `(presuppose ,(alpha-normalize-datum condition) ,category)]
    [`(when-positive ,count ,nested)
     `(when-positive ,(alpha-normalize-datum count)
        ,(normalize-obligation nested))]
    [_ obligation]))

(define (canonical-obligation-set values)
  (sort (remove-duplicates (map normalize-obligation values))
        string<? #:key (lambda (value) (format "~s" value))))

;; An obligation emitted inside a core binder may mention that binder.  At the
;; emission site the variable is free relative to the condition alone, so the
;; ordinary condition-local normalizer must not rename it.  When the typing
;; derivation exits the binder, normalize the complete obligation set as one
;; datum under a synthetic binder.  Keeping the set together preserves one
;; identity across every occurrence of the binder, including term-valued fields
;; in different obligations.
(define (scope-obligation-set binders obligations)
  (if (null? obligations)
      '()
      (match (alpha-normalize-datum
              `(λ ,binders (ObligationSetMarker ,@obligations)))
        [`(λ ,_ (ObligationSetMarker ,normalized ...))
         (canonical-obligation-set normalized)]
        [other
         (error 'scope-obligation-set
                "cannot unwrap normalized obligation scope ~e" other)])))

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

(define (a0-equality-type? type)
  (or (member type
              '(Entity Eventuality Number Natural Cardinal ThresholdKind))
      (match type
        [`(Set ,_) #t]
        [`(Group ,_) #t]
        [`(List ,_) #t]
        [_ #f])))

(define (a0-first-order-type? type)
  (or (member type '(Entity Eventuality Number Natural Cardinal))
      (match type
        [`(Set ,_) #t]
        [`(Group ,_) #t]
        [`(List ,_) #t]
        [_ #f])))

(define (a0-quantifier-domain-type? type)
  (or (a0-first-order-type? type)
      (match type
        [`(Referents ,inner) (a0-first-order-type? inner)]
        [_ #f])))

(define (a0-reference-inner type)
  (match type
    [`(Referents ,inner) inner]
    [_ (and (a0-first-order-type? type) type)]))

(define (a0-reference-compatible? left right)
  (define left-inner (a0-reference-inner left))
  (define right-inner (a0-reference-inner right))
  (and left-inner right-inner
       (or (a0-compatible? left-inner right-inner)
           (a0-compatible? right-inner left-inner))))

(define (a0-comp-category? type)
  (or (member type '(Content ClauseContent Discourse))
      (match type
        [`(RefComp ,_) #t]
        [`(PerfComp ,_) #t]
        [_ #f])))

(define (a0-number-join left right)
  (define ranks (hash 'Cardinal 0 'Natural 1 'Number 2))
  (and (hash-has-key? ranks left)
       (hash-has-key? ranks right)
       (if (>= (hash-ref ranks left) (hash-ref ranks right)) left right)))

(define (a0-reference-computation-form? datum)
  (and (list? datum)
       (pair? datum)
       (match datum
         [`(Presuppose ,_ ,body)
          (a0-reference-computation-form? body)]
         [`(,head . ,_)
          (and (member head
                       '(Context Vague Refer SelectExactly SelectAtLeast
                                 SelectSome SelectAllBut Massify MaxRefer))
               #t)]
         [_ #f])))

(define (a0-value-datum? datum)
  (redex-match? SmusniA0 v datum))

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
    ,(canonical-obligation-set
      (append extra-obligations (append-map record-obligations records)))))

(define (scope-record-datum binders record)
  `(typing ,(record-type record)
           ,(record-effects record)
           ,(scope-obligation-set binders (record-obligations record))))

(define (merge-positive-conditional-record-datums
         output count count-record conditional-records extra-effects)
  `(typing
    ,output
    ,(canonical-symbol-set
      (append extra-effects
              (append-map record-effects
                          (cons count-record conditional-records))))
    ,(canonical-obligation-set
      (append
       (record-obligations count-record)
       (for*/list ([record (in-list conditional-records)]
                   [obligation (in-list (record-obligations record))])
         `(when-positive ,count ,obligation))))))

(define (negate-record-datum record)
  `(typing Content
           ,(canonical-symbol-set
             (remove 'refer (record-effects record)))
           ,(canonical-obligation-set (record-obligations record))))

(define (presuppose-record-datum condition condition-record body-record)
  (define body-type (record-type body-record))
  `(typing
    ,body-type
    ,(canonical-symbol-set
      (append '(projective)
              (remove 'refer (record-effects condition-record))
              (record-effects body-record)))
    ,(canonical-obligation-set
      (append (record-obligations condition-record)
              (record-obligations body-record)
              (list `(presuppose ,condition ,body-type))))))

(define (gq-extra-effects nuclear-type exports?)
  (canonical-symbol-set
   (append
    (if (match nuclear-type [`(EFn ,_ Content) #t] [_ #f])
        '(effectful-call) '())
    (if exports? '(refer) '()))))

(define (extend-environment-datum environment bindings)
  (foldr cons environment bindings))

(define (lookup-environment-datum environment variable)
  (match (assoc variable environment)
    [(list _ type) type]
    [_ 'not-found]))

(define-metafunction SmusniA0
  extend-env : Γ ((x τ) ...) -> Γ
  [(extend-env Γ ((x τ) ...))
   ,(extend-environment-datum (term Γ) (term ((x τ) ...)))])

(define-metafunction SmusniA0
  env-lookup : Γ x -> lookup-result
  [(env-lookup Γ x)
   ,(lookup-environment-datum (term Γ) (term x))])

(define-metafunction SmusniA0
  record-type-of : R -> τ
  [(record-type-of (typing τ (effect ...) (obligation ...))) τ])

(define-metafunction SmusniA0
  merge-records : τ (R ...) (effect ...) (obligation ...) -> R
  [(merge-records τ (R ...) (effect ...) (obligation ...))
   ,(merge-record-datums (term τ) (term (R ...))
                         (term (effect ...)) (term (obligation ...)))])

(define-metafunction SmusniA0
  scope-record : ((x τ) ...) R -> R
  [(scope-record ((x τ) ...) R)
   ,(scope-record-datum (term ((x τ) ...)) (term R))])

(define-metafunction SmusniA0
  merge-positive-conditional-records : τ t R (R ...) (effect ...) -> R
  [(merge-positive-conditional-records
    τ t_count R_count (R_conditional ...) (effect ...))
   ,(merge-positive-conditional-record-datums
     (term τ) (term t_count) (term R_count) (term (R_conditional ...))
     (term (effect ...)))])

(define-metafunction SmusniA0
  negate-record : R -> R
  [(negate-record R) ,(negate-record-datum (term R))])

(define-metafunction SmusniA0
  presuppose-record : t R R -> R
  [(presuppose-record t_condition R_condition R_body)
   ,(presuppose-record-datum
     (term t_condition) (term R_condition) (term R_body))])

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

  [(where Γ_body (extend-env Γ ((x τ))))
   (a0-type synth Γ_body t_body
            (typing τ_body () (obligation ...)))
   (where (typing τ_body () (obligation_scoped ...))
          (scope-record ((x τ))
                        (typing τ_body () (obligation ...))))
   ----------------------------------------------- "A0-T-Lambda-Pure"
   (a0-type synth Γ
            (λ ((x τ)) t_body)
            (typing (Fn (τ) τ_body) () (obligation_scoped ...)))]

  [(where Γ_body (extend-env Γ ((x τ))))
   (a0-type synth Γ_body t_body
            (typing τ_body (effect_0 effect_rest ...) (obligation ...)))
   (where (typing τ_body (effect_0 effect_rest ...) (obligation_scoped ...))
          (scope-record
           ((x τ))
           (typing τ_body (effect_0 effect_rest ...) (obligation ...))))
   ----------------------------------------------- "A0-T-Lambda-Effectful"
   (a0-type synth Γ
            (λ ((x τ)) t_body)
            (typing (EFn (τ) τ_body) () (obligation_scoped ...)))]

  [(where Γ_body
          (extend-env Γ
                      ((x_0 τ_0) (x_1 τ_1) (x_rest τ_rest) ...)))
   (a0-type synth Γ_body t_body
            (typing τ_body () (obligation ...)))
   (where (typing τ_body () (obligation_scoped ...))
          (scope-record
           ((x_0 τ_0) (x_1 τ_1) (x_rest τ_rest) ...)
           (typing τ_body () (obligation ...))))
   ----------------------------------------------- "A0-T-Lambda-Multi-Pure"
   (a0-type synth Γ
            (λ ((x_0 τ_0) (x_1 τ_1) (x_rest τ_rest) ...) t_body)
            (typing (Fn (τ_0 τ_1 τ_rest ...) τ_body)
                    () (obligation_scoped ...)))]

  [(where Γ_body
          (extend-env Γ
                      ((x_0 τ_0) (x_1 τ_1) (x_rest τ_rest) ...)))
   (a0-type synth Γ_body t_body
            (typing τ_body (effect_0 effect_rest ...) (obligation ...)))
   (where (typing τ_body (effect_0 effect_rest ...)
                         (obligation_scoped ...))
          (scope-record
           ((x_0 τ_0) (x_1 τ_1) (x_rest τ_rest) ...)
           (typing τ_body (effect_0 effect_rest ...) (obligation ...))))
   ----------------------------------------------- "A0-T-Lambda-Multi-Effectful"
   (a0-type synth Γ
            (λ ((x_0 τ_0) (x_1 τ_1) (x_rest τ_rest) ...) t_body)
            (typing (EFn (τ_0 τ_1 τ_rest ...) τ_body)
                    () (obligation_scoped ...)))]

  [(side-condition ,(a0-value-datum? (term t_value)))
   (a0-type synth Γ t_value
            (typing τ_value () (obligation_value ...)))
   (side-condition
    ,(a0-compatible? (term τ_value) (term τ)))
   (where Γ_body (extend-env Γ ((x τ))))
   (a0-type synth Γ_body t_body R_body)
   (where τ_body (record-type-of R_body))
   (where R_body_scoped (scope-record ((x τ)) R_body))
   (where R_out
          (merge-records
           τ_body
           ((typing τ_value () (obligation_value ...)) R_body_scoped) () ()))
   ----------------------------------------------- "A0-T-Let"
   (a0-type synth Γ (Let (x τ) t_value t_body) R_out)]

  [(where t_nested
          (nest-bind (binding_0 binding_1 binding_rest ...) t_body))
   (a0-type synth Γ t_nested R_out)
   ----------------------------------------------- "A0-T-Bind-Nest"
   (a0-type synth Γ
            (Bind (binding_0 binding_1 binding_rest ...) t_body)
            R_out)]

  [(a0-type (check (RefComp τ)) Γ t_comp R_comp)
   (where Γ_body (extend-env Γ ((x τ))))
   (a0-type synth Γ_body t_body R_body)
   (where τ_body (record-type-of R_body))
   (where R_body_scoped (scope-record ((x τ)) R_body))
   (where R_out (merge-records τ_body (R_comp R_body_scoped) () ()))
   ----------------------------------------------- "A0-T-Bind-Reference"
   (a0-type synth Γ
            (Bind ((x τ t_comp)) t_body) R_out)]

  [(a0-type (check (PerfComp τ)) Γ t_comp R_comp)
   (where Γ_body (extend-env Γ ((x τ))))
   (a0-type synth Γ_body t_body
            (typing (Act force) (effect_body ...) (obligation_body ...)))
   (where R_body_scoped
          (scope-record
           ((x τ))
           (typing (Act force) (effect_body ...) (obligation_body ...))))
   (where R_out
          (merge-records Discourse
                         (R_comp R_body_scoped)
                         (performance) ()))
   ----------------------------------------------- "A0-T-Bind-Performance-Act"
   (a0-type synth Γ
            (Bind ((x τ t_comp)) t_body) R_out)]

  [(a0-type (check (PerfComp τ)) Γ t_comp R_comp)
   (where Γ_body (extend-env Γ ((x τ))))
   (a0-type synth Γ_body t_body
            (typing (PerfComp τ_body) (effect_body ...) (obligation_body ...)))
   (where R_body_scoped
          (scope-record
           ((x τ))
           (typing (PerfComp τ_body)
                   (effect_body ...) (obligation_body ...))))
   (where R_out
          (merge-records (PerfComp τ_body)
                         (R_comp R_body_scoped)
                         () ()))
   ----------------------------------------------- "A0-T-Bind-Performance-Comp"
   (a0-type synth Γ
            (Bind ((x τ t_comp)) t_body) R_out)]

  [(a0-type (check (PerfComp τ)) Γ t_comp R_comp)
   (where Γ_body (extend-env Γ ((x τ))))
   (a0-type synth Γ_body t_body
            (typing Discourse (effect_body ...) (obligation_body ...)))
   (where R_body_scoped
          (scope-record
           ((x τ))
           (typing Discourse (effect_body ...) (obligation_body ...))))
   (where R_out
          (merge-records Discourse
                         (R_comp R_body_scoped)
                         () ()))
   ----------------------------------------------- "A0-T-Bind-Performance-Discourse"
   (a0-type synth Γ
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
            (typing (arrow ((Referents τ)) Content) () (obligation ...)))
   (where (effect_extra ...)
          ,(if (equal? (term arrow) 'EFn) '(effectful-call) '()))
   (where R_out
          (merge-records
           (RefComp (Referents τ))
           ((typing (arrow ((Referents τ)) Content) () (obligation ...)))
           (effect_extra ... refer) ()))
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
   (side-condition ,(provably-positive-count? (term t_count)))
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

  [(a0-type (check Natural) Γ t_count R_count)
   (side-condition ,(provably-positive-count? (term t_count)))
   (a0-type synth Γ t_property
            (typing (Fn (τ) Content) () (obligation ...)))
   (where R_out
          (merge-records
           (RefComp (Referents τ))
           (R_count (typing (Fn (τ) Content) () (obligation ...)))
           (refer) ()))
   ----------------------------------------------- "B1-T-SelectAtLeast"
   (a0-type (check (RefComp (Referents τ))) Γ
            (SelectAtLeast t_count t_property) R_out)]

  [(a0-type (check Natural) Γ t_count R_count)
   (a0-type synth Γ t_property
            (typing (Fn (τ) Content) () (obligation ...)))
   (where R_out
          (merge-records
           (RefComp (Referents τ))
           (R_count (typing (Fn (τ) Content) () (obligation ...)))
           (refer) ()))
   ----------------------------------------------- "B1-T-SelectAllBut"
   (a0-type (check (RefComp (Referents τ))) Γ
            (SelectAllBut t_count t_property) R_out)]

  [(a0-type synth Γ v_P
            (typing (Fn (τ) Content) () (obligation ...)))
   (where R_out
          (merge-records
           (RefComp (Referents τ))
           ((typing (Fn (τ) Content) () (obligation ...)))
           (projective refer)
           ((presuppose (∃ v_P) (RefComp (Referents τ))))))
   ----------------------------------------------- "B1-T-MaxRefer"
   (a0-type (check (RefComp (Referents τ))) Γ (MaxRefer v_P) R_out)]

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

  [(a0-type synth Γ v_P R_P)
   (where (Fn (τ) Content) (record-type-of R_P))
   (a0-type (check (EFn ((Referents τ)) Content)) Γ v_Q R_Q)
   (where R_n (typing Natural () ()))
   (where (effect_extra ...)
          ,(gq-extra-effects (term (record-type-of R_Q)) #f))
   (where R_out
          (merge-records Content (R_n R_P R_Q) (effect_extra ...) ()))
   ----------------------------------------------- "A0-T-Exactly-Zero"
   (a0-type synth Γ (Exactly 0 v_P v_Q) R_out)]

  [(a0-type (check Natural) Γ t_count R_n)
   (side-condition ,(provably-positive-count? (term t_count)))
   (a0-type synth Γ v_P R_P)
   (where (Fn (τ) Content) (record-type-of R_P))
   (a0-type (check (EFn ((Referents τ)) Content)) Γ v_Q R_Q)
   (where (effect_extra ...)
          ,(gq-extra-effects (term (record-type-of R_Q)) #t))
   (where R_out
          (merge-records Content (R_n R_P R_Q) (effect_extra ...) ()))
   ----------------------------------------------- "A0-T-Exactly-Positive"
   (a0-type synth Γ (Exactly t_count v_P v_Q) R_out)]

  [(a0-type synth Γ v_P (typing (Fn (τ) Content) () (obligation_P ...)))
   (a0-type (check (EFn ((Referents τ)) Content)) Γ v_Q R_Q)
   ----------------------------------------------- "B1-T-AtLeast-Zero"
   (a0-type synth Γ (AtLeast 0 v_P v_Q) (typing Content () ()))]

  [(a0-type (check Natural) Γ t_count R_n)
   (side-condition ,(provably-positive-count? (term t_count)))
   (a0-type synth Γ v_P R_P)
   (where (Fn (τ) Content) (record-type-of R_P))
   (a0-type (check (EFn ((Referents τ)) Content)) Γ v_Q R_Q)
   (where (effect_extra ...)
          ,(gq-extra-effects (term (record-type-of R_Q)) #t))
   (where R_out
          (merge-records Content (R_n R_P R_Q) (effect_extra ...) ()))
   ----------------------------------------------- "B1-T-AtLeast-Positive"
   (a0-type synth Γ (AtLeast t_count v_P v_Q) R_out)]

  [(a0-type (check Natural) Γ t_count R_n)
   (side-condition
    ,(and (not (equal? (term t_count) 0))
          (not (provably-positive-count? (term t_count)))))
   (a0-type synth Γ v_P R_P)
   (where (Fn (τ) Content) (record-type-of R_P))
   (a0-type (check (EFn ((Referents τ)) Content)) Γ v_Q R_Q)
   (where (effect_extra ...)
          ,(gq-extra-effects (term (record-type-of R_Q)) #t))
   (where R_out
          (merge-positive-conditional-records
           Content t_count R_n (R_P R_Q) (effect_extra ...)))
   ----------------------------------------------- "B1-T-AtLeast-Symbolic"
   (a0-type synth Γ (AtLeast t_count v_P v_Q) R_out)]

  [(a0-type synth Γ v_P R_P)
   (where (Fn (τ) Content) (record-type-of R_P))
   (a0-type (check (EFn ((Referents τ)) Content)) Γ v_Q R_Q)
   (where (effect_extra ...)
          ,(gq-extra-effects (term (record-type-of R_Q)) #t))
   (where R_out (merge-records Content (R_P R_Q) (effect_extra ...) ()))
   ----------------------------------------------- "B1-T-Some"
   (a0-type synth Γ (Some v_P v_Q) R_out)]

  [(a0-type synth Γ v_P R_P)
   (where (Fn (τ) Content) (record-type-of R_P))
   (a0-type synth Γ v_Q R_Q)
   (where (arrow (τ) Content) (record-type-of R_Q))
   (where (effect_extra ...)
          ,(canonical-symbol-set
            (append '(projective refer)
                    (if (equal? (term arrow) 'EFn)
                        '(effectful-call) '()))))
   (where R_out
          (merge-records
           Content (R_P R_Q) (effect_extra ...)
           ((presuppose (∃ v_P) (RefComp (Referents τ))))))
   ----------------------------------------------- "B1-T-Every"
   (a0-type synth Γ (Every v_P v_Q) R_out)]

  [(a0-type synth Γ v_P R_P)
   (where (Fn (τ) Content) (record-type-of R_P))
   (a0-type (check (EFn ((Referents τ)) Content)) Γ v_Q R_Q)
   (where (effect_extra ...)
          ,(gq-extra-effects (term (record-type-of R_Q)) #f))
   (where R_out (merge-records Content (R_P R_Q) (effect_extra ...) ()))
   ----------------------------------------------- "A0-T-No"
   (a0-type synth Γ (No v_P v_Q) R_out)]

  [(a0-type (check Natural) Γ t_n R_n)
   (a0-type synth Γ v_P R_P)
   (where (Fn (τ) Content) (record-type-of R_P))
   (a0-type (check (EFn ((Referents τ)) Content)) Γ v_Q R_Q)
   (where (effect_extra ...)
          ,(gq-extra-effects (term (record-type-of R_Q)) #f))
   (where R_out
          (merge-records Content (R_n R_P R_Q) (effect_extra ...) ()))
   ----------------------------------------------- "B1-T-AtMost"
   (a0-type synth Γ (AtMost t_n v_P v_Q) R_out)]

  [(a0-type (check Natural) Γ t_n R_n)
   (a0-type synth Γ v_P R_P)
   (where (Fn (τ) Content) (record-type-of R_P))
   (a0-type (check (EFn ((Referents τ)) Content)) Γ v_Q R_Q)
   (where (effect_extra ...)
          ,(gq-extra-effects (term (record-type-of R_Q)) #t))
   (where R_out
          (merge-records Content (R_n R_P R_Q) (effect_extra ...) ()))
   ----------------------------------------------- "A0-T-MoreThan"
   (a0-type synth Γ (MoreThan t_n v_P v_Q) R_out)]

  [(a0-type synth Γ v_P (typing (Fn (τ) Content) () (obligation_P ...)))
   (a0-type (check (EFn ((Referents τ)) Content)) Γ v_Q R_Q)
   ----------------------------------------------- "B1-T-FewerThan-Zero"
   (a0-type synth Γ (FewerThan 0 v_P v_Q) (typing Content () ()))]

  [(a0-type (check Natural) Γ t_count R_n)
   (side-condition ,(provably-positive-count? (term t_count)))
   (a0-type synth Γ v_P R_P)
   (where (Fn (τ) Content) (record-type-of R_P))
   (a0-type (check (EFn ((Referents τ)) Content)) Γ v_Q R_Q)
   (where (effect_extra ...)
          ,(gq-extra-effects (term (record-type-of R_Q)) #f))
   (where R_out
          (merge-records Content (R_n R_P R_Q) (effect_extra ...) ()))
   ----------------------------------------------- "B1-T-FewerThan-Positive"
   (a0-type synth Γ (FewerThan t_count v_P v_Q) R_out)]

  [(a0-type (check Natural) Γ t_count R_n)
   (side-condition
    ,(and (not (equal? (term t_count) 0))
          (not (provably-positive-count? (term t_count)))))
   (a0-type synth Γ v_P R_P)
   (where (Fn (τ) Content) (record-type-of R_P))
   (a0-type (check (EFn ((Referents τ)) Content)) Γ v_Q R_Q)
   (where (effect_extra ...)
          ,(gq-extra-effects (term (record-type-of R_Q)) #f))
   (where R_out
          (merge-positive-conditional-records
           Content t_count R_n (R_P R_Q) (effect_extra ...)))
   ----------------------------------------------- "B1-T-FewerThan-Symbolic"
   (a0-type synth Γ (FewerThan t_count v_P v_Q) R_out)]

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
    ,(and (a0-equality-type? (term τ_left))
          (a0-equality-type? (term τ_right))
          (or (a0-compatible? (term τ_left) (term τ_right))
              (a0-compatible? (term τ_right) (term τ_left)))))
   (where R_out
          (merge-records Content (R_left R_right) () ()))
   ----------------------------------------------- "A0-T-Equality"
   (a0-type synth Γ (= t_left t_right) R_out)]

  [(a0-type synth Γ t_left R_left)
   (a0-type synth Γ t_right R_right)
   (where τ_left (record-type-of R_left))
   (where τ_right (record-type-of R_right))
   (where τ_result
          ,(a0-number-join (term τ_left) (term τ_right)))
   (where R_out (merge-records τ_result (R_left R_right) () ()))
   ----------------------------------------------- "B1-T-Addition"
   (a0-type synth Γ (+ t_left t_right) R_out)]

  [(a0-type (check Content) Γ t_left R_left)
   (a0-type (check Content) Γ t_right R_right)
   (where R_out (merge-records Content (R_left R_right) () ()))
   ----------------------------------------------- "A0-T-And"
   (a0-type synth Γ (∧ t_left t_right) R_out)]

  [(a0-type (check Content) Γ t_left R_left)
   (a0-type (check Content) Γ t_right R_right)
   (where R_out (merge-records Content (R_left R_right) () ()))
   ----------------------------------------------- "B1-T-Implication"
   (a0-type synth Γ (→ t_left t_right) R_out)]

  [(a0-type (check Content) Γ t_body R_body)
   (where R_out (negate-record R_body))
   ----------------------------------------------- "B1-T-Negation"
   (a0-type synth Γ (¬ t_body) R_out)]

  [(a0-type synth Γ v_property
            (typing (arrow (τ_domain τ_rest ...) Content)
                    (effect_property ...) (obligation ...)))
   (side-condition
    ,(andmap a0-quantifier-domain-type?
             (term (τ_domain τ_rest ...))))
   (where (effect_extra ...)
          ,(if (equal? (term arrow) 'EFn) '(effectful-call) '()))
   (where R_out
          (merge-records
           Content
           ((typing (arrow (τ_domain τ_rest ...) Content)
                    (effect_property ...) (obligation ...)))
           (effect_extra ...) ()))
   ----------------------------------------------- "B1-T-Forall"
   (a0-type synth Γ (∀ v_property) R_out)]

  [(a0-type synth Γ v_property
            (typing (arrow (τ_domain τ_rest ...) Content)
                    (effect_property ...) (obligation ...)))
   (side-condition
    ,(andmap a0-quantifier-domain-type?
             (term (τ_domain τ_rest ...))))
   (where (effect_extra ...)
          ,(if (equal? (term arrow) 'EFn) '(effectful-call) '()))
   (where R_out
          (merge-records
           Content
           ((typing (arrow (τ_domain τ_rest ...) Content)
                    (effect_property ...) (obligation ...)))
           (effect_extra ...) ()))
   ----------------------------------------------- "B1-T-Exists"
   (a0-type synth Γ (∃ v_property) R_out)]

  [(a0-type synth Γ t_left R_left)
   (a0-type synth Γ t_right R_right)
   (where τ_left (record-type-of R_left))
   (where τ_right (record-type-of R_right))
   (side-condition
    ,(a0-reference-compatible? (term τ_left) (term τ_right)))
   (where R_out (merge-records Content (R_left R_right) () ()))
   ----------------------------------------------- "B1-T-Among"
   (a0-type synth Γ (Among t_left t_right) R_out)]

  [(a0-type (check Content) Γ t_condition R_condition)
   (a0-type synth Γ t_body R_body)
   (where τ_body (record-type-of R_body))
   (side-condition ,(a0-comp-category? (term τ_body)))
   (where R_out
          (presuppose-record t_condition R_condition R_body))
   ----------------------------------------------- "B1-T-Presuppose-Synth"
   (a0-type synth Γ (Presuppose t_condition t_body) R_out)]

  [(side-condition
    ,(a0-reference-computation-form? (term t_body)))
   (a0-type (check Content) Γ t_condition R_condition)
   (a0-type (check (RefComp τ)) Γ t_body R_body)
   (where R_out
          (presuppose-record t_condition R_condition R_body))
   ----------------------------------------------- "B1-T-Presuppose-Reference"
   (a0-type (check (RefComp τ)) Γ
            (Presuppose t_condition t_body) R_out)]

  [(a0-type (check (Referents Eventuality)) Γ t_left R_left)
   (a0-type (check (Referents Eventuality)) Γ t_right R_right)
   (where R_out (merge-records Content (R_left R_right) () ()))
   ----------------------------------------------- "A0-T-CoRef"
   (a0-type synth Γ (CoRef t_left t_right) R_out)]

  [(a0-type synth Γ v_Q
            (typing (arrow (τ) Content)
                    (effect_Q ...) (obligation_Q ...)))
   (a0-type (check (Referents τ)) Γ t_reference R_reference)
   (where (effect_extra ...)
          ,(if (equal? (term arrow) 'EFn) '(effectful-call) '()))
   (where R_out
          (merge-records
           Content
           ((typing (arrow (τ) Content)
                    (effect_Q ...) (obligation_Q ...))
            R_reference)
           (effect_extra ...) ()))
   ----------------------------------------------- "B1-T-Distrib"
   (a0-type synth Γ (Distrib v_Q t_reference) R_out)]

  [(a0-type synth Γ v_P
            (typing (Fn (τ) Content) () (obligation_P ...)))
   (a0-type (check (Referents τ)) Γ t_reference R_reference)
   (where R_out
          (merge-records
           Content
           ((typing (Fn (τ) Content) () (obligation_P ...))
            R_reference)
           () ()))
   ----------------------------------------------- "B1-T-CoveredBy"
   (a0-type synth Γ (CoveredBy v_P t_reference) R_out)]

  [(a0-type synth Γ t_left R_left)
   (a0-type synth Γ t_right R_right)
   (where τ_left (record-type-of R_left))
   (where τ_right (record-type-of R_right))
   (side-condition
    ,(a0-reference-compatible? (term τ_left) (term τ_right)))
   (where R_out (merge-records Content (R_left R_right) () ()))
   ----------------------------------------------- "B1-T-Overlap"
   (a0-type synth Γ (Overlap t_left t_right) R_out)]

  [(a0-type (check τ) Γ t_item R_item) ...
   (where R_out (merge-records (List τ) (R_item ...) () ()))
   ----------------------------------------------- "A0-T-List-Check"
   (a0-type (check (List τ)) Γ (List t_item ...) R_out)]

  [(a0-type synth Γ v_f
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
   (a0-type synth Γ (ZipWith v_f t_left t_right) R_out)]

  [(a0-type synth Γ v_f
            (typing (EFn (τ_left τ_right) Content)
                    (effect_f ...) (obligation_f ...)))
   (where R_out
          (merge-records Content
                         ((typing (EFn (τ_left τ_right) Content)
                                  (effect_f ...) (obligation_f ...)))
                         () ()))
   ----------------------------------------------- "A0-T-ZipWith-Empty-Effectful"
   (a0-type synth Γ (ZipWith v_f (List) (List)) R_out)]

  [(a0-type synth Γ v_f
            (typing (EFn (τ_left τ_right) Content)
                    (effect_f ...) (obligation_f ...)))
   (a0-type (check (List τ_left)) Γ t_left R_left)
   (a0-type (check (List τ_right)) Γ t_right R_right)
   (side-condition
    ,(not (and (equal? (term t_left) '(List))
               (equal? (term t_right) '(List)))))
   (where R_out
          (merge-records Content
                         ((typing (EFn (τ_left τ_right) Content)
                                  (effect_f ...) (obligation_f ...))
                          R_left R_right)
                         (effectful-call) ()))
   ----------------------------------------------- "A0-T-ZipWith-Effectful"
   (a0-type synth Γ (ZipWith v_f t_left t_right) R_out)]

  [(a0-type (check Content) Γ t_content R_content)
   (where R_out (merge-records ClauseContent (R_content) () ()))
   ----------------------------------------------- "A0-T-StateClause"
   (a0-type synth Γ (StateClause t_content) R_out)]

  [(a0-type synth Γ t_property
            (typing (Fn ((Referents Eventuality)) Content)
                    (effect_property ...) (obligation ...)))
   (where R_out
          (merge-records
           (Fn ((Referents Eventuality)) Content)
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
           (EFn ((Referents Eventuality)) Content)
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
   (where R_out
          (merge-records (Fn ((Referents Eventuality)) Content)
                         (R_property) () ()))
   ----------------------------------------------- "A0-T-ActualClause-Event-Pure"
   (a0-type synth Γ (ActualClause t_property) R_out)]

  [(a0-type synth Γ t_property R_property)
   (where (EFn ((Referents Eventuality)) Content)
          (record-type-of R_property))
   (where R_out
          (merge-records (EFn ((Referents Eventuality)) Content)
                         (R_property) () ()))
   ----------------------------------------------- "A0-T-ActualClause-Event-Effectful"
   (a0-type synth Γ (ActualClause t_property) R_out)]

  [(a0-type (check ClauseContent) Γ t_clause R_clause)
   (where (effect_extra ...)
          ,(match (record-type (term R_clause))
             [`(EFn ,_ Content) '(effectful-call)]
             [_ '()]))
   (where R_out (merge-records Content (R_clause) (effect_extra ...) ()))
   ----------------------------------------------- "A0-T-CloseClause"
   (a0-type synth Γ (CloseClause t_clause) R_out)]

  [(side-condition
    ,(not (equal?
           'invalid
           (close-input-kind (term n) (term (label ...)) (term fills)
                             (term event-mode)))))
   (where t_expanded
          (a0-expand-close
           (row x_predicate n event-mode (label ...)) fills))
   (a0-type synth Γ t_expanded R_out)
   ----------------------------------------------- "A0-T-CloseWith"
   (a0-type synth Γ
            (CloseWith
             (row x_predicate n event-mode (label ...)) fills)
            R_out)]

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
    "A0-T-ZipWith-Pure" "A0-T-ZipWith-Empty-Effectful"
    "A0-T-ZipWith-Effectful"
    "A0-T-StateClause" "A0-T-DirectClause-Pure"
    "A0-T-DirectClause-Effectful" "A0-T-ActualClause-State"
    "A0-T-ActualClause-Event-Pure" "A0-T-ActualClause-Event-Effectful"
    "A0-T-CloseClause" "A0-T-CloseWith"
    "A0-T-Apply-ClauseContent"
    "A0-T-Apply-Pure" "A0-T-Apply-Effectful"
    "B1-T-SelectAtLeast" "B1-T-SelectAllBut" "B1-T-MaxRefer"
    "B1-T-Implication" "B1-T-Negation" "B1-T-Forall" "B1-T-Exists"
    "B1-T-Among" "B1-T-Presuppose-Synth"
    "B1-T-Presuppose-Reference" "B1-T-Distrib" "B1-T-CoveredBy"
    "B1-T-Overlap" "B1-T-Addition"
    "B1-T-AtLeast-Zero" "B1-T-AtLeast-Positive"
    "B1-T-AtLeast-Symbolic" "B1-T-Some"
    "B1-T-Every" "B1-T-AtMost" "B1-T-FewerThan-Zero"
    "B1-T-FewerThan-Positive" "B1-T-FewerThan-Symbolic"))

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
    ("A0-T-Context" "spec §5.3")
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
    ("A0-T-Equality" "spec §4.5")
    ("A0-T-And" "spec §4.5")
    ("A0-T-CoRef" "spec §4.5")
    ("A0-T-List-Check" "spec §4.9")
    ("A0-T-ZipWith-Pure" "spec §4.9; §12 ZipWith")
    ("A0-T-ZipWith-Empty-Effectful" "spec §4.9; §12 ZipWith empty")
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
    ("A0-T-Apply-Effectful" "spec §3.3, §4.4")
    ("B1-T-SelectAtLeast" "spec §5.6; §12 selection floor")
    ("B1-T-SelectAllBut" "spec §5.6; §12 SelectAllBut")
    ("B1-T-MaxRefer" "spec §5.3; §12 MaxRefer")
    ("B1-T-Implication" "spec §4.5")
    ("B1-T-Negation" "spec §4.5, §5.4")
    ("B1-T-Forall" "spec §4.5")
    ("B1-T-Exists" "spec §4.5")
    ("B1-T-Among" "spec §4.8")
    ("B1-T-Presuppose-Synth" "spec §5.5")
    ("B1-T-Presuppose-Reference" "spec §5.5")
    ("B1-T-Distrib" "spec §4.8; §12 Distrib")
    ("B1-T-CoveredBy" "spec §4.8")
    ("B1-T-Overlap" "spec §4.8; §12 Overlap")
    ("B1-T-Addition" "spec §4.9")
    ("B1-T-AtLeast-Zero" "spec §4.10; §12 AtLeast zero")
    ("B1-T-AtLeast-Positive" "spec §4.10; §12 AtLeast")
    ("B1-T-AtLeast-Symbolic" "spec §4.10; §12 AtLeast totality")
    ("B1-T-Some" "spec §4.10; §12 Some")
    ("B1-T-Every" "spec §4.10; §12 Every")
    ("B1-T-AtMost" "spec §4.10; §12 AtMost")
    ("B1-T-FewerThan-Zero" "spec §4.10; §12 FewerThan zero")
    ("B1-T-FewerThan-Positive" "spec §4.10; §12 FewerThan")
    ("B1-T-FewerThan-Symbolic" "spec §4.10; §12 FewerThan totality")))

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
           (ZipWith f (List) (List)))
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
    (synth ((f (EFn (Natural) Content))) (f 1))
    (check () (SelectAtLeast 1 (λ (($x Entity)) ⊤))
           (RefComp (Referents Entity)))
    (check () (SelectAllBut 0 (λ (($x Entity)) ⊤))
           (RefComp (Referents Entity)))
    (check ((P (Fn (Entity) Content))) (MaxRefer P)
           (RefComp (Referents Entity)))
    (synth () (→ ⊤ ⊤))
    (synth ((P (Fn (Entity) Content))
            (Q (EFn ((Referents Entity)) Content)))
           (¬ (Some P Q)))
    (synth () (∀ (λ (($x Entity)) ⊤)))
    (synth () (∃ (λ (($x Entity)) ⊤)))
    (synth () (Among Speaker Audience))
    (synth () (Presuppose ⊤ ⊤))
    (check () (Presuppose ⊤ (Context))
           (RefComp (Referents Entity)))
    (synth ((Q (EFn (Entity) Content))) (Distrib Q Speaker))
    (synth ((P (Fn (Entity) Content))) (CoveredBy P Speaker))
    (synth () (Overlap Speaker Audience))
    (synth () (+ 1 2))
    (synth ((P (Fn (Entity) Content))
            (Q (EFn ((Referents Entity)) Content)))
           (AtLeast 0 P Q))
    (synth ((P (Fn (Entity) Content))
            (Q (EFn ((Referents Entity)) Content)))
           (AtLeast 1 P Q))
    (synth ((n Natural) (P (Fn (Entity) Content))
            (Q (EFn ((Referents Entity)) Content)))
           (AtLeast n P Q))
    (synth ((P (Fn (Entity) Content))
            (Q (EFn ((Referents Entity)) Content)))
           (Some P Q))
    (synth ((P (Fn (Entity) Content))
            (Q (EFn (Entity) Content)))
           (Every P Q))
    (synth ((P (Fn (Entity) Content))
            (Q (EFn ((Referents Entity)) Content)))
           (AtMost 1 P Q))
    (synth ((P (Fn (Entity) Content))
            (Q (EFn ((Referents Entity)) Content)))
           (FewerThan 0 P Q))
    (synth ((n Natural) (P (Fn (Entity) Content))
            (Q (EFn ((Referents Entity)) Content)))
           (FewerThan n P Q))
    (synth ((P (Fn (Entity) Content))
            (Q (EFn ((Referents Entity)) Content)))
           (FewerThan 1 P Q))))

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
          (make-coverage a0-hoist)
          (make-coverage b1-expand-at-least)
          (make-coverage b1-expand-some)
          (make-coverage b1-expand-every)
          (make-coverage b1-expand-no)
          (make-coverage b1-expand-at-most)
          (make-coverage b1-expand-more-than)
          (make-coverage b1-expand-fewer-than)
          (make-coverage b1-expand-distrib)
          (make-coverage b1-expand-overlap)
          (make-coverage b1-expand-covered-by)
          (make-coverage b1-expand-select-some)
          (make-coverage b1-expand-max-refer)))
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
    (term (b1-expand-at-least 0 Entity P Q))
    (term (b1-expand-at-least 2 Entity P Q))
    (term (b1-expand-some Entity P Q))
    (term (b1-expand-every Entity P Q))
    (term (b1-expand-no Entity P Q))
    (term (b1-expand-at-most n Entity P Q))
    (term (b1-expand-more-than n Entity P Q))
    (term (b1-expand-fewer-than n Entity P Q))
    (term (b1-expand-distrib Entity Q r))
    (term (b1-expand-overlap Entity a b))
    (term (b1-expand-covered-by Entity P r))
    (term (b1-expand-select-some Entity P))
    (term (b1-expand-max-refer Entity P))
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
    `(Let (,(string->symbol (format "$growth_~a_~a" salt index)) Natural)
       ,value
       ,body)))

(define (run-a0-size-growth #:depths [depths '(16 32 64)]
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
