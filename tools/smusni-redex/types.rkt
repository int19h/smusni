#lang racket

(require racket/list
         racket/match
         racket/set
         racket/string
         redex/reduction-semantics
         "inventory.rkt"
         "syntax.rkt")

(provide (struct-out typing)
         (struct-out exn:fail:smusni)
         parse-type
         type-well-formed?
         type-compatible?
         infer-core
         infer-specimen-forms
         pass-through-forms
         pure-typing?
         SmusniStatic
         type-compatible)

(struct typing (type effects obligations gaps) #:transparent)
(struct exn:fail:smusni exn:fail (source line column) #:transparent)

(define pass-through-forms
  '(Reciprocate CardBasis CoRef Named
          Realizes SpeakerOf EvidentialBasis Happiness Unhappiness Desire
          AdmissibleCutoff AdmissibleThreshold MetalinguisticallyDefective
          Contrast JaiRoleAdmissible CompleteGunmaAt GunmaAt Aggregate
          CanonicalAggregateAt Tanru Scalar Grade JaiRaise DuhuRel NiRel
          SuhuRel JeiRel InterpretContent
          RealizedContent AmountValue ZipWith))

(define-language SmusniStatic
  [τ any])

;; A small Redex judgment used by the Racket inference layer and its tests.
;; Rich inference remains extrinsic because ill-typed ASTs must be representable.
(define-judgment-form SmusniStatic
  #:mode (type-compatible I I)
  #:contract (type-compatible τ τ)
  [(side-condition ,(type-compatible? (term τ_1) (term τ_2)))
   ------------------------------------
   (type-compatible τ_1 τ_2)])

(define empty-effects (set))

(define (raise-type node format-string . arguments)
  (define message (apply format format-string arguments))
  (define source
    (cond [(core-atom? node) (core-atom-source node)]
          [(core-list? node) (core-list-source node)]
          [else #f]))
  (define line
    (cond [(core-atom? node) (core-atom-line node)]
          [(core-list? node) (core-list-line node)]
          [else #f]))
  (define column
    (cond [(core-atom? node) (core-atom-column node)]
          [(core-list? node) (core-list-column node)]
          [else #f]))
  (raise (exn:fail:smusni
          (format "~a:~a:~a: ~a" (or source 'smusni) (or line "?")
                  (or column "?") message)
          (current-continuation-marks)
          source line column)))

(define (atom-value node)
  (and (core-atom? node) (core-atom-value node)))

(define (application-head node)
  (and (core-list? node)
       (pair? (core-list-elements node))
       (atom-value (first (core-list-elements node)))))

(define (dynamic-effect? effect)
  (member effect '(context refer projective performance effectful-call)))

(define (pure-typing? result)
  (not (for/or ([effect (in-set (typing-effects result))])
         (dynamic-effect? effect))))

(define (same-parameter-type? left right)
  ;; Parameter identity is stricter than the one-way singleton lift used at
  ;; referential value positions.  A member property and a reference property
  ;; are not interchangeable GQ operands.
  (and (type-compatible? left right)
       (type-compatible? right left)))

(define (pure-property-domain node result position)
  (match (typing-type result)
    [`(Fn (,domain) Content)
     (unless (pure-typing? result)
       (raise-type node
                   "~a violates the L0.1 pure-position requirement"
                   position))
     domain]
    [`(EFn (,_) Content)
     (raise-type node
                 "~a must be a pure Fn under L0.1"
                 position)]
    [other
     (raise-type node
                 "~a must be a pure unary property per L0.1, got ~e"
                 position other)]))

(define (property-domain node result position)
  (match (typing-type result)
    [`(,arrow (,domain) Content)
     #:when (member arrow '(Fn EFn))
     domain]
    ['ClauseContent '(Referents Eventuality)]
    [other
     (raise-type node "~a must be a unary Fn or EFn property, got ~e"
                 position other)]))

(define (ensure-same-property-domain node left right position)
  (unless (same-parameter-type? left right)
    (raise-type node "~a domain mismatch: ~e versus ~e" position left right)))

(define (effectful-property? result)
  (match (typing-type result)
    [`(EFn (,_ ...) Content) #t]
    ['ClauseContent #t]
    [_ #f]))

(define (gq-result-effects nuclear #:exports? exports?)
  (define effects
    (if (effectful-property? nuclear)
        (set 'effectful-call)
        empty-effects))
  (if exports? (set-add effects 'refer) effects))

(define card-definedness-effects (set 'projective))
(define card-definedness-obligations '(finite-set-cardinality-defined))

(define (literal-zero? node)
  (and (core-atom? node) (equal? (core-atom-value node) 0)))

(define (merge-results type results
                       #:effects [extra-effects empty-effects]
                       #:obligations [extra-obligations '()]
                       #:gaps [extra-gaps '()])
  (typing type
          (for/fold ([effects extra-effects]) ([result (in-list results)])
            (set-union effects (typing-effects result)))
          (append extra-obligations
                  (append-map typing-obligations results))
          (append extra-gaps (append-map typing-gaps results))))

(define (suspend-results type results)
  ;; First-class act constructors package their payloads without running them.
  (typing type empty-effects
          (append-map typing-obligations results)
          (append-map typing-gaps results)))

(define (type-constructor? value)
  (member value '(Referents Set Group List Act ActOccurrence RefComp PerfComp
                             Query Sign SignToken Record PredTerm Fn EFn
                             DecompositionBasis ContributionBasis Family+
                             ContrastDomain Region)))

(define (legacy-angle-type? symbol)
  (and (symbol? symbol)
       (regexp-match? #px"[<>,]" (symbol->string symbol))))

(define (parse-type-node node)
  (cond
    [(core-atom? node)
     (define value (core-atom-value node))
     (when (legacy-angle-type? value)
       (raise-type node "legacy angle/comma type spelling is not §2 flat syntax: ~a"
                   value))
     value]
    [(core-list? node)
     (define elements (core-list-elements node))
     (when (or (null? elements)
               (member (application-head node) '(quote unquote)))
       (raise-type node "invalid nested type instantiation"))
     (parse-type elements)]
    [else (raise-type node "type instantiation must use atoms/parentheses")]))

(define (parse-type nodes)
  (unless (pair? nodes) (error 'parse-type "empty type spine"))
  (define first-type (parse-type-node (first nodes)))
  (cond
    [(null? (rest nodes)) first-type]
    [(member first-type '(Fn EFn))
     (unless (and (= (length nodes) 3) (core-list? (second nodes)))
       (raise-type (first nodes)
                   "~a type syntax is ~a (A B) C with one parameter-list operand"
                   first-type first-type))
     (define parameters
       (for/list ([parameter (in-list (core-list-elements (second nodes)))])
         (parse-type-node parameter)))
     `(,first-type ,parameters ,(parse-type-node (third nodes)))]
    [(eq? first-type 'Row)
     `(Row
       ,@(for/list ([field (in-list (rest nodes))])
           (unless (and (core-list? field)
                        (>= (length (core-list-elements field)) 2))
             (raise-type field "Row fields are (label type) lists"))
           (define field-elements (core-list-elements field))
           `(,(parse-type-node (first field-elements))
             ,(parse-type (rest field-elements)))))]
    [(not (symbol? first-type))
     (raise-type (first nodes) "type constructor must be a symbol")]
    [else `(,first-type ,@(map parse-type-node (rest nodes)))]))

(define (first-order-type? type)
  (cond
    [(symbol? type)
     (not (member type '(Content ClauseContent Discourse Unit Bool)))]
    [(and (list? type) (pair? type))
     (case (first type)
       [(Set Group List Sign SignToken) (andmap first-order-type? (rest type))]
       [else #f])]
    [else #f]))

(define (quantifier-domain-type? type)
  (or (first-order-type? type)
      (match type
        [`(Referents ,inner) (first-order-type? inner)]
        [_ #f])))

(define (type-well-formed? type [inv (load-inventory)])
  (cond
    [(symbol? type) #t]
    [(and (list? type) (pair? type))
     (match type
       [`(Referents ,inner) (first-order-type? inner)]
       [`(Set ,inner) (first-order-type? inner)]
       [`(Group ,inner) (first-order-type? inner)]
       [`(List ,inner) (first-order-type? inner)]
       [`(Act ,_) #t]
       [`(ActOccurrence ,_) #t]
       [`(RefComp ,_) #t]
       [`(PerfComp ,_) #t]
       [`(Query ,_) #t]
       [`(Sign ,_) #t]
       [`(SignToken ,_) #t]
       [`(PredTerm ,row ,_ ...)
        (if (and (list? row) (member (first row) '(Row RowOf RowMinus)))
            (type-well-formed? row inv)
            #t)]
       [`(Record ,_) #t]
       [`(Row ,fields ...)
        (andmap (lambda (field)
                  (and (list? field) (= (length field) 2)
                       (or (exact-positive-integer? (first field))
                           (eq? (first field) 'Eventuality))
                       (type-well-formed? (second field))))
                fields)]
       [`(RowOf ,(? symbol? head))
        (hash-has-key? (inventory-rows inv) head)]
       [`(RowMinus ,row ,label)
        (and (type-well-formed? row inv)
             (let ([shape (row-index-shape row inv)])
               (and shape
                    (or (and (exact-positive-integer? label)
                             (<= label (first shape)))
                        (and (eq? label 'Eventuality) (second shape))))))]
       [`(Label ,row) (type-well-formed? row)]
       [`(Fn ,params ,result)
        (and (list? params) (andmap type-well-formed? params)
             (type-well-formed? result))]
       [`(EFn ,params ,result)
        (and (list? params) (andmap type-well-formed? params)
             (type-well-formed? result))]
       [`(DecompositionBasis ,whole ,component)
        (and (first-order-type? whole) (first-order-type? component))]
       [`(ContributionBasis ,_) #t]
       [`(ContrastDomain ,_) #t]
       [`(CompatibleLabel ,_ ...) #t]
       [`(Region ,_) #t]
       [else #f])]
    [else #f]))

(define default-subsorts
  '((Achievement Eventuality) (Process Eventuality) (Activity Eventuality)
    (State Eventuality) (Experience Eventuality) (Locution Eventuality)
    (Eventuality Entity) (Location Entity) (Time Entity) (Amount Entity)
    (Scale Entity) (Epistemology Entity) (TruthValue Entity) (Concept Entity)
    (AbstractNature Entity) (Proposition Entity) (Question Entity)
    (Number Entity) (Natural Number) (Cardinal Natural) (Text Entity)
    (UtteranceToken Entity) (Ground Entity)))

(define (subsort? actual expected [seen (set)])
  (or (equal? actual expected)
      (and (symbol? actual) (symbol? expected)
           (not (set-member? seen actual))
           (for/or ([edge (in-list default-subsorts)]
                    #:when (eq? (first edge) actual))
             (subsort? (second edge) expected (set-add seen actual))))))

(define (function-type? type)
  (match type
    [`(,arrow ,(? list?) ,_) (member arrow '(Fn EFn))]
    [_ #f]))

(define (arrow-compatible? actual expected)
  (or (eq? actual expected)
      (and (eq? actual 'Fn) (eq? expected 'EFn))))

(define (type-compatible? actual expected)
  (cond
    [(or (equal? actual 'Unknown) (equal? expected 'Unknown)) #t]
    [(equal? actual expected) #t]
    [(subsort? actual expected) #t]
    ;; ClauseContent is transparent to its EFn representation, never to
    ;; Content. CloseClause remains the only general crossing to Content.
    [(and (equal? actual 'ClauseContent)
          (match expected
            [`(EFn ((Referents Eventuality)) Content) #t]
            [`(Fn ((Referents Eventuality)) Content) #t]
            [_ #f])) #t]
    [(and (equal? expected 'ClauseContent)
          (match actual
            [`(EFn ((Referents Eventuality)) Content) #t]
            [`(Fn ((Referents Eventuality)) Content) #t]
            [_ #f])) #t]
    ;; Singleton lifting is a typing rule, never an object-language operator.
    [(match expected [`(Referents ,inner) (type-compatible? actual inner)] [_ #f]) #t]
    ;; Functions are contravariant in every parameter and covariant in their
    ;; result.  A pure function refines the corresponding effectful function.
    ;; The token-sort spelling used by Utterance/Sign is handled explicitly in
    ;; those entry-notation rules, never by relaxing this function rule.
    [(and (function-type? actual) (function-type? expected))
     (match* (actual expected)
       [(`(,arrow-a ,params-a ,result-a) `(,arrow-e ,params-e ,result-e))
        (and (arrow-compatible? arrow-a arrow-e)
             (= (length params-a) (length params-e))
             (for/and ([param-a (in-list params-a)]
                       [param-e (in-list params-e)])
               (type-compatible? param-e param-a))
             (type-compatible? result-a result-e))])]
    [(or (function-type? actual) (function-type? expected)) #f]
    [(and (list? actual) (list? expected)
          (= (length actual) (length expected))
          (eq? (first actual) (first expected)))
     (for/and ([left (in-list (rest actual))]
               [right (in-list (rest expected))])
       (if (and (list? left) (list? right))
           (and (= (length left) (length right))
                (for/and ([l (in-list left)] [r (in-list right)])
                  (type-compatible? l r)))
           (type-compatible? left right)))]
    [else #f]))

(define (ensure-compatible node actual expected)
  (unless (type-compatible? actual expected)
    (raise-type node "type mismatch: expected ~e, got ~e" expected actual)))

(define (body-term node)
  ;; Milestone 1.1 migrates direct forms to bare bodies. Retain a narrow
  ;; compatibility path for defined entry notations not yet synchronized.
  (if (and (core-list? node)
           (= (length (core-list-elements node)) 1)
           (core-list? (first (core-list-elements node))))
      (first (core-list-elements node))
      node))

(define (binder-separator elements node)
  (define positions
    (for/list ([element (in-list elements)] [index (in-naturals)]
               #:when (eq? (atom-value element) '::)) index))
  (unless (and (= (length positions) 1)
               (positive? (first positions))
               (< (first positions) (sub1 (length elements))))
    (raise-type node "malformed binder type ascription"))
  (first positions))

(define (parse-binder-group node)
  (unless (core-list? node)
    (raise-type node "expected binder list"))
  (define elements (core-list-elements node))
  (define separator (binder-separator elements node))
  (define names (take elements separator))
  (define type (parse-type (drop elements (add1 separator))))
  (unless (type-well-formed? type)
    (raise-type node "ill-formed type: ~e" type))
  (for/list ([name-node (in-list names)])
    (define name (atom-value name-node))
    (unless (and (symbol? name) (string-prefix? (symbol->string name) "$"))
      (raise-type name-node "binder name must begin with $"))
    (cons name type)))

(define (parse-telescope node)
  (unless (core-list? node)
    (raise-type node "expected binder/telescope list"))
  (define elements (core-list-elements node))
  (if (and (pair? elements)
           (core-list? (first elements)))
      (append-map parse-binder-group elements)
      (parse-binder-group node)))

(define (extend-env env bindings)
  (for/fold ([extended env]) ([binding (in-list bindings)])
    (hash-set extended (car binding) (cdr binding))))

(define (infer-atom node env inv)
  (define value (core-atom-value node))
  (cond
    [(number? value) (typing 'Natural empty-effects '() '())]
    [(string? value) (typing 'Text empty-effects '() '())]
    [(and (symbol? value) (string-prefix? (symbol->string value) "$"))
     (typing (hash-ref env value
                       (lambda () (raise-type node "unbound variable ~a" value)))
             empty-effects '() '())]
    [(and (symbol? value) (string-prefix? (symbol->string value) ":"))
     (typing 'LabelToken empty-effects '() '())]
    [(member value '(MiAOthers MaAOthers DoOOthers))
     (typing '(Referents Entity)
             (set 'projective)
             (list (case value
                     [(MiAOthers) 'mi-a-others-defined]
                     [(MaAOthers) 'ma-a-others-defined]
                     [(DoOOthers) 'do-o-others-defined]))
             '())]
    [(hash-has-key? (inventory-constants inv) value)
     (typing (first (hash-ref (inventory-constants inv) value))
             empty-effects '() '())]
    [(inventory-row inv value)
     (typing `(PredTerm ,value 0) empty-effects '() '())]
    [(inventory-name-declared? inv value)
     (typing `(Form ,value) empty-effects '() '())]
    [else
     (typing 'Unknown empty-effects '()
             (list (format "undeclared atom ~a" value))) ]))

(define (infer-body body env inv)
  (infer-core (body-term body) env inv))

(define (infer-lambda node env inv)
  (define elements (core-list-elements node))
  (define bindings (parse-telescope (second elements)))
  (define body (infer-body (third elements) (extend-env env bindings) inv))
  (define arrow (if (pure-typing? body) 'Fn 'EFn))
  (typing `(,arrow ,(map cdr bindings) ,(typing-type body))
          empty-effects
          (typing-obligations body)
          (typing-gaps body)))

(define (infer-let node env inv)
  (define elements (core-list-elements node))
  (define bindings (parse-binder-group (second elements)))
  (unless (= (length bindings) 1)
    (raise-type (second elements) "Let binds exactly one variable"))
  (define value-result (infer-core (third elements) env inv))
  (ensure-compatible (third elements) (typing-type value-result) (cdar bindings))
  (define body-result
    (infer-body (fourth elements) (extend-env env bindings) inv))
  (merge-results (typing-type body-result) (list value-result body-result)))

(define (computation-inner type)
  (match type
    [`(RefComp ,inner) (values 'ref inner)]
    [`(PerfComp ,inner) (values 'perf inner)]
    [_ (values #f #f)]))

(define (infer-with-expected node env inv expected)
  (define head (application-head node))
  (cond
    [(eq? head 'Context)
     (match expected
       [`(RefComp ,_)
        (typing expected (set 'context) '() '())]
       [_ (raise-type node "Context requires a RefComp expected type")])]
    [(eq? head 'Vague)
     (match expected
       [`(RefComp ,_)
        (typing expected (set 'context) '() '())]
       [_ (raise-type node "Vague requires a RefComp expected type")])]
    [(eq? head 'Refer)
     (match expected
       [`(RefComp (Referents ,inner))
        (define arguments (rest (core-list-elements node)))
        (unless (= (length arguments) 1)
          (raise-type node "Refer takes one restrictor"))
        (define restriction (infer-core (first arguments) env inv))
        (define restriction-type (typing-type restriction))
        ;; spec §5.3: the reference-level restrictor may be effectful (EFn);
        ;; a member-level restrictor is the pure CoveredBy lift and must be Fn.
        ;; Checked directly, because type-compatible? lifts a member-sorted
        ;; parameter to Referents covariantly (the §7.4/§7.5 entry-notation
        ;; allowance), which would otherwise admit EFn (T) Content here.
        (when (match restriction-type
                [`(EFn (,param) Content)
                 (not (match param [`(Referents ,_) #t] [_ #f]))]
                [_ #f])
          (raise-type (first arguments)
                      "Refer: a member-level restrictor must be a pure Fn (the §5.3 CoveredBy lift; hoist its sites outside the Refer), got ~e"
                      restriction-type))
        (unless (or (type-compatible? restriction-type
                                      `(Fn ((Referents ,inner)) Content))
                    (type-compatible? restriction-type `(Fn (,inner) Content))
                    (type-compatible? restriction-type
                                      `(EFn ((Referents ,inner)) Content))
                    (and (eq? inner 'Eventuality)
                         (type-compatible? restriction-type 'ClauseContent)))
          (raise-type (first arguments)
                      "Refer restrictor has wrong type (a member-level restrictor must be a pure Fn, spec §5.3): ~e"
                      restriction-type))
        (merge-results expected (list restriction) #:effects (set 'refer))]
       [_ (raise-type node "Refer requires RefComp<Referents<T>> expected type")])]
    [(member head '(SelectExactly SelectAtLeast SelectSome SelectAllBut))
     (match expected
       [`(RefComp (Referents ,inner))
        (define arguments (rest (core-list-elements node)))
        (define counted? (not (eq? head 'SelectSome)))
        (define expected-arity (if counted? 2 1))
        (unless (= (length arguments) expected-arity)
          (raise-type node (if counted?
                               "~a takes a count and restrictor"
                               "~a takes one restrictor")
                      head))
        (define count-results
          (if counted?
              (let ([count-result (infer-core (first arguments) env inv)])
                (ensure-compatible (first arguments) (typing-type count-result) 'Natural)
                (list count-result))
              '()))
        (define restriction-node (last arguments))
        (define restriction (infer-core restriction-node env inv))
        (define domain
          (pure-property-domain restriction-node restriction
                                (format "~a restrictor" head)))
        (ensure-same-property-domain restriction-node domain inner
                                     (format "~a restrictor" head))
        (merge-results expected (append count-results (list restriction))
                       #:effects (set 'refer))]
       [_ (raise-type node "~a requires RefComp<Referents<T>> expected type" head)])]
    [(eq? head 'Local)
     (match expected
       [`(RefComp ,inner)
        (define arguments (rest (core-list-elements node)))
        (unless (= (length arguments) 1) (raise-type node "Local takes one operand"))
        (define operand (infer-with-expected (first arguments) env inv expected))
        (merge-results expected (list operand))]
       [_ (raise-type node "Local is restricted to RefComp")])]
    [(eq? head 'Massify)
     (match expected
       [`(RefComp (Referents (Group ,inner)))
        (define arguments (rest (core-list-elements node)))
        (unless (= (length arguments) 2)
          (raise-type node "Massify takes group basis and component reference"))
        (define basis (infer-core (first arguments) env inv))
        (define cover (infer-core (second arguments) env inv))
        (ensure-compatible (first arguments) (typing-type basis)
                           `(DecompositionBasis (Group ,inner) ,inner))
        (ensure-compatible (second arguments) (typing-type cover)
                           `(Referents ,inner))
        (merge-results expected (list basis cover) #:effects (set 'refer))]
       [_ (raise-type node
                      "Massify requires RefComp<Referents<Group<T>>> expected type")])]
    [(eq? head 'JoiGroup)
     (match expected
       [`(RefComp (Referents (Group ,inner)))
        (define arguments (rest (core-list-elements node)))
        (unless (>= (length arguments) 3)
          (raise-type node "JoiGroup takes one group basis and at least two references"))
        (define basis (infer-core (first arguments) env inv))
        (define operands
          (map (lambda (argument) (infer-core argument env inv))
               (rest arguments)))
        (ensure-compatible (first arguments) (typing-type basis)
                           `(DecompositionBasis (Group ,inner) ,inner))
        (for ([argument (in-list (rest arguments))]
              [operand (in-list operands)])
          (ensure-compatible argument (typing-type operand)
                             `(Referents ,inner)))
        (merge-results expected (cons basis operands) #:effects (set 'refer))]
       [_ (raise-type node
                      "JoiGroup requires RefComp<Referents<Group<T>>> expected type")])]
    [else
     (define inferred (infer-core node env inv))
     (ensure-compatible node (typing-type inferred) expected)
     inferred]))

(define (infer-bind node env inv)
  (define elements (core-list-elements node))
  (define pieces (rest elements))
  (define body-node (last pieces))
  (define pairs (drop-right pieces 1))
  (let loop ([remaining pairs]
             [current-env env]
             [results '()]
             [saw-performance? #f])
    (if (null? remaining)
        (let ([body-result (infer-body body-node current-env inv)])
          (define act-body?
            (match (typing-type body-result) [`(Act ,_) #t] [_ #f]))
          (when (and saw-performance?
                     (not (or act-body?
                              (match (typing-type body-result)
                                [`(PerfComp ,_) #t]
                                ['Discourse #t]
                                [_ #f]))))
            (raise-type body-node
                        "a PerfComp Bind operand requires a performance-level body"))
          (merge-results (if (and saw-performance? act-body?)
                             'Discourse
                             (typing-type body-result))
                         (reverse (cons body-result results))
                         #:effects (if (and saw-performance? act-body?)
                                       (set 'performance)
                                       empty-effects)))
        (let* ([binder-node (first remaining)]
               [computation-node (second remaining)]
               [bindings (parse-binder-group binder-node)])
          (unless (= (length bindings) 1)
            (raise-type binder-node "Bind groups bind exactly one variable"))
          (define binding (first bindings))
          (define declared-type (cdr binding))
          (define computation
            (if (member (application-head computation-node)
                        '(Context Vague Refer SelectExactly SelectAtLeast SelectSome
                                  SelectAllBut Local
                                  Massify JoiGroup))
                (infer-with-expected computation-node current-env inv
                                     `(RefComp ,declared-type))
                (infer-core computation-node current-env inv)))
          (define-values (category inner) (computation-inner (typing-type computation)))
          (unless category
            (raise-type computation-node "Bind operand is not a computation: ~e"
                        (typing-type computation)))
          (ensure-compatible binder-node inner declared-type)
          (loop (drop remaining 2)
                (hash-set current-env (car binding) declared-type)
                (cons computation results)
                (or saw-performance? (eq? category 'perf)))))))

(define (infer-lexical-application node head arguments env inv row)
  (define argument-results
    (for/list ([argument (in-list arguments)]
               #:unless (and (core-atom? argument)
                             (symbol? (core-atom-value argument))
                             (string-prefix? (symbol->string (core-atom-value argument)) ":")))
      (infer-core argument env inv)))
  (define value-count
    (for/sum ([argument (in-list arguments)])
      (if (and (core-atom? argument)
               (symbol? (core-atom-value argument))
               (string-prefix? (symbol->string (core-atom-value argument)) ":"))
          0 1)))
  (define event-filled?
    (for/or ([argument (in-list arguments)])
      (eq? (atom-value argument) ':Eventuality)))
  (define ordinary-count (- value-count (if event-filled? 1 0)))
  (when (> ordinary-count (row-decl-total row))
    (raise-type node "row ~a has ~a ordinary places but received ~a fills"
                head (row-decl-total row) ordinary-count))
  (define output-type
    (if (and (= ordinary-count (row-decl-total row))
             (or (eq? (row-decl-event-mode row) 'holding-state)
                 event-filled?))
        'Content
        `(PredTerm ,head ,ordinary-count ,event-filled?)))
  (merge-results output-type argument-results))

(define (row-index-shape row inv)
  (cond
    [(symbol? row)
     (define declaration (inventory-row inv row))
     (and declaration
          (list (row-decl-total declaration)
                (eq? (row-decl-event-mode declaration) 'direct-event)))]
    [else
     (match row
       [`(RowOf ,(? symbol? head))
        (define declaration (inventory-row inv head))
        (and declaration
             (list (row-decl-total declaration)
                   (eq? (row-decl-event-mode declaration) 'direct-event)))]
       [`(RowMinus ,base ,label)
        (define base-shape (row-index-shape base inv))
        (and base-shape
             (cond
               [(and (exact-positive-integer? label)
                     (<= label (first base-shape)))
                (list (sub1 (first base-shape)) (second base-shape))]
               [(and (eq? label 'Eventuality) (second base-shape))
                (list (first base-shape) #f)]
               [else #f]))]
       [`(ArityRow ,(? exact-nonnegative-integer? count)) (list count #f)]
       [`(Row ,fields ...)
        (list (count (lambda (field)
                       (and (list? field) (exact-positive-integer? (first field))))
                     fields)
              (for/or ([field (in-list fields)])
                (and (list? field) (eq? (first field) 'Eventuality))))]
       [_ #f])]))

(define (argument-fill-counts arguments)
  (define event-filled?
    (for/or ([argument (in-list arguments)])
      (eq? (atom-value argument) ':Eventuality)))
  (define value-count
    (for/sum ([argument (in-list arguments)])
      (if (and (core-atom? argument)
               (symbol? (core-atom-value argument))
               (string-prefix? (symbol->string (core-atom-value argument)) ":"))
          0 1)))
  (values (- value-count (if event-filled? 1 0)) event-filled?))

(define (infer-predterm-application node pred-type operator results arguments inv)
  (match pred-type
    [`(PredTerm ,row ,filled ,event-already?)
     (define shape (row-index-shape row inv))
     (define-values (new-fills event-now?) (argument-fill-counts arguments))
     (define total-filled (+ filled new-fills))
     (when (and shape (> total-filled (first shape)))
       (raise-type node "PredTerm row has ~a ordinary places but application fills ~a"
                   (first shape) total-filled))
     (define event-filled? (or event-already? event-now?))
     (merge-results
      (if (and shape (= total-filled (first shape))
               (or (not (second shape)) event-filled?))
          'Content
          `(PredTerm ,row ,total-filled ,event-filled?))
      (cons operator results))]
    [`(PredTerm ,row)
     (infer-predterm-application node `(PredTerm ,row 0 #f)
                                 operator results arguments inv)]
    [`(PredTerm ,row ,filled)
     (infer-predterm-application node `(PredTerm ,row ,filled #f)
                                 operator results arguments inv)]
    [other (raise-type node "not a PredTerm application: ~e" other)]))

(define (infer-logical node head arguments env inv)
  (define results (map (lambda (argument) (infer-core argument env inv)) arguments))
  (for ([argument (in-list arguments)] [result (in-list results)])
    (ensure-compatible argument (typing-type result) 'Content))
  (merge-results 'Content results))

(define (infer-quantifier node head arguments env inv)
  (unless (= (length arguments) 1)
    (raise-type node "~a takes one property" head))
  (define property (infer-core (first arguments) env inv))
  (match (typing-type property)
    [`(,arrow ,domains Content)
     #:when (and (member arrow '(Fn EFn)) (pair? domains))
     (unless (andmap quantifier-domain-type? domains)
       (raise-type (first arguments)
                   "quantifier domains must be first-order/referential, got ~e"
                   domains))
     (merge-results 'Content (list property))]
    [other (raise-type (first arguments)
                       "quantifier requires a Content-valued property, got ~e" other)]))

(define (infer-application node env inv)
  (define elements (core-list-elements node))
  (define head-node (first elements))
  (define arguments (rest elements))
  (define head (atom-value head-node))
  (cond
    [(member head '(Context Vague Refer))
     (raise-type node
                 "~a is a retrieval/reference computation; bind it with an expected type and do not place it directly in a pure position"
                 head)]
    [(not head)
     (define operator (infer-core head-node env inv))
     (define argument-results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (match (typing-type operator)
       [`(,arrow ,params ,result)
        #:when (member arrow '(Fn EFn))
        (unless (= (length params) (length arguments))
          (raise-type node "function arity mismatch"))
        (for ([argument (in-list arguments)] [actual (in-list argument-results)]
              [expected (in-list params)])
          (ensure-compatible argument (typing-type actual) expected))
        (merge-results result (cons operator argument-results)
                       #:effects (if (eq? arrow 'EFn)
                                     (set 'effectful-call)
                                     empty-effects))]
       ['ClauseContent
        (unless (= (length arguments) 1)
          (raise-type node "ClauseContent application takes one event reference"))
        (ensure-compatible (first arguments)
                           (typing-type (first argument-results))
                           '(Referents Eventuality))
        (merge-results 'Content (cons operator argument-results)
                       #:effects (set 'effectful-call))]
       [`(PredTerm ,_ ,_ ...)
        (infer-predterm-application node (typing-type operator)
                                    operator argument-results arguments inv)]
       [other (typing 'Unknown empty-effects '()
                      (list (format "application of unsupported operator type ~e" other)))])]
    [(member head '(∧ ∨ →)) (infer-logical node head arguments env inv)]
    [(eq? head '¬)
     (unless (= (length arguments) 1) (raise-type node "¬ takes one Content"))
     (infer-logical node head arguments env inv)]
    [(member head '(∀ ∃)) (infer-quantifier node head arguments env inv)]
    [(eq? head '=)
     (unless (= (length arguments) 2) (raise-type node "= takes two operands"))
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (unless (or (type-compatible? (typing-type (first results))
                                   (typing-type (second results)))
                 (type-compatible? (typing-type (second results))
                                   (typing-type (first results))))
       (raise-type node "equality operands have incompatible types"))
     (merge-results 'Content results)]
    [(eq? head '∈)
     (unless (= (length arguments) 2) (raise-type node "∈ takes element and set"))
     (define element (infer-core (first arguments) env inv))
     (define set-result (infer-core (second arguments) env inv))
     (match (typing-type set-result)
       [`(Set ,inner)
        (unless (type-compatible? (typing-type element) inner)
          (raise-type (first arguments)
                      "set membership requires one ~e, got ~e"
                      inner (typing-type element)))
        (merge-results 'Content (list element set-result))]
       [other (raise-type (second arguments) "∈ requires Set<T>, got ~e" other)])]
    [(eq? head 'Among)
     (unless (= (length arguments) 2) (raise-type node "Among takes two references"))
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (match* ((typing-type (first results)) (typing-type (second results)))
       [(`(Referents ,left) `(Referents ,right))
        (unless (or (type-compatible? left right) (type-compatible? right left))
          (raise-type node "Among references have incompatible sorts"))
        (merge-results 'Content results)]
       [(left right) (raise-type node "Among requires plural references, got ~e and ~e"
                                left right)])]
    [(eq? head 'Combine)
     (unless (= (length arguments) 2)
       (raise-type node "Combine takes two plural references"))
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (define (reference-inner type)
       (match type
         [`(Referents ,inner) inner]
         [_ (and (first-order-type? type) type)]))
     (define left (reference-inner (typing-type (first results))))
     (define right (reference-inner (typing-type (second results))))
     (unless (and left right)
       (raise-type node "Combine requires referential values, got ~e and ~e"
                   (typing-type (first results)) (typing-type (second results))))
     (define common
       (cond [(type-compatible? left right) right]
             [(type-compatible? right left) left]
             [else #f]))
     (unless common (raise-type node "Combine references have incompatible sorts"))
     (merge-results `(Referents ,common) results)]
    [(or (member head '(+ −))
         (and (symbol? head) (string=? (symbol->string head) "te'a")))
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (for ([arg (in-list arguments)] [result (in-list results)])
       (ensure-compatible arg (typing-type result) 'Number))
     (merge-results 'Number results)]
    [(member head '(λ Let Bind))
     (case head
       [(λ) (infer-lambda node env inv)]
       [(Let) (infer-let node env inv)]
       [(Bind) (infer-bind node env inv)])]
    [(eq? head 'Close)
     (unless (= (length arguments) 1) (raise-type node "Close takes one operand"))
     (define operand (infer-core (first arguments) env inv))
     (match (typing-type operand)
       ['Content operand]
       ['ClauseContent
        (raise-type node "ClauseContent requires CloseClause, not Close/Content transparency")]
       [`(PredTerm ,row ,filled ,_event-filled)
        (define row-declaration (inventory-row inv row))
        (define defaults-remain?
          (or (not row-declaration)
              (< filled (row-decl-total row-declaration))))
        (merge-results 'Content (list operand)
                       #:effects (if defaults-remain?
                                     (set 'context)
                                     empty-effects))]
       [`(PredTerm ,_ ,_ ...)
        (merge-results 'Content (list operand) #:effects (set 'context))]
       [`(,arrow ,params Content)
        #:when (member arrow '(Fn EFn))
        (merge-results 'Content (list operand)
                       #:effects (if (or (eq? arrow 'EFn) (pair? params))
                                     (set 'context)
                                     empty-effects))]
       [other (raise-type node "Close cannot consume ~e" other)])]
    [(eq? head 'CloseClause)
     (unless (= (length arguments) 1) (raise-type node "CloseClause takes one operand"))
     (define operand (infer-core (first arguments) env inv))
     (ensure-compatible (first arguments) (typing-type operand) 'ClauseContent)
     (merge-results 'Content (list operand))]
    [(eq? head 'DirectClause)
     (unless (= (length arguments) 1) (raise-type node "DirectClause takes one predicate"))
     (define operand (infer-core (first arguments) env inv))
     (unless (match (typing-type operand) [`(PredTerm ,_ ,_ ...) #t] [_ #f])
       (raise-type node "DirectClause requires an open lexical predicate"))
     (merge-results 'ClauseContent (list operand))]
    [(eq? head 'StateClause)
     (unless (= (length arguments) 1) (raise-type node "StateClause takes Content"))
     (define operand (infer-core (first arguments) env inv))
     (ensure-compatible (first arguments) (typing-type operand) 'Content)
     (merge-results 'ClauseContent (list operand))]
    [(member head '(ActualClause CapableClause ClauseNot))
     (unless (= (length arguments) 1) (raise-type node "~a takes ClauseContent" head))
     (define operand (infer-core (first arguments) env inv))
     (ensure-compatible (first arguments) (typing-type operand) 'ClauseContent)
     (merge-results 'ClauseContent (list operand))]
    [(member head '(ClauseAnd ClauseOr))
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (for ([arg arguments] [result results])
       (ensure-compatible arg (typing-type result) 'ClauseContent))
     (merge-results 'ClauseContent results)]
    [(member head '(Assert Express))
     (unless (= (length arguments) 1) (raise-type node "~a takes Content" head))
     (define content (infer-core (first arguments) env inv))
     (ensure-compatible (first arguments) (typing-type content) 'Content)
     (suspend-results `(Act ,(if (eq? head 'Assert) 'Assertion 'Expressive))
                      (list content))]
    [(eq? head 'Mention)
     (unless (= (length arguments) 1) (raise-type node "Mention takes one value"))
     (define value (infer-core (first arguments) env inv))
     (suspend-results '(Act Expressive) (list value))]
    [(eq? head 'Ask)
     (unless (= (length arguments) 1) (raise-type node "Ask takes one Query"))
     (define query (infer-core (first arguments) env inv))
     (match (typing-type query)
       [`(Query ,_) (suspend-results '(Act Question) (list query))]
       [other (raise-type node "Ask requires Query, got ~e" other)])]
    [(eq? head 'ContextualAnswer)
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (merge-results 'Unknown results
                    #:gaps '("ContextualAnswer answer-domain inference is fixture-gapped"))]
    [(eq? head 'Answer)
     (unless (= (length arguments) 2)
       (raise-type node "Answer takes a query and an answer value"))
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (match (typing-type (first results))
       [`(Query ,_) (merge-results 'Content results)]
       [other (raise-type (first arguments) "Answer requires Query, got ~e" other)])]
    [(eq? head 'Polar)
     (unless (= (length arguments) 1) (raise-type node "Polar takes Content"))
     (define content (infer-core (first arguments) env inv))
     (ensure-compatible (first arguments) (typing-type content) 'Content)
     (merge-results '(Query Bool) (list content))]
    [(eq? head 'OpenQ)
     (unless (= (length arguments) 1) (raise-type node "OpenQ takes a function"))
     (define function (infer-core (first arguments) env inv))
     (match (typing-type function)
       [`(,arrow ,params Content)
        #:when (member arrow '(Fn EFn))
        (merge-results `(Query ,(if (= (length params) 1)
                                    (first params) `(Tuple ,@params)))
                       (list function))]
       [other (raise-type node "OpenQ requires a Content-valued function, got ~e" other)])]
    [(eq? head 'Perform)
     (unless (member (length arguments) '(1 2))
       (raise-type node "Perform takes an act, optionally preceded by a role"))
     (define act-node (last arguments))
     (define act (infer-core act-node env inv))
     (match (typing-type act)
       [`(Act ,force)
        (merge-results `(PerfComp (ActOccurrence ,force))
                       (list act) #:effects (set 'performance))]
       [other (raise-type act-node "Perform requires Act<F>, got ~e" other)])]
    [(eq? head 'Do)
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (for ([arg arguments] [result results])
       (unless (match (typing-type result)
                 ['Discourse #t]
                 [`(PerfComp ,_) #t]
                 [`(Act ,_) #t]
                 [_ #f])
         (raise-type arg "Do requires acts or performance computations")))
     (merge-results 'Discourse results #:effects (set 'performance))]
    [(eq? head 'Reify)
     (unless (= (length arguments) 1) (raise-type node "Reify takes Content"))
     (define content (infer-core (first arguments) env inv))
     (ensure-compatible (first arguments) (typing-type content) 'Content)
     ;; Reify packages Content without running its contextual computation.
     (typing 'Proposition empty-effects
             (typing-obligations content) (typing-gaps content))]
    [(eq? head 'Holds)
     (unless (= (length arguments) 1) (raise-type node "Holds takes Proposition"))
     (define proposition (infer-core (first arguments) env inv))
     (ensure-compatible (first arguments) (typing-type proposition)
                        '(Referents Proposition))
     (merge-results 'Content (list proposition))]
    [(eq? head 'EventOfContent)
     (unless (= (length arguments) 1) (raise-type node "EventOfContent takes Content"))
     (define content (infer-core (first arguments) env inv))
     (ensure-compatible (first arguments) (typing-type content) 'Content)
     (merge-results '(Referents Eventuality) (list content)
                    #:obligations '(EventOfContent-defined))]
    [(eq? head 'Presuppose)
     (unless (= (length arguments) 2) (raise-type node "Presuppose takes side and body"))
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (for ([arg arguments] [result results])
       (ensure-compatible arg (typing-type result) 'Content))
     (merge-results 'Content results #:effects (set 'projective))]
    [(eq? head 'Supplement)
     (unless (= (length arguments) 3) (raise-type node "Supplement takes anchor, side, body"))
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (ensure-compatible (second arguments) (typing-type (second results)) 'Content)
     (ensure-compatible (third arguments) (typing-type (third results)) 'Content)
     (merge-results 'Content results #:effects (set 'projective))]
    [(eq? head 'SetOf)
     (unless (= (length arguments) 1) (raise-type node "SetOf takes a pure property"))
     (define property (infer-core (first arguments) env inv))
     (define domain
       (pure-property-domain (first arguments) property "SetOf property"))
     (merge-results `(Set ,domain) (list property))]
    [(eq? head 'Card)
     (unless (= (length arguments) 1) (raise-type node "Card takes Set<T>"))
     (define set-result (infer-core (first arguments) env inv))
     (match (typing-type set-result)
       [`(Set ,_)
        (merge-results 'Cardinal (list set-result)
                       #:effects card-definedness-effects
                       #:obligations card-definedness-obligations)]
       [other (raise-type node "Card requires Set<T>, got ~e" other)])]
    [(eq? head 'CardBasis)
     (unless (= (length arguments) 2) (raise-type node "CardBasis takes reference and basis"))
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (merge-results 'Cardinal results)]
    [(eq? head 'Distrib)
     (unless (= (length arguments) 2) (raise-type node "Distrib takes property and reference"))
     (define property (infer-core (first arguments) env inv))
     (define reference (infer-core (second arguments) env inv))
     (match* ((typing-type property) (typing-type reference))
       [(`(,arrow (,domain) Content) `(Referents ,inner))
        #:when (member arrow '(Fn EFn))
        (unless (type-compatible? inner domain)
          (raise-type node "Distrib property/reference type mismatch"))
        (merge-results 'Content (list property reference))]
       [(left right) (raise-type node "Distrib types are incompatible: ~e, ~e" left right)])]
    [(eq? head 'CoveredBy)
     (unless (= (length arguments) 2)
       (raise-type node "CoveredBy takes a pure unit property and reference"))
     (define property (infer-core (first arguments) env inv))
     (define reference (infer-core (second arguments) env inv))
     (match* ((typing-type property) (typing-type reference))
       [(`(Fn (,domain) Content) `(Referents ,inner))
        (unless (pure-typing? property)
          (raise-type (first arguments) "CoveredBy unit property must be pure"))
        (unless (type-compatible? inner domain)
          (raise-type node "CoveredBy property/reference type mismatch"))
        (merge-results 'Content (list property reference))]
       [(left right)
        (raise-type node "CoveredBy types are incompatible: ~e, ~e" left right)])]
    [(member head '(Exactly AtLeast MoreThan AtMost FewerThan))
     (unless (= (length arguments) 3)
       (raise-type node "~a takes count, restrictor, and nuclear scope" head))
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (ensure-compatible (first arguments) (typing-type (first results)) 'Natural)
     (define restrictor-domain
       (pure-property-domain (second arguments) (second results)
                             (format "~a restrictor" head)))
     (define nuclear-domain
       (property-domain (third arguments) (third results)
                        (format "~a nuclear scope" head)))
     (match nuclear-domain
       [`(Referents ,inner)
        (ensure-same-property-domain (third arguments) restrictor-domain inner
                                     (format "~a restrictor/nuclear" head))]
       [other
        (raise-type (third arguments)
                    "~a nuclear scope must be reference-level EFn<(Referents<T>), Content>, got parameter ~e"
                    head other)])
     (merge-results 'Content results
                    #:effects
                    (if (and (eq? head 'AtLeast)
                             (literal-zero? (first arguments)))
                        empty-effects
                        (gq-result-effects
                         (third results)
                         #:exports?
                         (case head
                           [(MoreThan) #t]
                           [(Exactly AtLeast)
                            (not (literal-zero? (first arguments)))]
                           [else #f]))))]
    [(member head '(Some No))
     (unless (= (length arguments) 2)
       (raise-type node "~a takes restrictor and nuclear scope" head))
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (define restrictor-domain
       (pure-property-domain (first arguments) (first results)
                             (format "~a restrictor" head)))
     (define nuclear-domain
       (property-domain (second arguments) (second results)
                        (format "~a nuclear scope" head)))
     (match nuclear-domain
       [`(Referents ,inner)
        (ensure-same-property-domain (second arguments) restrictor-domain inner
                                     (format "~a restrictor/nuclear" head))]
       [other
        (raise-type (second arguments)
                    "~a nuclear scope must be reference-level EFn<(Referents<T>), Content>, got parameter ~e"
                    head other)])
     (merge-results 'Content results
                    #:effects
                    (gq-result-effects (second results)
                                       #:exports? (eq? head 'Some)))]
    [(eq? head 'Every)
     (unless (= (length arguments) 2)
       (raise-type node "Every takes restrictor and nuclear scope"))
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (define restrictor-domain
       (pure-property-domain (first arguments) (first results) "Every restrictor"))
     (define nuclear-domain
       (property-domain (second arguments) (second results) "Every nuclear scope"))
     (ensure-same-property-domain (second arguments) restrictor-domain nuclear-domain
                                  "Every restrictor/nuclear")
     (merge-results 'Content results
                    #:effects (gq-result-effects (second results) #:exports? #t))]
    [(member head '(GlobalExactly Most))
     (define counted? (eq? head 'GlobalExactly))
     (define expected-arity (if counted? 3 2))
     (unless (= (length arguments) expected-arity)
       (raise-type node (if counted?
                            "GlobalExactly takes count, restrictor, and nuclear scope"
                            "Most takes restrictor and nuclear scope")))
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (when counted?
       (ensure-compatible (first arguments) (typing-type (first results)) 'Natural))
     (define restrictor-index (if counted? 1 0))
     (define nuclear-index (if counted? 2 1))
     (define restrictor-domain
       (pure-property-domain (list-ref arguments restrictor-index)
                             (list-ref results restrictor-index)
                             (format "~a restrictor" head)))
     (define nuclear-domain
       (pure-property-domain (list-ref arguments nuclear-index)
                             (list-ref results nuclear-index)
                             (format "~a nuclear scope" head)))
     (ensure-same-property-domain (list-ref arguments nuclear-index)
                                  restrictor-domain nuclear-domain
                                  (format "~a restrictor/nuclear" head))
     (merge-results 'Content results
                    #:effects card-definedness-effects
                    #:obligations card-definedness-obligations)]
    [(eq? head 'Generic)
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (unless (member (length results) '(3 4))
       (raise-type node "Generic takes mode, optional holder, restrictor, nuclear scope"))
     (define restrictor (list-ref results (- (length results) 2)))
     (define nuclear (last results))
     (define restrictor-node (list-ref arguments (- (length arguments) 2)))
     (define nuclear-node (last arguments))
     (define restrictor-domain
       (pure-property-domain restrictor-node restrictor "Generic restrictor"))
     (define nuclear-domain
       (property-domain nuclear-node nuclear "Generic nuclear scope"))
     (ensure-same-property-domain nuclear-node restrictor-domain nuclear-domain
                                  "Generic restrictor/nuclear")
     (merge-results 'Content results
                    #:effects (if (effectful-property? nuclear)
                                  (set 'effectful-call)
                                  empty-effects))]
    [(eq? head 'Reciprocate)
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (merge-results 'Content results)]
    [(eq? head 'JoiPred)
     (unless (>= (length arguments) 3)
       (raise-type node "JoiPred requires one contribution basis and at least two predicates"))
     (define basis (infer-core (first arguments) env inv))
     (define predicates
       (map (lambda (arg) (infer-core arg env inv)) (rest arguments)))
     (match (typing-type basis)
       [`(ContributionBasis ,row)
        (for ([argument (in-list (rest arguments))]
              [predicate (in-list predicates)])
          (unless (match (typing-type predicate)
                    [`(PredTerm ,predicate-row ,_ ...)
                     (equal? predicate-row row)]
                    [_ #f])
            (raise-type argument
                        "JoiPred operands must share the contribution-basis row ~e"
                        row)))
        (merge-results `(PredTerm ,row) (cons basis predicates))]
       [other (raise-type (first arguments)
                          "JoiPred first operand must be ContributionBasis<ρ>, got ~e"
                          other)])]
    [(eq? head 'MeiRel)
     (unless (= (length arguments) 2)
       (raise-type node "MeiRel takes group basis and Natural cardinal"))
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (ensure-compatible (second arguments) (typing-type (second results)) 'Natural)
     (merge-results '(PredTerm MeiRelRow)
                    results
                    #:gaps (if (and (core-atom? (second arguments))
                                    (equal? (core-atom-value (second arguments)) 0))
                               '("MeiRel kappa 0 is gap #23")
                               '()))]
    [(member head '(DuhuRel NiRel SuhuRel JeiRel))
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (merge-results '(PredTerm (ArityRow 2) 0 #f) results)]
    [(member head '(Tanru Scalar Grade JaiRaise))
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (merge-results `(PredTerm ,head 0 #f) results)]
    [(eq? head 'LocutionOf)
     (unless (= (length arguments) 2)
       (raise-type node "LocutionOf takes a locution reference and an utterance token"))
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (ensure-compatible (first arguments) (typing-type (first results))
                        '(Referents Locution))
     (ensure-compatible (second arguments) (typing-type (second results))
                        '(Referents UtteranceToken))
     (merge-results 'Content results)]
    [(eq? head 'SpeakerDescribes)
     ;; §12: (SpeakerDescribes r P) ≝ (∃ {λ [$e :: Referents Locution]
     ;;   (∧ (LocutionOf $e CurrentToken) (skicu Speaker r Audience P :Eventuality $e))})
     ;; Every skicu place is filled and P is handed to x4 as a value, so the
     ;; form is pure whatever P's arrow; r lifts to its singleton reference.
     (unless (= (length arguments) 2)
       (raise-type node "SpeakerDescribes takes the described reference and a description property"))
     (define reference (infer-core (first arguments) env inv))
     (define property (infer-core (second arguments) env inv))
     (ensure-compatible (first arguments) (typing-type reference) '(Referents Entity))
     (match (typing-type property)
       [`(,arrow (,domain) Content)
        #:when (and (member arrow '(Fn EFn))
                    (type-compatible? domain '(Referents Entity)))
        (void)]
       [other
        (raise-type (second arguments)
                    "SpeakerDescribes description property must be a unary property of a reference, got ~e"
                    other)])
     (merge-results 'Content (list reference property))]
    [(member head '(Named Realizes SpeakerOf EvidentialBasis Happiness Unhappiness
                          Desire AdmissibleCutoff AdmissibleThreshold
                          MetalinguisticallyDefective Contrast JaiRoleAdmissible
                          CompleteGunmaAt GunmaAt Aggregate CanonicalAggregateAt
                          CoRef))
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (merge-results 'Content results)]
    [(eq? head 'components_κ)
     (unless (= (length arguments) 2)
       (raise-type node "components_κ takes basis and one group"))
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (match (typing-type (second results))
       [`(Group ,inner)
       (ensure-compatible (first arguments) (typing-type (first results))
                          `(DecompositionBasis (Group ,inner) ,inner))
       (merge-results `(Referents ,inner) results
                       #:effects (set 'projective)
                       #:obligations '(complete-group-cover-defined))]
       [other (raise-type (second arguments)
                          "components_κ requires one Group<T>, got ~e" other)])]
    [(eq? head 'List)
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (define inner (if (null? results) 'Unknown (typing-type (first results))))
     (for ([arg (in-list (rest arguments))] [result (in-list (rest results))])
       (ensure-compatible arg (typing-type result) inner))
     (merge-results `(List ,inner) results)]
    [(member head '(Utterance Sign))
     (unless (= (length arguments) 2)
       (raise-type node "~a entry notation takes binder and fact body" head))
     (define bindings (parse-binder-group (first arguments)))
     (unless (= (length bindings) 1)
       (raise-type (first arguments) "~a entry notation binds one token" head))
     (define binding (first bindings))
     (define declared-type (cdr binding))
     (define internal-type
       (case head
         [(Utterance)
          (unless (equal? declared-type 'UtteranceToken)
            (raise-type (first arguments)
                        "Utterance entry binder is ascribed UtteranceToken"))
          '(Referents UtteranceToken)]
         [(Sign)
          (match declared-type
            [`(SignToken ,kind) `(Referents (SignToken ,kind))]
            [other
             (raise-type (first arguments)
                         "Sign entry binder is ascribed SignToken<K>, got ~e"
                         other)])]))
     (define internal-binding (cons (car binding) internal-type))
     (define body
       (infer-body (second arguments)
                   (extend-env env (list internal-binding)) inv))
     (ensure-compatible (second arguments) (typing-type body) 'Content)
     (unless (pure-typing? body)
       (raise-type (second arguments) "~a entry property must be pure" head))
     (merge-results `(Fn (,internal-type) Content) (list body))]
    [(eq? head 'At)
     (unless (= (length arguments) 3)
       (raise-type node "At takes relation, bare numeral/Eventuality label, and value"))
     (define label (atom-value (second arguments)))
     (unless (or (exact-positive-integer? label)
                 (eq? label 'Eventuality)
                 (match (typing-type (infer-core (second arguments) env inv))
                   [`(CompatibleLabel ,_ ,_) #t]
                   [`(Label ,_) #t]
                   [_ #f]))
       (raise-type (second arguments)
                   "At label must be a bare numeral/Eventuality or typed label value"))
     (define relation (infer-core (first arguments) env inv))
     (define value (infer-core (third arguments) env inv))
     (unless (match (typing-type relation) [`(PredTerm ,_ ,_ ...) #t] [_ #f])
       (raise-type (first arguments) "At requires PredTerm"))
     (match (typing-type relation)
       [`(PredTerm ,row ,_ ...)
        (define shape (row-index-shape row inv))
        (when (and shape (or (exact-positive-integer? label)
                             (eq? label 'Eventuality))
                   (not (or (and (exact-positive-integer? label)
                                 (<= label (first shape)))
                            (and (eq? label 'Eventuality) (second shape)))))
          (raise-type (second arguments) "label ~a is outside row ~e" label row))]
       [_ (void)])
     (merge-results '(PredTerm Derived 0 #f) (list relation value))]
    [(eq? head 'DropPlace)
     (unless (= (length arguments) 2)
       (raise-type node "DropPlace takes relation and bare numeral/Eventuality label"))
     (define label (atom-value (second arguments)))
     (unless (or (exact-positive-integer? label) (eq? label 'Eventuality))
       (raise-type (second arguments)
                   "DropPlace label must be a bare positive numeral or Eventuality"))
     (define relation (infer-core (first arguments) env inv))
     (unless (match (typing-type relation) [`(PredTerm ,_ ,_ ...) #t] [_ #f])
       (raise-type (first arguments) "DropPlace requires PredTerm"))
     (match (typing-type relation)
       [`(PredTerm ,row ,_ ...)
        (define shape (row-index-shape row inv))
        (when (and shape
                   (not (or (and (exact-positive-integer? label)
                                 (<= label (first shape)))
                            (and (eq? label 'Eventuality) (second shape)))))
          (raise-type (second arguments) "label ~a is outside row ~e" label row))]
       [_ (void)])
     (merge-results '(PredTerm Derived 0 #f) (list relation))]
    [(member head '(OpaqueQuote WordSign NameSign LetteralSign))
     (unless (= (length arguments) 1)
       (raise-type node "~a takes one Text operand" head))
     (define operand (infer-core (first arguments) env inv))
     (ensure-compatible (first arguments) (typing-type operand) 'Text)
     (define kind
       (case head
         [(OpaqueQuote) 'Opaque]
         [(WordSign) 'Word]
         [(NameSign) 'Name]
         [(LetteralSign) 'Letteral]))
     (merge-results `(Sign ,kind) (list operand))]
    [(eq? head 'SentenceSign)
     (unless (= (length arguments) 1)
       (raise-type node "SentenceSign takes one Content operand"))
     (define operand (infer-core (first arguments) env inv))
     (ensure-compatible (first arguments) (typing-type operand) 'Content)
     (suspend-results '(Sign Sentence) (list operand))]
    [(eq? head 'StructuredQuote)
     (unless (= (length arguments) 1)
       (raise-type node "StructuredQuote takes one entry operand"))
     (define operand (infer-core (first arguments) env inv))
     (ensure-compatible (first arguments) (typing-type operand)
                        '(Fn ((Referents UtteranceToken)) Content))
     (merge-results '(Sign Structured) (list operand))]
    [(member head '(InterpretContent RealizedContent AmountValue ZipWith))
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (define type
       (case head
         [(InterpretContent RealizedContent) 'Content]
         [(AmountValue) 'Number]
         [(ZipWith) 'Content]))
     (merge-results type results)]
    [(inventory-row inv head)
     (infer-lexical-application node head arguments env inv (inventory-row inv head))]
    [(and (symbol? head) (string-prefix? (symbol->string head) "$"))
     (define operator (infer-atom head-node env inv))
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (match (typing-type operator)
       [`(,arrow ,params ,output)
        #:when (member arrow '(Fn EFn))
        (unless (= (length params) (length results))
          (raise-type node "bound function arity mismatch"))
        (for ([arg arguments] [result results] [expected params])
          (ensure-compatible arg (typing-type result) expected))
        (merge-results output (cons operator results)
                       #:effects (if (eq? arrow 'EFn)
                                     (set 'effectful-call)
                                     empty-effects))]
       ['ClauseContent
        (unless (= (length results) 1)
          (raise-type node "ClauseContent application takes one event reference"))
        (ensure-compatible (first arguments) (typing-type (first results))
                           '(Referents Eventuality))
        (merge-results 'Content (cons operator results)
                       #:effects (set 'effectful-call))]
       [`(PredTerm ,_ ,_ ...)
        (infer-predterm-application node (typing-type operator)
                                    operator results arguments inv)]
       [other (raise-type node "bound value is not applicable: ~e" other)])]
    [else
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (merge-results 'Unknown results
                    #:gaps (list (format "no typing rule for form ~a" head))) ]))

(define (infer-core node [env (hash)] [inv (load-inventory)])
  (cond
    [(core-atom? node) (infer-atom node env inv)]
    [else (infer-application node env inv)]))

(define (infer-specimen-forms forms [inv (load-inventory)])
  (for/list ([form (in-list forms)])
    (infer-core form (hash) inv)))
