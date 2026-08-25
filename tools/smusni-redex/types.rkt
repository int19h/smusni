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
  '(Every No Exactly AtLeast MoreThan Reciprocate CardBasis CoRef Named
          Realizes SpeakerOf EvidentialBasis Happiness Unhappiness Desire
          AdmissibleCutoff AdmissibleThreshold MetalinguisticallyDefective
          Contrast JaiRoleAdmissible CompleteGunmaAt GunmaAt Tanru Scalar
          Grade JaiRaise DuhuRel NiRel SuhuRel JeiRel StructuredQuote
          OpaqueQuote WordSign InterpretContent RealizedContent AmountValue
          ZipWith))

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
       [`(PredTerm ,_ ...) #t]
       [`(Record ,_) #t]
       [`(Row ,fields ...)
        (andmap (lambda (field)
                  (and (list? field) (= (length field) 2)
                       (or (exact-positive-integer? (first field))
                           (eq? (first field) 'Eventuality))
                       (type-well-formed? (second field))))
                fields)]
       [`(RowOf ,(? symbol? _)) #t]
       [`(RowMinus ,row ,_) (type-well-formed? row)]
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
    ;; A pure function is admissible where an effectful function is allowed.
    [(match* (actual expected)
       [(`(Fn ,params-a ,result-a) `(EFn ,params-e ,result-e))
        (and (= (length params-a) (length params-e))
             (andmap values
                     (map type-compatible? params-e params-a))
             (type-compatible? result-a result-e))]
       [(_ _) #f]) #t]
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
        (unless (or (type-compatible? restriction-type
                                      `(Fn ((Referents ,inner)) Content))
                    (type-compatible? restriction-type `(Fn (,inner) Content))
                    (type-compatible? restriction-type
                                      `(EFn ((Referents ,inner)) Content))
                    (type-compatible? restriction-type `(EFn (,inner) Content))
                    (and (eq? inner 'Eventuality)
                         (type-compatible? restriction-type 'ClauseContent)))
          (raise-type (first arguments)
                      "Refer restrictor has wrong type: ~e" restriction-type))
        (merge-results expected (list restriction) #:effects (set 'refer))]
       [_ (raise-type node "Refer requires RefComp<Referents<T>> expected type")])]
    [(member head '(SelectExactly SelectAtLeast))
     (match expected
       [`(RefComp (Referents ,inner))
        (define arguments (rest (core-list-elements node)))
        (unless (= (length arguments) 2)
          (raise-type node "~a takes a count and restrictor" head))
        (define count-result (infer-core (first arguments) env inv))
        (ensure-compatible (first arguments) (typing-type count-result) 'Natural)
        (define restriction (infer-core (second arguments) env inv))
        (unless (type-compatible? (typing-type restriction) `(Fn (,inner) Content))
          (raise-type (second arguments) "selection restrictor has wrong type"))
        (unless (pure-typing? restriction)
          (raise-type (second arguments) "selection restrictor must be pure"))
        (merge-results expected (list count-result restriction) #:effects (set 'refer))]
       [_ (raise-type node "~a requires RefComp<Referents<T>> expected type" head)])]
    [(eq? head 'Local)
     (match expected
       [`(RefComp ,inner)
        (define arguments (rest (core-list-elements node)))
        (unless (= (length arguments) 1) (raise-type node "Local takes one operand"))
        (define operand (infer-with-expected (first arguments) env inv expected))
        (merge-results expected (list operand))]
       [_ (raise-type node "Local is restricted to RefComp")])]
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
                        '(Context Vague Refer SelectExactly SelectAtLeast Local))
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
     (merge-results `(Act ,(if (eq? head 'Assert) 'Assertion 'Expressive))
                    (list content))]
    [(eq? head 'Mention)
     (unless (= (length arguments) 1) (raise-type node "Mention takes one value"))
     (define value (infer-core (first arguments) env inv))
     (merge-results '(Act Assertion) (list value))]
    [(eq? head 'Ask)
     (unless (= (length arguments) 1) (raise-type node "Ask takes one Query"))
     (define query (infer-core (first arguments) env inv))
     (match (typing-type query)
       [`(Query ,_) (merge-results '(Act Question) (list query))]
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
     (match (typing-type property)
       [`(Fn (,domain) Content)
        (unless (pure-typing? property) (raise-type node "SetOf property must be pure"))
        (merge-results `(Set ,domain) (list property))]
       [other (raise-type node "SetOf requires pure unary property, got ~e" other)])]
    [(eq? head 'Card)
     (unless (= (length arguments) 1) (raise-type node "Card takes Set<T>"))
     (define set-result (infer-core (first arguments) env inv))
     (match (typing-type set-result)
       [`(Set ,_) (merge-results 'Cardinal (list set-result))]
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
    [(member head '(Every No Exactly AtLeast MoreThan))
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (merge-results 'Content results)]
    [(eq? head 'Generic)
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (unless (member (length results) '(3 4))
       (raise-type node "Generic takes mode, optional holder, restrictor, nuclear scope"))
     (define restrictor (list-ref results (- (length results) 2)))
     (define nuclear (last results))
     (match* ((typing-type restrictor) (typing-type nuclear))
       [(`(Fn (,left) Content) `(,arrow (,right) Content))
        #:when (and (member arrow '(Fn EFn)) (type-compatible? left right))
        (merge-results 'Content results)]
       [(left right)
        (raise-type node "Generic restrictor/nuclear mismatch: ~e, ~e" left right)])]
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
    [(member head '(Named Realizes SpeakerOf EvidentialBasis Happiness Unhappiness
                          Desire AdmissibleCutoff AdmissibleThreshold
                          MetalinguisticallyDefective Contrast JaiRoleAdmissible
                          CompleteGunmaAt GunmaAt CoRef))
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (merge-results 'Content results)]
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
     (define body (infer-body (second arguments) (extend-env env bindings) inv))
     (ensure-compatible (second arguments) (typing-type body) 'Content)
     (merge-results (if (eq? head 'Utterance)
                        '(Sign Sentence)
                        '(Sign UnknownKind))
                    (list body))]
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
     (merge-results '(PredTerm Derived 0 #f) (list relation))]
    [(member head '(StructuredQuote OpaqueQuote WordSign InterpretContent
                                    RealizedContent AmountValue ZipWith))
     (define results (map (lambda (arg) (infer-core arg env inv)) arguments))
     (define type
       (case head
         [(OpaqueQuote WordSign StructuredQuote) '(Sign Sentence)]
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
