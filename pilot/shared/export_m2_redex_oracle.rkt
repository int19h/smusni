#lang racket

(require json
         racket/cmdline
         racket/file
         racket/list
         racket/match
         racket/pretty
         racket/runtime-path
         racket/string
         redex/reduction-semantics
         "../../tools/smusni-redex/inventory.rkt"
         "../../tools/smusni-redex/port-a0.rkt"
         "../../tools/smusni-redex/port-phase0.rkt")

(define-runtime-path relative-root "../..")
(define root (simplify-path relative-root))
(define case-manifest-path (build-path root "pilot/shared/M2_CASE_MANIFEST.json"))
(define output-path (build-path root "pilot/shared/M2_REDEX_ORACLE.sexp"))
(define source-output-path (build-path root "pilot/shared/M2_ORACLE_SOURCES.sexp"))

(struct exn:fail:oracle-domain exn:fail (category stage))
(define (non-admission category stage format-string . arguments)
  (raise (exn:fail:oracle-domain
          (apply format format-string arguments) (current-continuation-marks)
          category stage)))
(define (domain-unavailable format-string . arguments)
  (apply non-admission 'expansion-domain-unavailable 'expansion format-string arguments))

(define (port-environment entries)
  (unless (and (list? entries) (andmap pair? entries)
               (andmap (lambda (entry) (symbol? (car entry))) entries))
    (non-admission 'malformed-input 'environment "malformed port environment"))
  (unless (= (length entries) (length (remove-duplicates (map car entries))))
    (non-admission 'malformed-input 'environment "duplicate port environment binding"))
  (for/list ([entry (in-list entries)])
    (match entry
      [(cons variable type) (list variable type)])))

;; The A0 judgment consumes lexical function declarations, not fixture names.
;; This mirrors the frozen port adapter's row input, using actual declared row
;; arity/event mode. Conflicting explicit declarations fail closed. No output values
;; or Lean results participate in constructing this environment.
(define inventory (load-inventory))
(define (row-environment datum)
  (define (declaration predicate arity event-mode)
    (list predicate
          `(Fn ,(append (make-list arity '(Referents Entity))
                        (if (eq? event-mode 'direct-event)
                            '((Referents Eventuality)) '())) Content)))
  (match datum
    [`(CloseWith (row ,predicate ,arity ,event-mode ,_) ,fills)
     (define row (inventory-row inventory predicate))
     (unless (and row (equal? arity (row-decl-total row))
                  (equal? event-mode (row-decl-event-mode row)))
       (non-admission 'malformed-input 'lexical-row
                      "missing or inconsistent CloseWith row declaration: ~e" predicate))
     (cons (declaration predicate arity event-mode) (row-environment fills))]
    [`(,(? symbol? predicate) ,arguments ...)
     (define row (inventory-row inventory predicate))
     (append (if row
                 (list (declaration predicate (row-decl-total row) (row-decl-event-mode row)))
                 '())
             (append-map row-environment arguments))]
    [(? list?) (append-map row-environment datum)]
    [_ '()]))

(define (with-row-environment environment datum)
  (define result (remove-duplicates (append environment (row-environment datum))))
  (unless (= (length result) (length (remove-duplicates (map first result))))
    (non-admission 'malformed-input 'environment "conflicting lexical/port declarations"))
  result)

(define (require-declared-variables datum environment)
  (define (walk child [env environment]) (require-declared-variables child env))
  (match datum
    [(? symbol? name)
     (when (and (string-prefix? (symbol->string name) "$")
                (not (assoc name environment)))
       (non-admission 'malformed-input 'environment "missing declaration for free variable ~a" name))]
    [`(λ ,binders ,body) (walk body (append binders environment))]
    [`(Let (,variable ,type) ,value ,body)
     (walk value)
     (walk body (cons (list variable type) environment))]
    [`(PerformSource (,first ,first-type) ,source ,content
                     (,read ,read-type) (,occurrence ,occurrence-type) ,continuation)
     ;; This is the grouped, Host/Assert-normalized adapter representation.
     ;; Its descriptors are declarations, not free variable occurrences. Each
     ;; arm starts from the incoming environment; none exports into a sibling.
     (walk source)
     (walk content (cons (list first first-type) environment))
     (walk continuation (append (list (list read read-type)
                                      (list occurrence occurrence-type)) environment))]
    [`(Bind ,bindings ,body)
     (define final-environment
       (for/fold ([env environment]) ([binding bindings])
         (match-define (list variable type value) binding)
         (walk value env)
         (cons (list variable type) env)))
     (walk body final-environment)]
    [(? list?) (for-each walk datum)]
    [_ (void)]))

;; Only these separately known contextual interfaces receive a named
;; unsupported diagnosis. Generic A0 application can parse an unknown symbol;
;; zero derivations alone do not prove that symbol's type is wrong.
(define unsupported-context-heads
  '(Assert Express Mention Ask Polar OpenQ SentenceSign NameSign WordSign
           LetteralSign StructuredQuote OpaqueQuote Reify Do PerformSource))
(define (unsupported-context-in datum)
  (match datum
    [`(,(? symbol? head) ,children ...)
     (or (and (member head unsupported-context-heads) head)
         (ormap unsupported-context-in children))]
    [(? list?) (ormap unsupported-context-in datum)]
    [_ #f]))

(define definition-manifest
  (call-with-input-file (build-path root "pilot/shared/M2_DEFINITION_MANIFEST.json") read-json))
(define selected-heads
  (remove-duplicates
   (cons 'CloseWith
         (for/list ([row (hash-ref definition-manifest 'definitions)]
                    #:unless (equal? (hash-ref row 'head) "Refer"))
           (string->symbol (hash-ref row 'head))))))

(define (residual-definition datum)
  (match datum
    [`(,(? symbol? head) ,children ...)
     (or (and (member head selected-heads) head)
         (ormap residual-definition children))]
    [(? list?) (ormap residual-definition datum)]
    [_ #f]))

(define (require-complete-expansion datum environment)
  (define residual (residual-definition datum))
  (when residual
    (domain-unavailable "residual selected definition after expansion: ~a" residual))
  (when (contains-member-refer? datum environment)
    (domain-unavailable "residual member-Refer lift has no admitted equation domain")))

;; Check every selected redex, including redexes introduced by expansion.
;; Expected modes below are the declared result types of these specific
;; checking-only definitions, inferred from their actual operands, not Lean.
(define (guard-definition datum environment)
  (when (and (pair? datum) (memq (car datum) selected-heads))
    (match datum
      [`(CoveredBy ,property ,_)
       (when (declared-effectful-property? property environment)
         (non-admission 'type/domain-rejected 'coveredby-purity
                        "CoveredBy member property is declared EFn (#83)"))]
      [_ (void)])
    ;; Frozen metafunction domains are narrower than some typing rules.
    ;; Reject these known expansion boundaries explicitly before Redex raises
    ;; a no-clause/contract exception; do not catch unrelated failures.
    (match datum
      [`(AtLeast ,count ,_ ,_)
       (unless (or (equal? count 0) (and (exact-integer? count) (positive? count))
                   (match count [`(+ ,_ 1) #t] [`(+ 1 ,_) #t] [_ #f]))
         (domain-unavailable "AtLeast symbolic-natural expansion is not selected"))]
      [`(Exactly ,count ,_ ,_)
       (unless (exact-nonnegative-integer? count)
         (domain-unavailable "Exactly metafunction requires a literal Natural"))]
      [`(ZipWith ,_ ,left ,right)
       (unless (match (list left right)
                 [(list `(List ,xs ...) `(List ,ys ...)) (= (length xs) (length ys))]
                 [_ #f])
         (domain-unavailable "ZipWith requires explicit equal-length lists (#41)"))]
      [_ (void)])
    (define env (with-row-environment environment datum))
    (unless (and (redex-match? SmusniA0 Γ env) (redex-match? SmusniA0 t datum))
      (non-admission 'grammar-unsupported 'expansion "selected redex outside A0 grammar: ~e" datum))
    (define expected
      (match datum
        [`(,(or 'SelectSome 'MaxRefer) ,property)
         (define type (member-type property env))
         (and type `(RefComp (Referents ,type)))]
        [`(Massify ,basis ,_)
         (match (basis-types basis env)
           [(list `(Group ,type) type) `(RefComp (Referents (Group ,type)))]
           [_ #f])]
        [_ #f]))
    (define typings
      (if expected
          (judgment-holds (a0-check ,env ,datum ,expected R) R)
          (judgment-holds (a0-synth ,env ,datum R) R)))
    (unless (= (length typings) 1)
      (non-admission 'unclassified-non-admission 'expansion
                     "selected redex has ~a admitted typings: ~e" (length typings) datum))))

(define (lookup-type environment variable)
  (match (assoc variable environment)
    [(list _ type) type]
    [_ #f]))

(define (member-type property environment)
  (match property
    [`(λ ((,_ ,type)) ,_) type]
    [(? symbol? variable)
     (match (lookup-type environment variable)
       [`(Fn (,type) Content) type]
       [`(EFn (,type) Content) type]
       [_ #f])]
    [_ #f]))

(define (declared-effectful-property? property environment)
  (and (symbol? property)
       (match (lookup-type environment property)
         [`(EFn (,_type) Content) #t]
         [_ #f])))

(define (reference-member term environment)
  (define type
    (cond [(eq? term 'Speaker) '(Referents Entity)]
          [(eq? term 'Audience) '(Referents Entity)]
          [(symbol? term) (lookup-type environment term)]
          [else #f]))
  (match type
    [`(Referents ,inner) inner]
    [_ #f]))

(define (basis-types basis environment)
  (match (and (symbol? basis) (lookup-type environment basis))
    [`(DecompositionBasis ,whole ,component) (list whole component)]
    [_ #f]))

(define (extend-lambda environment binders)
  (append binders environment))

(define (contains-member-refer? datum [environment '()])
  (define (walk child [env environment]) (contains-member-refer? child env))
  (match datum
    [`(λ ,binders ,body) (walk body (extend-lambda environment binders))]
    [`(Bind ,bindings ,body)
     (let loop ([remaining bindings] [env environment])
       (if (null? remaining) (walk body env)
           (match-let ([(list variable type value) (first remaining)])
             (or (walk value env)
                 (loop (rest remaining) (cons (list variable type) env))))))]
    [`(Refer ,property)
     (define typings
       (if (and (redex-match? SmusniA0 Γ environment)
                (redex-match? SmusniA0 t property))
           (judgment-holds (a0-synth ,environment ,property R) R) '()))
     (or (for/or ([record typings])
           (match record
             [`(typing (,(or 'Fn 'EFn) (,type) Content) ,_ ,_)
              (not (match type [`(Referents ,_) #t] [_ #f]))]
             [_ #f]))
         (walk property))]
    [(? list?) (ormap walk datum)]
    [_ #f]))

(define (actual-clause clause)
  (define event (variable-not-in clause '$actual_event))
  `(λ ((,event (Referents Eventuality)))
     (∧ (,clause ,event) (fasnu ,event))))

(define (gunma-at basis whole cover environment)
  (match (basis-types basis environment)
    [(list _ component)
     (define unit (variable-not-in (list basis whole cover) '$basis_unit))
     (define peer (variable-not-in (list basis whole cover unit) '$peer_unit))
     `(∀ (λ ((,unit (Referents ,component)))
           (→ (BasisUnitAt ,basis ,unit ,cover)
              (∃ (λ ((,peer (Referents ,component)))
                    (∧ (PeerUnitAt ,basis ,peer ,whole)
                       (∧ (Among ,unit ,peer) (Among ,peer ,unit))))))))]
    [_ (domain-unavailable "cannot infer GunmaAt basis type for ~e" basis)]))

(define (complete-gunma-at basis whole cover environment)
  (match (basis-types basis environment)
    [(list _ component)
     (define peer (variable-not-in (list basis whole cover) '$complete_peer))
     (define unit (variable-not-in (list basis whole cover peer) '$complete_unit))
     `(∧ ,(gunma-at basis whole cover environment)
         (∀ (λ ((,peer (Referents ,component)))
              (→ (PeerUnitAt ,basis ,peer ,whole)
                 (∃ (λ ((,unit (Referents ,component)))
                      (∧ (BasisUnitAt ,basis ,unit ,cover)
                         (∧ (Among ,unit ,peer) (Among ,peer ,unit)))))))))]
    [_ (domain-unavailable "cannot infer CompleteGunmaAt basis type for ~e" basis)]))

(define (expand-term datum environment)
  (guard-definition datum environment)
  (define (again value [env environment]) (expand-term value env))
  (match datum
    ['⊤ '⊤]
    [`(λ ,binders ,body)
     `(λ ,binders ,(again body (extend-lambda environment binders)))]
    [`(Bind ,bindings ,body)
     (let loop ([remaining bindings] [scope environment] [expanded '()])
       (if (null? remaining)
           `(Bind ,expanded ,(again body scope))
           (match-let ([(list variable type computation) (first remaining)])
             (loop (rest remaining)
                   (cons (list variable type) scope)
                   (append expanded
                           (list (list variable type (again computation scope))))))))]
    [`(Let (,variable ,type) ,value ,body)
     (again (term (a0-expand-let ,variable ,type ,value ,body)))]
    [`(Exactly ,count ,property ,nuclear)
     (define type (member-type property environment))
     (unless type (domain-unavailable "Exactly member type unavailable"))
     (again (term (a0-expand-exactly ,count ,type ,property ,nuclear)))]
    [`(AtLeast ,count ,property ,nuclear)
     (define type (member-type property environment))
     (unless type (domain-unavailable "AtLeast member type unavailable"))
     (define outputs (term (b1-expand-at-least ,count ,type ,property ,nuclear)))
     (if (equal? outputs `(b1-expand-at-least ,count ,type ,property ,nuclear))
         (domain-unavailable "AtLeast domain has no Redex expansion")
         (again outputs))]
    [`(Some ,property ,nuclear)
     (define type (member-type property environment))
     (unless type (domain-unavailable "Some member type unavailable"))
     (again (term (b1-expand-some ,type ,property ,nuclear)))]
    [`(Every ,property ,nuclear)
     (define type (member-type property environment))
     (unless type (domain-unavailable "Every member type unavailable"))
     (again (term (b1-expand-every ,type ,property ,nuclear)))]
    [`(No ,property ,nuclear)
     (define type (member-type property environment))
     (unless type (domain-unavailable "No member type unavailable"))
     (again (term (b1-expand-no ,type ,property ,nuclear)))]
    [`(,(and head (or 'IndividualSome 'IndividualNo 'IndividualEvery
                     'PluralSome 'PluralNo)) ,property ,nuclear)
     (define parameter (member-type property environment))
     (unless parameter (domain-unavailable "~a property type unavailable" head))
     (define output
       (case head
         [(IndividualSome) (term (e01-expand-individual-some ,parameter ,property ,nuclear))]
         [(IndividualNo) (term (e01-expand-individual-no ,parameter ,property ,nuclear))]
         [(IndividualEvery) (term (e01-expand-individual-every ,parameter ,property ,nuclear))]
         [else
          (match parameter
            [`(Referents ,inner)
             (if (eq? head 'PluralSome)
                 (term (e01-expand-plural-some ,inner ,property ,nuclear))
                 (term (e01-expand-plural-no ,inner ,property ,nuclear)))]
            [_ (domain-unavailable "~a requires a reference-level property" head)])]))
     (again output)]
    [`(Only ,alternatives ,host ,focus)
     (match (member-type alternatives environment)
       [`(Referents ,inner)
        (again (term (e01-expand-only ,inner ,alternatives ,host ,focus)))]
       [_ (domain-unavailable "Only alternatives require a reference-level property")])]
    [`(AtMost ,count ,property ,nuclear)
     (define type (member-type property environment))
     (unless type (domain-unavailable "AtMost member type unavailable"))
     (again (term (b1-expand-at-most ,count ,type ,property ,nuclear)))]
    [`(MoreThan ,count ,property ,nuclear)
     (define type (member-type property environment))
     (unless type (domain-unavailable "MoreThan member type unavailable"))
     (again (term (b1-expand-more-than ,count ,type ,property ,nuclear)))]
    [`(FewerThan ,count ,property ,nuclear)
     (define type (member-type property environment))
     (unless type (domain-unavailable "FewerThan member type unavailable"))
     (again (term (b1-expand-fewer-than ,count ,type ,property ,nuclear)))]
    [`(GlobalExactly ,count ,property ,nuclear)
     (define type (member-type property environment))
     (unless type (domain-unavailable "GlobalExactly member type unavailable"))
     (again (term (a0-expand-global-exactly ,count ,type ,property ,nuclear)))]
    [`(Distrib ,property ,reference)
     (define type (or (reference-member reference environment)
                      (member-type property environment)))
     (unless type (domain-unavailable "Distrib member type unavailable"))
     (again (term (b1-expand-distrib ,type ,property ,reference)))]
    [`(Overlap ,first ,second)
     (define type (or (reference-member first environment)
                      (reference-member second environment)))
     (unless type (domain-unavailable "Overlap member type unavailable"))
     (again (term (b1-expand-overlap ,type ,first ,second)))]
    [`(CoveredBy ,property ,reference)
     (when (declared-effectful-property? property environment)
       (domain-unavailable
              "CoveredBy member property is EFn; §5.3 purity rejects the term oracle (#83)"))
     (define type (or (member-type property environment)
                      (reference-member reference environment)))
     (unless type (domain-unavailable "CoveredBy member type unavailable"))
     (again (term (b1-expand-covered-by ,type ,property ,reference)))]
    [`(SelectSome ,property)
     (define type (member-type property environment))
     (unless type (domain-unavailable "SelectSome member type unavailable"))
     (again (term (b1-expand-select-some ,type ,property)))]
    [`(MaxRefer ,property)
     (define type (member-type property environment))
     (unless type (domain-unavailable "MaxRefer member type unavailable"))
     (again (term (b1-expand-max-refer ,type ,property)))]
    [`(TooMany ,property ,nuclear)
     (define type (member-type property environment))
     (unless type (domain-unavailable "TooMany member type unavailable"))
     (again (term (a0-expand-too-many ,type ,property ,nuclear)))]
    [`(Massify ,basis ,cover)
     (match (basis-types basis environment)
       [(list `(Group ,type) component)
        (unless (equal? type component) (domain-unavailable "Massify basis mismatch"))
        (again (term (a0-expand-massify ,type ,basis ,cover)))]
       [_ (domain-unavailable "Massify basis type unavailable")])]
    [`(ZipWith ,function ,left ,right)
     (define output (term (a0-expand-zipwith ,function ,left ,right)))
     (if (equal? output `(a0-expand-zipwith ,function ,left ,right))
         (domain-unavailable "ZipWith unequal-length domain")
         (again output))]
    [`(CloseWith ,row ,fills)
     (define output (term (a0-expand-close ,row ,fills)))
     (if (equal? output `(a0-expand-close ,row ,fills))
         (domain-unavailable "Close row domain unavailable")
         (again output))]
    [`(Close ,_)
     (domain-unavailable "Close has no adapter-supplied lexical row declaration")]
    [`(DirectClause ,property) (again property)]
    [`(ActualClause ,clause) (again (actual-clause clause))]
    [`(CoRef ,first ,second)
     (again `(∧ (Among ,first ,second) (Among ,second ,first)))]
    [`(GunmaAt ,basis ,whole ,cover)
     (again (gunma-at basis whole cover environment))]
    [`(CompleteGunmaAt ,basis ,whole ,cover)
     (again (complete-gunma-at basis whole cover environment))]
    [`(CanonicalAggregateAt ,basis ,group ,cover)
     (again `(∧ (Aggregate ,basis ,group)
                (CompleteGunmaAt ,basis ,group ,cover)))]
    [(? list?) (map again datum)]
    [_ datum]))

(define (a0->surface datum)
  (match datum
    ['⊤ '(∧)]
    [`(λ ,binders ,body)
     `(λ ,(for/list ([binder (in-list binders)])
            (match binder [`(,variable ,type) `(,variable :: ,type)]))
        ,(a0->surface body))]
    [`(Bind ,bindings ,body)
     `(Bind ,@(append-map
               (lambda (binding)
                 (match binding
                   [`(,variable ,type ,computation)
                    (list `(,variable :: ,type) (a0->surface computation))]))
               bindings)
            ,(a0->surface body))]
    [(? list?) (map a0->surface datum)]
    [_ datum]))

(define (typing-type record)
  (match record [`(typing ,type ,_ ,_) type]
    [_ (error 'm2-oracle "malformed internal typing record: ~e" record)]))

(define (assert-witness payload)
  (match payload
    [`(typing Content ,(? list? _effects) ,(? list? obligations))
     `(typing (Act Assertion) () ,obligations)]
    [_ (error 'assert-witness "payload witness is not Content: ~e" payload)]))

;; This small context certificate states only §7.1's inert Assert law.
;; Payload judgments themselves are produced independently by frozen Redex.
(define (validate-assert-certificate record source-payload target-payload)
  (define (get key)
    (match (assoc key (cdr record))
      [(list _ value) value]
      [_ (error 'assert-certificate "missing or malformed ~a" key)]))
  (unless (and (equal? (get 'context) 'assert-bridge)
               (equal? (get 'source-type) '(Act Assertion))
               (match (get 'term) [`(Assert ,_) #t] [_ #f])
               (equal? (get 'payload-source-typing) source-payload)
               (equal? (get 'payload-target-typing) target-payload)
               (equal? (get 'source-typing) (assert-witness source-payload))
               (equal? (get 'target-typing) (assert-witness target-payload)))
    (error 'assert-certificate "invalid wrapper/type/obligation witness"))
  #t)

(struct admitted-source (payload environment bridge? witness) #:transparent)

(define (prepare-source item)
  (define raw (port-case-term item))
  (define bridge? (and (pair? raw) (eq? (car raw) 'Assert)))
  (when (and bridge? (not (and (list? raw) (= (length raw) 2))))
    (non-admission 'malformed-input 'context "Assert requires exactly one payload"))
  (define input (legacy-datum->a0 raw))
  (define payload (if bridge? (second input) input))
  (define environment (with-row-environment (port-environment (port-case-env item)) input))
  (unless (redex-match? SmusniA0 Γ environment)
    (non-admission 'malformed-input 'environment "environment outside the A0 type vocabulary: ~e" environment))
  (require-declared-variables input environment)
  (when (and bridge? (pair? payload) (eq? (car payload) 'Assert))
    (unless (and (list? payload) (= (length payload) 2))
      (non-admission 'malformed-input 'context "nested Assert has malformed arity"))
    (non-admission 'type/domain-rejected 'assert-payload
                   "nested Assert cannot supply Content; its valid result type is Act Assertion"))
  (define unsupported (unsupported-context-in payload))
  (when unsupported
    (non-admission 'context-unsupported 'context
                   "no independent context rule for ~a within ~a"
                   unsupported (if bridge? 'Assert 'whole-source)))
  (unless (redex-match? SmusniA0 t payload)
    (non-admission 'grammar-unsupported 'source "outside frozen A0 payload grammar: ~e" payload))
  (when (contains-member-refer? payload environment)
    (domain-unavailable "Refer-member-lift has ledger port-state none; term oracle unavailable"))
  ;; Source synthesis is intentionally the first bridge's conservative mode.
  ;; Zero derivations are not evidence of semantic ill-typing.
  (define source-typings (judgment-holds (a0-synth ,environment ,payload R) R))
  (unless (= (length source-typings) 1)
    (non-admission 'unclassified-non-admission 'source
                   "source has ~a admitted A0 typings: ~e" (length source-typings) payload))
  (define source-witness (first source-typings))
  (define source-type (typing-type source-witness))
  (when (and bridge? (not (equal? source-type 'Content)))
    (non-admission 'type/domain-rejected 'assert-payload
                   "Assert requires literal Content; payload synthesizes ~e" source-type))
  (admitted-source payload environment bridge? source-witness))

(define (oracle-case item #:expand [expander expand-term])
  (with-handlers ([exn:fail:oracle-domain?
                   (lambda (exception)
                     `(case (id ,(port-case-id item))
                            (status unavailable)
                            (category ,(exn:fail:oracle-domain-category exception))
                            (stage ,(exn:fail:oracle-domain-stage exception))
                            (reason ,(exn-message exception))))])
    (match-define (admitted-source payload environment bridge? source-witness)
      (prepare-source item))
    (define source-type (typing-type source-witness))
    (define expanded (expander payload environment))
    (define output-environment (with-row-environment environment expanded))
    (require-complete-expansion expanded output-environment)
    (unless (redex-match? SmusniA0 Γ output-environment)
      (non-admission 'malformed-input 'target-environment "target lexical environment is outside A0"))
    (unless (redex-match? SmusniA0 t expanded)
      (non-admission 'grammar-unsupported 'target "outside frozen A0 target grammar: ~e" expanded))
    (define target-typings
      (judgment-holds (a0-check ,output-environment ,expanded ,source-type R) R))
    (unless (= (length target-typings) 1)
      (non-admission 'unclassified-non-admission 'target
                     "expanded target has ~a A0 typings at source type ~e"
                     (length target-typings) source-type))
    (define target-witness (first target-typings))
    (define output (a0->surface expanded))
    (cond
      [bridge?
       (define record
         `(case (id ,(port-case-id item)) (status available) (context assert-bridge)
                (source-type (Act Assertion))
                (source-typing ,(assert-witness source-witness))
                (target-typing ,(assert-witness target-witness))
                (payload-source-typing ,source-witness)
                (payload-target-typing ,target-witness)
                (term (Assert ,output))))
       (validate-assert-certificate record source-witness target-witness)
       record]
      [else
       `(case (id ,(port-case-id item)) (status available) (context whole-a0)
              (source-type ,source-type)
              (source-typing ,source-witness) (target-typing ,target-witness)
              (term ,output))])))

(define (selected-corpus-cases)
  (define manifest (call-with-input-file case-manifest-path read-json))
  (define ids (hash-ref (hash-ref manifest 'cohorts) 'definition_parity))
  (define wanted (for/hash ([id (in-list ids)]) (values id #t)))
  (define cases
    (for/list ([item (in-list (load-port-corpus))]
               #:when (hash-has-key? wanted (port-case-id item)))
      item))
  (unless (and (pair? ids) (= (length ids) (hash-count wanted))
               (= (length cases) (length ids)))
    (error 'm2-oracle "manifest/corpus join failed: ~a selected, ~a joined"
           (length ids) (length cases)))
  cases)

;; An independent source-only input to the consumer. This phase never reads
;; the candidate oracle, runs candidate-target expansion, or consults any Lean outcome.
(define (source-contract item)
  (with-handlers ([exn:fail:oracle-domain?
                   (lambda (exception)
                     `(case (id ,(port-case-id item)) (status unavailable)
                            (category ,(exn:fail:oracle-domain-category exception))
                            (stage ,(exn:fail:oracle-domain-stage exception))
                            (reason ,(exn-message exception))))])
    (match-define (admitted-source _payload _environment bridge? witness) (prepare-source item))
    `(case (id ,(port-case-id item)) (status typed-source)
           (context ,(if bridge? 'assert-bridge 'whole-a0))
           (source-typing ,(if bridge? (assert-witness witness) witness))
           ,@(if bridge? `((payload-source-typing ,witness)) '()))))

(define (build-source-contracts)
  (define cases (map source-contract (selected-corpus-cases)))
  `(smusni-m2-oracle-sources 2 (count ,(length cases)) (cases ,@cases)))

(define (build-oracle)
  (define cases (map oracle-case (selected-corpus-cases)))
  (unless (ormap (lambda (item) (member '(status available) item)) cases)
    (error 'm2-oracle "typed oracle is empty; refusing vacuous parity"))
  `(smusni-m2-redex-oracle 2 (count ,(length cases)) (cases ,@cases)))

(define (render value)
  (parameterize ([pretty-print-columns 120])
    (call-with-output-string (lambda (out) (pretty-write value out)))))

(module+ main
  (define write? #f)
  (define sources? #f)
  (command-line
   #:program "export_m2_redex_oracle.rkt"
   #:once-each
   [("--sources") "generate source-only typing contracts (no expansion/oracle/Lean input)" (set! sources? #t)]
   [("--write") "write the generated oracle" (set! write? #t)])
  (define generated (if sources? (build-source-contracts) (build-oracle)))
  (define destination (if sources? source-output-path output-path))
  (define result (render generated))
  (cond
    [write?
     (call-with-output-file destination
       (lambda (out) (display result out)) #:exists 'truncate/replace)
     (printf "wrote ~a\n" (find-relative-path root destination))]
    [(not (file-exists? destination))
     (error 'm2-oracle "missing ~a; run --write" destination)]
    [(not (string=? result (file->string destination)))
     (error 'm2-oracle "stale ~a; regenerate with --write" destination)]
    [sources? (printf "M2 independent source contracts: ok\n")]
    [else
     (define cases (match generated [`(,_ ,_ ,_ (cases ,cases ...)) cases]))
     (define available
       (count (lambda (item) (member '(status available) item)) cases))
     (define total (length cases))
     (define bridge (count (lambda (item) (member '(context assert-bridge) item)) cases))
     (printf "M2 Redex oracle: ok cases=~a available=~a whole-a0=~a assert-bridge=~a unavailable=~a\n"
             total available (- available bridge) bridge (- total available))]))

(module+ test
  (require rackunit)
  ;; #83's actual symbolic EFn input, and an unseen alpha/type variant.
  (for ([type '(Entity Eventuality)] [name '($p $unseen)])
    (check-exn #rx"EFn"
      (lambda ()
        (expand-term `(CoveredBy ,name $r)
                     `((,name (EFn (,type) Content)) ($r (Referents ,type)))))))
  (define actual-control
    (findf (lambda (item)
             (equal? (port-case-id item) "2a00f8ca5df0ba140dbe29fa18c0acda9b274913"))
           (load-port-corpus)))
  (check-not-false actual-control "the transported actual #83 control must remain present")
  (check-not-false (member '(status unavailable) (oracle-case actual-control)))
  (define unseen-control
    (port-case "unseen-effectful-member" 'test
      '(λ (($q :: EFn (Eventuality) Content) ($events :: Referents Eventuality))
         (CoveredBy $q $events)) '() '()))
  (check-not-false (member '(status unavailable) (oracle-case unseen-control)))
  (define pure-control
    (port-case "unseen-pure-member" 'test
      '(CoveredBy $q $events)
      '(( $q Fn (Eventuality) Content) ($events Referents Eventuality)) '()))
  (check-not-false (member '(status available) (oracle-case pure-control)))

  (define (probe source [environment '()] #:expand [expander expand-term])
    (oracle-case (port-case "mechanism-control" 'test source environment '())
                 #:expand expander))
  (define (get record key) (second (assoc key (cdr record))))
  ;; F01-A2: actual producer boundaries, not a case-ID classification patch.
  ;; Source-only contracts must retain the same independently obtained reason.
  (define source-env '(($S RefComp (Referents Entity))
                       ($P Fn ((Referents Entity)) Content)))
  (define (source-form x read occurrence [source '$S] [content #f] [continuation #f])
    `(PerformSource Host (,x :: Referents Entity) ,source
       (Assert ,(or content `($P ,x)))
       (,read :: RefComp (Referents Entity)) (,occurrence :: ActOccurrence Assertion)
       ,(or continuation
            `(Let ($saved :: ActOccurrence Assertion) ,occurrence
               (Do (Perform Host (Assert (Bind ($y :: Referents Entity) ,read ($P $y)))))))))
  (define (source-boundary! term env category stage reason-pattern)
    (define item (port-case "source-boundary-control" 'test term env '()))
    (define oracle (oracle-case item #:expand (lambda _ (error "unsupported source reached expansion"))))
    (define contract (source-contract item))
    (for ([record (list oracle contract)])
      (check-equal? (get record 'status) 'unavailable)
      (check-equal? (get record 'category) category)
      (check-equal? (get record 'stage) stage)
      (check-regexp-match reason-pattern (get record 'reason))
      (check-false (assoc 'term (cdr record))))
    (check-equal? contract oracle))
  (for ([names '(($x $read $o) ($fresh $again $token))])
    (match-define (list x read occurrence) names)
    (define valid (source-form x read occurrence))
    (source-boundary! valid source-env 'context-unsupported 'context #rx"PerformSource")
    (source-boundary! (cons 'PerformSource (cddr valid)) source-env
                      'context-unsupported 'context #rx"PerformSource")
    (for ([illegal (list x read occurrence)])
      (source-boundary! (source-form x read occurrence illegal) source-env
                        'malformed-input 'environment #rx"missing declaration"))
    (for ([illegal (list read occurrence)])
      (source-boundary! (source-form x read occurrence '$S `($P ,illegal)) source-env
                        'malformed-input 'environment #rx"missing declaration"))
    (source-boundary! (source-form x read occurrence '$S #f `(Do (Assert ($P ,x)))) source-env
                      'malformed-input 'environment #rx"missing declaration")
    (source-boundary! (source-form x read occurrence '$missing) source-env
                      'malformed-input 'environment #rx"missing declaration")
    ;; Existing outer declarations remain accessible without leaking the
    ;; newly introduced first-arm binder into S or D.
    (source-boundary! (source-form x read occurrence x)
                      (cons `(,x RefComp (Referents Entity)) source-env)
                      'context-unsupported 'context #rx"PerformSource")
    (source-boundary! (source-form x read occurrence '$S #f `(Do (Assert ($P ,x))))
                      (cons `(,x Referents Entity) source-env)
                      'context-unsupported 'context #rx"PerformSource"))
  (define source-number
    (source-contract (port-case "source-only-control" 'test '$number '(($number . Number)) '())))
  (define source-natural
    (source-contract (port-case "source-only-control" 'test '$number '(($number . Natural)) '())))
  (check-equal? (get source-number 'source-typing) '(typing Number () ()))
  (check-equal? (get source-natural 'source-typing) '(typing Natural () ()))
  (define (replace record key value)
    (cons (car record)
          (for/list ([entry (cdr record)])
            (if (eq? (car entry) key) (list key value) entry))))
  (define (unavailable! source [environment '()] [category #f])
    (define result (probe source environment))
    (check-equal? (get result 'status) 'unavailable (format "~e" source))
    (when category (check-equal? (get result 'category) category))
    (check-false (assoc 'term (cdr result)))
    (void))
  (define close-payload '(CloseWith (row klama 5 direct-event (1 2 3 4 5)) ((1 Speaker))))
  (define positive (probe `(Assert ,close-payload)))
  (check-equal? (get positive 'status) 'available)
  (check-equal? (get positive 'context) 'assert-bridge)
  (check-equal? (get positive 'source-type) '(Act Assertion))
  (check-equal? (car (get positive 'term)) 'Assert)
  (check-equal? (second (get positive 'payload-source-typing)) 'Content)
  (check-equal? (second (get positive 'payload-target-typing)) 'Content)
  (check-true (validate-assert-certificate positive
               (get positive 'payload-source-typing) (get positive 'payload-target-typing)))
  (check-exn #rx"wrapper/type/obligation"
    (lambda ()
      (validate-assert-certificate
       (replace positive 'term (second (get positive 'term)))
       (get positive 'payload-source-typing) (get positive 'payload-target-typing))))

  (define projective (probe `(Assert (Presuppose (= 1 1) ,close-payload))))
  (check-equal? (get projective 'status) 'available)
  (for ([act-key '(source-typing target-typing)]
        [payload-key '(payload-source-typing payload-target-typing)])
    (define act (get projective act-key))
    (define payload (get projective payload-key))
    (check-equal? (third act) '())
    (check-not-false (member 'projective (third payload)))
    (check-true (pair? (fourth payload)))
    (check-equal? (fourth act) (fourth payload))
    (check-exn #rx"wrapper/type/obligation"
      (lambda ()
        (validate-assert-certificate
         (replace projective act-key '(typing (Act Assertion) () ()))
         (get projective 'payload-source-typing) (get projective 'payload-target-typing)))))

  (for ([payload (list 3 'Speaker '(StateClause ⊤) `(Assert ,close-payload))])
    (unavailable! `(Assert ,payload) '() 'type/domain-rejected))
  (unavailable! '(Assert) '() 'malformed-input)
  (unavailable! '(Assert ⊤ ⊤) '() 'malformed-input)
  (for ([source (list `(Express ,close-payload) '(Mention Speaker)
                     `(Ask (Polar ,close-payload)) `(Polar ,close-payload)
                     `(SentenceSign ,close-payload)
                     `(Let ($a :: Act Assertion) (Assert ,close-payload) (Do (Perform $a)))
                     `(Bind ($a :: ActOccurrence Assertion) (Perform (Assert ,close-payload))
                        (Do (Mention $a)))
                     `(Do (Assert ,close-payload))
                     `(Assert (Reify ,close-payload)))])
    (unavailable! source '() 'context-unsupported))

  ;; These variants test the actual A0 pure arrow/construction-effect domain,
  ;; not just the symbolic diagnostic shortcut in the expansion dispatcher.
  (for ([type '(Entity Eventuality)] [p '($p $new-member)])
    (unavailable! `(Assert (CoveredBy ,p $r))
                  `((,p EFn (,type) Content) ($r Referents ,type))))
  (unavailable!
   '(Assert (CoveredBy (λ ($x :: Entity) (Bind ($y :: Entity) (Context) ⊤)) Speaker)))
  (unavailable!
   '(Assert (CoveredBy
      (Bind ($y :: Entity) (Context) (λ ($x :: Entity) ⊤)) Speaker)))
  (unavailable! '(Assert (CoveredBy $p Speaker)) '(( $p Fn (Number) Content)))
  (define gq-environment '(( $p Fn (Entity) Content) ($q Fn ((Referents Entity)) Content)))
  (check-equal? (get (probe '(Some $p $q) gq-environment) 'status) 'available)
  (unavailable! '(Assert (= (Card (SetOf (λ ($x :: Entity) (Some $p $q)))) 1))
                gq-environment)
  (check-equal? (get (probe `(Assert ,close-payload) '()
                            #:expand (lambda (datum environment) datum)) 'status) 'unavailable)
  (check-equal?
   (get (probe `(Assert ,close-payload)
               '(( $bad EFn (Entity) Content))
               #:expand (lambda (_ env) (expand-term '(CoveredBy $bad Speaker) env)))
        'category)
   'type/domain-rejected)
  ;; Unexpected implementation exceptions must not become unavailable cases.
  (check-exn #rx"injected implementation failure"
    (lambda () (probe `(Assert ,close-payload) '()
                       #:expand (lambda (_ _env) (error "injected implementation failure")))))
  (unavailable! '(Assert (CloseWith (row nonexistent 1 holding-state (1)) ((1 Speaker))))
                '() 'malformed-input)
  (unavailable! '(Assert (CloseWith (row klama 1 holding-state (1)) ((1 Speaker))))
                '() 'malformed-input)
  (unavailable! `(Assert ,close-payload) '((klama Fn (Entity) Content)) 'malformed-input)
  (unavailable! '(Assert (CoveredBy $missing Speaker)) '() 'malformed-input)
  (unavailable! `(Assert ,close-payload) '(broken-entry) 'malformed-input)
  (unavailable! '(Assert (AtLeast $n $p $q))
                (cons '($n . Natural) gq-environment) 'expansion-domain-unavailable)
  (check-equal? (get (probe '(Assert (AtLeast (+ $n 1) $p $q))
                            (cons '($n . Natural) gq-environment)) 'status) 'available)
  (unavailable! '(Assert (Exactly (+ 3 1) $p $q)) gq-environment 'expansion-domain-unavailable)
  (unavailable! '(Assert (ZipWith $f (List Speaker) (List Speaker Audience)))
                '(( $f Fn ((Referents Entity) (Referents Entity)) Content))
                'expansion-domain-unavailable))
