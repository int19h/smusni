#lang racket

(require json
         racket/cmdline
         racket/file
         racket/list
         racket/match
         racket/pretty
         redex/reduction-semantics
         "../../tools/smusni-redex/inventory.rkt"
         "../../tools/smusni-redex/port-a0.rkt"
         "../../tools/smusni-redex/port-phase0.rkt")

(define root (simplify-path (build-path (current-directory))))
(define case-manifest-path (build-path root "pilot/shared/M2_CASE_MANIFEST.json"))
(define output-path (build-path root "pilot/shared/M2_REDEX_ORACLE.sexp"))

(struct exn:fail:oracle-domain exn:fail ())
(define (domain-unavailable format-string . arguments)
  (raise (exn:fail:oracle-domain
          (apply format format-string arguments) (current-continuation-marks))))

(define (port-environment entries)
  (for/list ([entry (in-list entries)])
    (match entry
      [(cons variable type) (list variable type)])))

;; The A0 judgment consumes lexical function declarations, not fixture names.
;; This mirrors the frozen port adapter's row input, using actual declared row
;; arity/event mode. Explicit case bindings retain priority. No output values
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
     (cons (declaration predicate arity event-mode) (row-environment fills))]
    [`(,(? symbol? predicate) ,arguments ...)
     (define row (inventory-row inventory predicate))
     (append (if row
                 (list (declaration predicate (row-decl-total row) (row-decl-event-mode row)))
                 '())
             (append-map row-environment arguments))]
    [(? list?) (append-map row-environment datum)]
    [_ '()]))

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

(define (contains-member-refer? datum)
  (match datum
    [`(Refer (λ ((,_ ,type)) ,_))
     (not (match type [`(Referents ,_) #t] [_ #f]))]
    [(? list?) (ormap contains-member-refer? datum)]
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

(define (instantiate-plural-dependencies datum type)
  (match datum
    [`(Distrib ,property ,reference)
     (instantiate-plural-dependencies
      (term (b1-expand-distrib ,type ,property ,reference)) type)]
    [`(Overlap ,first ,second)
     (instantiate-plural-dependencies
      (term (b1-expand-overlap ,type ,first ,second)) type)]
    [(? list?) (map (lambda (child) (instantiate-plural-dependencies child type)) datum)]
    [_ datum]))

(define (expand-term datum environment)
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
     (again (instantiate-plural-dependencies
             (term (b1-expand-covered-by ,type ,property ,reference)) type))]
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

(define (oracle-case item)
  (with-handlers ([exn:fail:oracle-domain?
                   (lambda (exception)
                     `(case (id ,(port-case-id item))
                            (status unavailable)
                            (reason ,(exn-message exception))))])
    (define input (legacy-datum->a0 (port-case-term item)))
    (define environment
      (remove-duplicates (append (port-environment (port-case-env item))
                                 (row-environment input))))
    (unless (and (redex-match? SmusniA0 Γ environment)
                 (redex-match? SmusniA0 t input))
      (domain-unavailable "outside frozen A0 source grammar: ~e" input))
    (when (contains-member-refer? input)
      (domain-unavailable
             "Refer-member-lift has ledger port-state none; term oracle unavailable"))
    ;; The metafunctions are untyped. A generated RHS alone is not an oracle:
    ;; both ends must inhabit the independently maintained Redex judgment.
    ;; Report the precise boundary; never ask Lean whether to publish a target.
    (define source-typings (judgment-holds (a0-synth ,environment ,input R) R))
    (unless (= (length source-typings) 1)
      (domain-unavailable "source has ~a admitted A0 typings: ~e"
                          (length source-typings) input))
    (define expanded (expand-term input environment))
    (define output-environment
      (remove-duplicates (append environment (row-environment expanded))))
    (unless (and (redex-match? SmusniA0 Γ output-environment)
                 (redex-match? SmusniA0 t expanded))
      (domain-unavailable "outside frozen A0 target grammar: ~e" expanded))
    (define source-type (second (first source-typings)))
    (define target-typings
      (judgment-holds (a0-check ,output-environment ,expanded ,source-type R) R))
    (unless (= (length target-typings) 1)
      (domain-unavailable "expanded target has ~a A0 typings at source type ~e"
             (length target-typings) source-type))
    (define output (a0->surface expanded))
    `(case (id ,(port-case-id item)) (status available)
           (source-type ,source-type) (term ,output))))

(define (build-oracle)
  (define manifest (call-with-input-file case-manifest-path read-json))
  (define ids (hash-ref (hash-ref manifest 'cohorts) 'definition_parity))
  (define wanted (for/hash ([id (in-list ids)]) (values id #t)))
  (define cases
    (for/list ([item (in-list (load-port-corpus))]
               #:when (hash-has-key? wanted (port-case-id item)))
      (oracle-case item)))
  (unless (and (pair? ids) (= (length ids) (hash-count wanted))
               (= (length cases) (length ids)))
    (error 'm2-oracle "manifest/corpus join failed: ~a selected, ~a joined"
           (length ids) (length cases)))
  (unless (ormap (lambda (item) (member '(status available) item)) cases)
    (error 'm2-oracle "typed oracle is empty; refusing vacuous parity"))
  `(smusni-m2-redex-oracle 1 (count ,(length cases)) (cases ,@cases)))

(define (render value)
  (parameterize ([pretty-print-columns 120])
    (call-with-output-string (lambda (out) (pretty-write value out)))))

(module+ main
  (define write? #f)
  (command-line
   #:program "export_m2_redex_oracle.rkt"
   #:once-each
   [("--write") "write the generated oracle" (set! write? #t)])
  (define result (render (build-oracle)))
  (cond
    [write?
     (call-with-output-file output-path
       (lambda (out) (display result out)) #:exists 'truncate/replace)
     (printf "wrote ~a\n" (find-relative-path root output-path))]
    [(not (file-exists? output-path))
     (error 'm2-oracle "missing ~a; run --write" output-path)]
    [(not (string=? result (file->string output-path)))
     (error 'm2-oracle "stale ~a; regenerate with --write" output-path)]
    [else
     (define available
       (count (lambda (item) (member '(status available) item))
              (match (build-oracle) [`(,_ ,_ ,_ (cases ,cases ...)) cases])))
     (define total (match (build-oracle) [`(,_ ,_ (count ,n) ,_) n]))
     (printf "M2 Redex oracle: ok cases=~a available=~a unavailable=~a\n"
             total available (- total available))]))

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
             (equal? (port-case-id item) "9179373ca8c2e48ede6fe47086cebd79b7f61352"))
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
  (check-not-false (member '(status available) (oracle-case pure-control))))
