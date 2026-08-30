#lang racket

(require json
         racket/cmdline
         racket/file
         racket/list
         racket/match
         racket/pretty
         redex/reduction-semantics
         "../../tools/smusni-redex/port-a0.rkt"
         "../../tools/smusni-redex/port-phase0.rkt")

(define root (simplify-path (build-path (current-directory))))
(define case-manifest-path (build-path root "pilot/shared/M2_CASE_MANIFEST.json"))
(define output-path (build-path root "pilot/shared/M2_REDEX_ORACLE.sexp"))

(define (port-environment entries)
  (for/list ([entry (in-list entries)])
    (match entry
      [(cons variable type) (list variable type)])))

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
    [_ (error 'm2-oracle "cannot infer GunmaAt basis type for ~e" basis)]))

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
    [_ (error 'm2-oracle "cannot infer CompleteGunmaAt basis type for ~e" basis)]))

(define (expand-term datum environment)
  (define (again value [env environment]) (expand-term value env))
  (match datum
    ['⊤ '(∧)]
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
     (unless type (error 'm2-oracle "Exactly member type unavailable"))
     (again (term (a0-expand-exactly ,count ,type ,property ,nuclear)))]
    [`(AtLeast ,count ,property ,nuclear)
     (define type (member-type property environment))
     (unless type (error 'm2-oracle "AtLeast member type unavailable"))
     (define outputs (term (b1-expand-at-least ,count ,type ,property ,nuclear)))
     (if (equal? outputs `(b1-expand-at-least ,count ,type ,property ,nuclear))
         (error 'm2-oracle "AtLeast domain has no Redex expansion")
         (again outputs))]
    [`(Some ,property ,nuclear)
     (define type (member-type property environment))
     (unless type (error 'm2-oracle "Some member type unavailable"))
     (again (term (b1-expand-some ,type ,property ,nuclear)))]
    [`(Every ,property ,nuclear)
     (define type (member-type property environment))
     (unless type (error 'm2-oracle "Every member type unavailable"))
     (again (term (b1-expand-every ,type ,property ,nuclear)))]
    [`(No ,property ,nuclear)
     (define type (member-type property environment))
     (unless type (error 'm2-oracle "No member type unavailable"))
     (again (term (b1-expand-no ,type ,property ,nuclear)))]
    [`(AtMost ,count ,property ,nuclear)
     (define type (member-type property environment))
     (unless type (error 'm2-oracle "AtMost member type unavailable"))
     (again (term (b1-expand-at-most ,count ,type ,property ,nuclear)))]
    [`(MoreThan ,count ,property ,nuclear)
     (define type (member-type property environment))
     (unless type (error 'm2-oracle "MoreThan member type unavailable"))
     (again (term (b1-expand-more-than ,count ,type ,property ,nuclear)))]
    [`(FewerThan ,count ,property ,nuclear)
     (define type (member-type property environment))
     (unless type (error 'm2-oracle "FewerThan member type unavailable"))
     (again (term (b1-expand-fewer-than ,count ,type ,property ,nuclear)))]
    [`(GlobalExactly ,count ,property ,nuclear)
     (define type (member-type property environment))
     (unless type (error 'm2-oracle "GlobalExactly member type unavailable"))
     (again (term (a0-expand-global-exactly ,count ,type ,property ,nuclear)))]
    [`(Distrib ,property ,reference)
     (define type (or (reference-member reference environment)
                      (member-type property environment)))
     (unless type (error 'm2-oracle "Distrib member type unavailable"))
     (again (term (b1-expand-distrib ,type ,property ,reference)))]
    [`(Overlap ,first ,second)
     (define type (or (reference-member first environment)
                      (reference-member second environment)))
     (unless type (error 'm2-oracle "Overlap member type unavailable"))
     (again (term (b1-expand-overlap ,type ,first ,second)))]
    [`(CoveredBy ,property ,reference)
     (define type (or (member-type property environment)
                      (reference-member reference environment)))
     (unless type (error 'm2-oracle "CoveredBy member type unavailable"))
     (again (term (b1-expand-covered-by ,type ,property ,reference)))]
    [`(SelectSome ,property)
     (define type (member-type property environment))
     (unless type (error 'm2-oracle "SelectSome member type unavailable"))
     (again (term (b1-expand-select-some ,type ,property)))]
    [`(MaxRefer ,property)
     (define type (member-type property environment))
     (unless type (error 'm2-oracle "MaxRefer member type unavailable"))
     (again (term (b1-expand-max-refer ,type ,property)))]
    [`(TooMany ,property ,nuclear)
     (define type (member-type property environment))
     (unless type (error 'm2-oracle "TooMany member type unavailable"))
     (again (term (a0-expand-too-many ,type ,property ,nuclear)))]
    [`(Massify ,basis ,cover)
     (match (basis-types basis environment)
       [(list `(Group ,type) component)
        (unless (equal? type component) (error 'm2-oracle "Massify basis mismatch"))
        (again (term (a0-expand-massify ,type ,basis ,cover)))]
       [_ (error 'm2-oracle "Massify basis type unavailable")])]
    [`(ZipWith ,function ,left ,right)
     (define output (term (a0-expand-zipwith ,function ,left ,right)))
     (if (equal? output `(a0-expand-zipwith ,function ,left ,right))
         (error 'm2-oracle "ZipWith unequal-length domain")
         (again output))]
    [`(CloseWith ,row ,fills)
     (define output (term (a0-expand-close ,row ,fills)))
     (if (equal? output `(a0-expand-close ,row ,fills))
         (error 'm2-oracle "Close row domain unavailable")
         (again output))]
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
  (with-handlers ([exn:fail?
                   (lambda (exception)
                     `(case (id ,(port-case-id item))
                            (status unavailable)
                            (reason ,(exn-message exception))))])
    (define environment (port-environment (port-case-env item)))
    (define input (legacy-datum->a0 (port-case-term item)))
    (define output (a0->surface (expand-term input environment)))
    `(case (id ,(port-case-id item)) (status available) (term ,output))))

(define (build-oracle)
  (define manifest (call-with-input-file case-manifest-path read-json))
  (define ids (hash-ref (hash-ref manifest 'cohorts) 'definition_parity))
  (define wanted (for/hash ([id (in-list ids)]) (values id #t)))
  (define cases
    (for/list ([item (in-list (load-port-corpus))]
               #:when (hash-has-key? wanted (port-case-id item)))
      (oracle-case item)))
  (unless (= (length cases) 160)
    (error 'm2-oracle "expected 160 cases, got ~a" (length cases)))
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
     (printf "M2 Redex oracle: ok cases=160 available=~a unavailable=~a\n"
             available (- 160 available))]))
