#lang racket

(require rackunit racket/list racket/set redex/reduction-semantics
         "../syntax.rkt" "../types.rkt" "../elaborate.rkt" "../lower.rkt"
         "../port-a0.rkt" "../port-phase0.rkt" "../port-b2-spike.rkt")

(define R '(Referents Entity))
(define env (hash '$S `(RefComp ,R) '$P `(Fn (,R) Content)
                  '$Q `(Fn (,R) Content) '$D 'Discourse))
(define (source-form [source '$S] [content '($P $x)]
                     [continuation '(Do (Perform Host (Assert (Bind ($y :: Referents Entity) $read ($Q $y)))))]
                     #:x [x '$x] #:read [r '$read] #:occurrence [o '$o]
                     #:role [role '(Host)])
  `(PerformSource ,@role (,x :: Referents Entity) ,source (Assert ,content)
                  (,r :: RefComp (Referents Entity)) (,o :: ActOccurrence Assertion)
                  ,continuation))
(define (ast term) (read-core-specimen (format "~s" term)))
(define (infer term [environment env]) (infer-core (ast term) environment))
(define (reject term [environment env])
  (check-exn exn:fail? (lambda () (infer term environment))))

;; General parameters, not a sample classifier or canned source result.
(for ([role (in-list '((Host) ()))])
  (define term (source-form #:role role))
  (define result (infer term))
  (check-equal? (typing-type result) 'Discourse)
  (check-true (set-member? (typing-effects result) 'performance))
  (check-equal? (typing-gaps result) '()))
(check-equal? (typing-type (infer (source-form '(Refer $P)))) 'Discourse)
(check-equal? (typing-type (infer (source-form '$S '($P $x) '$D))) 'Discourse)
(reject (source-form #:role '(AttachedDisplay)))
(reject (source-form #:role '(17)))
(reject (source-form 'Speaker))
(reject (source-form '$S 'Speaker))
(reject (source-form '$S '($P $x) '($Q Speaker)))
(reject (source-form '$S '($P $x) '(Assert ($Q Speaker))))
(reject (source-form '$unknown))
(reject (source-form '$S '$unknown))
(reject (source-form '$S '($P $x) '$unknown))
(match-define (list 'PerformSource 'Host b s a r o d) (source-form))
(for ([bad (in-list (list
                    `(PerformSource Host ,b ,s (Ask ($P $x)) ,r ,o ,d)
                    `(PerformSource Host ,b ,s (Assert ($P $x) ($P $x)) ,r ,o ,d)
                    `(PerformSource Host ,b ,s ,a ,r ,o)
                    `(PerformSource Host ,b ,s ,a ,r ,o ,d ,d)
                    `(PerformSource Host ($x :: Entity) ,s ,a ,r ,o ,d)
                    `(PerformSource Host ,b ,s ,a ($read :: RefComp Entity) ,o ,d)
                    `(PerformSource Host ,b ,s ,a ,r ($o :: ActOccurrence Question) ,d)
                    `(PerformSource Host ,b ,s ,a ($o :: RefComp (Referents Entity)) ,o ,d)
                    `(PerformSource Host ($x $z :: Referents Entity) ,s ,a ,r ,o ,d)))])
  (reject bad))

;; Each arm's names are genuinely lexical: no new source binders in S,
;; only x in C1, only read/o in D. An outer spelling remains accessible.
(for ([name '($x $read $o)]) (reject (source-form name)))
(for ([name '($x $read $o)]) (reject (source-form `(Context ,name))))
(for ([name '($read $o)]) (reject (source-form '$S name)))
(for ([name '($read $o)])
  (reject (source-form '$S `(Bind ($z :: Referents Entity) (Context ,name) ($P $z)))))
(reject (source-form '$S '($P $x) '(Do (Perform (Assert ($Q $x))))))
(check-equal? (typing-type
               (infer (source-form '$x '($P $x) '$D)
                      (hash-set env '$x `(RefComp ,R)))) 'Discourse)
(check-equal? (typing-type
               (infer (source-form '$S '($P $read) '$D)
                      (hash-set env '$read R))) 'Discourse)
(check-equal? (typing-type
               (infer (source-form '$S '($P $x) '(Do (Perform (Assert ($Q $x)))))
                      (hash-set env '$x R))) 'Discourse)
(check-equal? (typing-type
               (infer (source-form '$S '($P $x) (source-form '$read)))) 'Discourse)

;; The ordinary Perform role check accepts declared roles, rejects wrong types.
(reject '(Perform 3 (Assert ($P Speaker))))
(reject '(Perform $unknown (Assert ($P Speaker))))
(check-equal? (typing-type (infer '(Perform AttachedDisplay (Assert ($P Speaker)))))
              '(PerfComp (ActOccurrence Assertion)))

(define (adapter term) (core-redex-adapter-term (core->redex-adapter (ast term))))
(check-true (alpha-equivalent? SmusniCore (adapter (source-form))
                              (adapter (source-form '$S '($P $a)
                                '(Do (Perform Host (Assert (Bind ($z :: Referents Entity) $v ($Q $z)))))
                                #:x '$a #:read '$v #:occurrence '$u #:role '()))))
(check-equal? (adapter (source-form #:role '())) (adapter (source-form)))
(check-equal? (free-core-variables (adapter (source-form))) (set '$S '$P '$Q))
(define grouped (adapter (source-form '$S '$x '(Do $read $o))))
(define-values (opaque node-count) (b2-compile-term grouped))
(check-equal? (b2-node->datum opaque) grouped)
(check-equal? node-count (b2-raw-occurrence-count grouped))
(check-eq? (b2-node-binding (b2-node-at-path opaque '(1 0)))
           (b2-node-binding (b2-node-at-path opaque '(3))))
(check-eq? (b2-node-binding (b2-node-at-path opaque '(4 0)))
           (b2-node-binding (b2-node-at-path opaque '(6 1))))
(check-eq? (b2-node-binding (b2-node-at-path opaque '(5 0)))
           (b2-node-binding (b2-node-at-path opaque '(6 2))))
(check-false (b2-node-binding (b2-node-at-path opaque '(2))))
(check-equal? (term (introducing? ,grouped)) #t)
(define substituted (substitute-free-symbol (source-form) '$P '$x))
(check-true (set-member? (free-core-variables (adapter substituted)) '$x))
(check-false (equal? substituted (source-form '$S '($x $x))))
(check-equal? (substitute-free-symbol (source-form) '$read '$fresh) (source-form))
(define with-sites
  (source-form '(Context $S)
               '(Bind ($z :: Referents Entity) (Context $x) ($P $z))
               '(Do (Perform (Assert (Bind ($y :: Referents Entity) (Vague $read) ($Q $y)))))))
(check-equal? (map third (site-signatures with-sites)) '(Context Context Vague))
(check-equal? (site-signatures with-sites)
              (site-signatures (substitute-free-symbol with-sites '$S '$fresh)))
(define elaborated (elaborate-core (ast with-sites)))
(match-define (list _ _ _ _ (list 'Assert actual-content) _ _ _)
  (core->plain-datum (elaboration-ast elaborated)))
(check-equal? actual-content '(Bind ($z :: Referents Entity) (Context $x) ($P $z)))
(check-equal? (map site-id-kind (elaboration-sites elaborated)) '(Context Context Vague))
(check-equal? (core->plain-datum (elaboration-ast (elaborate-core (ast (source-form '$S '($P $x) '$D)))))
              (source-form '$S '($P $x) '$D))
(define inert-nested-act
  (source-form '$S '(Let ($a :: Act Assertion) (Assert ($P $x)) (ActContent $a)) '$D))
(check-equal? (core->plain-datum (elaboration-ast (elaborate-core (ast inert-nested-act))))
              inert-nested-act)

;; PerformSource has no strict-Bind expansion, and the previous successful
;; multi-source route still binds both referents across its one first Host.
(check-equal? (car (adapter (source-form))) 'PerformSource)
(check-equal?
 (typing-type (infer '(Bind ($x :: Referents Entity) $S
                           ($y :: Referents Entity) $S
                       (Do (Perform (Assert ($P $x))) (Perform (Assert ($Q $y)))))))
 'Discourse)
