#lang racket

(require (for-syntax racket/base)
         redex/reduction-semantics)

(provide define-definition-metafunction
         define-definition-relation)

;; These wrappers make the ledger's case ids structural: every id encloses the
;; actual Redex clause/rule it names. Raw comments or a detached registry cannot
;; satisfy the source gate.
(define-syntax (define-definition-metafunction stx)
  (syntax-case stx (: -> definition-case)
    [(_ language name : domain -> range
        (definition-case _case-id clause) ...)
     #'(define-metafunction language
         name : domain -> range
         clause ...)]))

(define-syntax (define-definition-relation stx)
  (syntax-case stx (definition-case)
    [(_ name language domain
        (definition-case _case-id rule) ...)
     #'(define name
         (reduction-relation language #:domain domain rule ...))]))
