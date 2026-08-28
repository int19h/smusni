#lang racket

(require (for-syntax racket/base racket/list)
         redex/reduction-semantics)

(provide define-definition-metafunction
         define-definition-relation)

;; These wrappers make the ledger's case ids structural: every id encloses the
;; actual Redex clause/rule it names. Raw comments or a detached registry cannot
;; satisfy the source gate.
(define-syntax (define-definition-metafunction stx)
  (define parts (rest (syntax->list stx)))
  (define (case-form? part)
    (define items (syntax->list part))
    (and items (= (length items) 3)
         (eq? (syntax-e (first items)) 'definition-case)))
  (define prefix (filter (lambda (part) (not (case-form? part))) parts))
  (define clauses
    (for/list ([part (in-list parts)] #:when (case-form? part))
      (third (syntax->list part))))
  #`(define-metafunction #,@prefix #,@clauses))

(define-syntax (define-definition-relation stx)
  (syntax-case stx (definition-case)
    [(_ name language domain
        (definition-case _case-id rule) ...)
     #'(define name
         (reduction-relation language #:domain domain rule ...))]))

(module+ test
  (define-language NestedStructuralToy [n natural])
  (define-definition-metafunction NestedStructuralToy
    nested-test-only : n -> n
    (definition-case nested [(nested-test-only n) n])))
