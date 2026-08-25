#lang racket

(require racket/list
         racket/match
         racket/port
         redex/reduction-semantics)

(provide (struct-out core-atom)
         (struct-out core-list)
         read-core-forms
         read-core-specimen
         core->datum
         validate-core-form
         SmusniSurface)

(struct core-atom (value source line column position span) #:transparent)
(struct core-list (shape elements source line column position span) #:transparent)

(define-language SmusniSurface
  [shape paren brace bracket]
  [atom variable-not-otherwise-mentioned natural string]
  [term atom (node shape term ...)])

(define (syntax-location stx)
  (values (syntax-source stx)
          (syntax-line stx)
          (syntax-column stx)
          (syntax-position stx)
          (syntax-span stx)))

(define (shape-of stx)
  (case (syntax-property stx 'paren-shape)
    [(#\{) 'brace]
    [(#\[) 'bracket]
    [else 'paren]))

(define (syntax->core stx)
  (define-values (source line column position span) (syntax-location stx))
  (define elements (syntax->list stx))
  (if elements
      (core-list (shape-of stx)
                 (map syntax->core elements)
                 source line column position span)
      (core-atom (syntax-e stx) source line column position span)))

(define (read-core-forms input [source-name 'smusni])
  (define in (if (input-port? input) input (open-input-string input)))
  (port-count-lines! in)
  (let loop ([forms '()])
    (define stx (read-syntax source-name in))
    (if (eof-object? stx)
        (reverse forms)
        (loop (cons (syntax->core stx) forms)))))

(define (node-symbol? node symbol)
  (and (core-atom? node) (eq? (core-atom-value node) symbol)))

(define (raise-shape who node expected)
  (error who "expected ~a punctuation at ~a:~a, got ~a"
         expected (core-list-line node) (core-list-column node)
         (core-list-shape node)))

(define (require-shape who node expected)
  (unless (and (core-list? node) (eq? (core-list-shape node) expected))
    (if (core-list? node)
        (raise-shape who node expected)
        (error who "expected ~a-delimited form, got ~e" expected node))))

(define (validate-binder who binder)
  (require-shape who binder 'brace)
  (define elems (core-list-elements binder))
  (unless (and (>= (length elems) 3)
               (node-symbol? (list-ref elems (- (length elems) 2)) '::))
    (error who "malformed typed binder group at ~a:~a"
           (core-list-line binder) (core-list-column binder))))

(define (validate-direct-binder form)
  (define elems (core-list-elements form))
  (define head (core-atom-value (first elems)))
  (case head
    [(λ)
     (unless (= (length elems) 3)
       (error 'validate-core-form "λ requires a telescope and one body"))
     (require-shape 'validate-core-form (second elems) 'brace)
     (require-shape 'validate-core-form (third elems) 'brace)]
    [(Let)
     (unless (= (length elems) 4)
       (error 'validate-core-form "Let requires binder, value, and body"))
     (validate-binder 'validate-core-form (second elems))
     (require-shape 'validate-core-form (fourth elems) 'brace)]
    [(Bind)
     (unless (and (>= (length elems) 4) (even? (length elems)))
       (error 'validate-core-form
              "Bind requires alternating binder/computation pairs and one body"))
     (define tail (rest elems))
     (define body (last tail))
     (require-shape 'validate-core-form body 'brace)
     (define pairs (drop-right tail 1))
     (for ([index (in-range 0 (length pairs) 2)])
       (validate-binder 'validate-core-form (list-ref pairs index)))]))

(define (validate-core-form form)
  (cond
    [(core-atom? form) (void)]
    [else
     (define elems (core-list-elements form))
     (when (and (eq? (core-list-shape form) 'paren)
                (pair? elems)
                (core-atom? (first elems))
                (member (core-atom-value (first elems)) '(λ Let Bind)))
       (validate-direct-binder form))
     (for ([element (in-list elems)]) (validate-core-form element))]))

(define (read-core-specimen input [source-name 'smusni])
  (define forms (read-core-forms input source-name))
  (unless (= (length forms) 1)
    (error 'read-core-specimen "expected exactly one term, got ~a" (length forms)))
  (define form (first forms))
  (require-shape 'read-core-specimen form 'paren)
  (validate-core-form form)
  form)

(define (core->datum form)
  (match form
    [(core-atom value _ _ _ _ _) value]
    [(core-list shape elements _ _ _ _ _)
     `(node ,shape ,@(map core->datum elements))]))

