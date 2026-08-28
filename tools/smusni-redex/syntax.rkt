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
         core->plain-datum
         core->redex-adapter
         redex-adapter->core
         validate-core-form
         SmusniSurface
         SmusniCore
         (struct-out core-redex-adapter))

(struct core-atom (value source line column position span) #:transparent)
(struct core-list (elements source line column position span) #:transparent)
(struct core-redex-adapter (term original) #:transparent)

(define-language SmusniSurface
  [atom variable-not-otherwise-mentioned natural string]
  [term atom (node term ...)])

;; Canonical derived representation for Redex binding-aware comparison. The
;; concrete reader retains the document's flat binder notation; M3 translates
;; it to this grouped shape before calling `alpha-equivalent?`.
(define-language SmusniCore
  [x variable-not-otherwise-mentioned]
  [τ any]
  [a variable-not-otherwise-mentioned natural string]
  [t a
     (λ ((x τ) ...) t)
     (Let (x τ) t t)
     (Bind ((x τ t) ...) t)
     (t t ...)]
  #:binding-forms
  (λ ((x τ) ...) t #:refers-to (shadow x ...))
  (Let (x τ) t_rhs t_body #:refers-to x)
  (Bind ((x τ t_rhs) #:...bind (clauses x (shadow clauses x)))
        t_body #:refers-to clauses))

(define (syntax-location stx)
  (values (syntax-source stx)
          (syntax-line stx)
          (syntax-column stx)
          (syntax-position stx)
          (syntax-span stx)))

(define (syntax->core stx)
  (define-values (source line column position span) (syntax-location stx))
  (define elements (syntax->list stx))
  (if elements
      (core-list (map syntax->core elements)
                 source line column position span)
      (let ([value (syntax-e stx)])
        (core-atom
         (if (symbol? value)
             (string->symbol
              (string-replace (symbol->string value) "ʼ" "'"))
             value)
         source line column position span))))

(define (identifier-char? character)
  (or (char-alphabetic? character)
      (char-numeric? character)
      (member character '(#\_ #\-))))

;; Racket treats ASCII apostrophe as quote punctuation even in `te'a`.
;; Protect identifier-internal Lojban apostrophes with a same-width marker
;; before read-syntax, then restore them in syntax->core. Comments and strings
;; are left byte-for-byte semantic text.
(define (protect-lojban-apostrophes text)
  (define length (string-length text))
  (define out (open-output-string))
  (let loop ([index 0] [state 'normal] [escaped? #f])
    (when (< index length)
      (define character (string-ref text index))
      (define next-state state)
      (define next-escaped? #f)
      (cond
        [(eq? state 'comment)
         (write-char character out)
         (when (char=? character #\newline) (set! next-state 'normal))]
        [(eq? state 'string)
         (write-char character out)
         (cond
           [escaped? (set! next-escaped? #f)]
           [(char=? character #\\) (set! next-escaped? #t)]
           [(char=? character #\") (set! next-state 'normal)])]
        [else
         (cond
           [(char=? character #\;)
            (write-char character out)
            (set! next-state 'comment)]
           [(char=? character #\")
            (write-char character out)
            (set! next-state 'string)]
           [(and (char=? character #\')
                 (positive? index)
                 (< (add1 index) length)
                 (identifier-char? (string-ref text (sub1 index)))
                 (identifier-char? (string-ref text (add1 index))))
            (write-char #\ʼ out)]
           [else (write-char character out)])])
      (loop (add1 index) next-state next-escaped?)))
  (get-output-string out))

(define (read-core-forms input [source-name 'smusni])
  (define raw
    (if (input-port? input) (port->string input) input))
  (define in (open-input-string (protect-lojban-apostrophes raw)))
  (port-count-lines! in)
  (let loop ([forms '()])
    (define stx (read-syntax source-name in))
    (if (eof-object? stx)
        (reverse forms)
        (loop (cons (syntax->core stx) forms)))))

(define (node-symbol? node symbol)
  (and (core-atom? node) (eq? (core-atom-value node) symbol)))

(define (validate-binder who binder)
  (unless (core-list? binder)
    (error who "expected binder list, got ~e" binder))
  (define elems (core-list-elements binder))
  (define separators
    (for/list ([element (in-list elems)]
               [index (in-naturals)]
               #:when (node-symbol? element '::))
      index))
  (unless (and (= (length separators) 1)
               (positive? (first separators))
               (< (first separators) (sub1 (length elems))))
    (error who "malformed typed binder group at ~a:~a"
           (core-list-line binder) (core-list-column binder))))

(define (validate-telescope who telescope)
  (unless (core-list? telescope)
    (error who "expected binder/telescope list, got ~e" telescope))
  (define elems (core-list-elements telescope))
  (if (and (pair? elems) (core-list? (first elems)))
      (for ([group (in-list elems)]) (validate-binder who group))
      (validate-binder who telescope)))

(define (validate-direct-binder form)
  (define elems (core-list-elements form))
  (define head (core-atom-value (first elems)))
  (case head
    [(λ)
     (unless (= (length elems) 3)
       (error 'validate-core-form "λ requires a telescope and one body"))
     (validate-telescope 'validate-core-form (second elems))
     (void)]
    [(Let)
     (unless (= (length elems) 4)
       (error 'validate-core-form "Let requires binder, value, and body"))
     (validate-binder 'validate-core-form (second elems))
     (void)]
    [(Bind)
     (unless (and (>= (length elems) 4) (even? (length elems)))
       (error 'validate-core-form
              "Bind requires alternating binder/computation pairs and one body"))
     (define tail (rest elems))
     (define pairs (drop-right tail 1))
     (for ([index (in-range 0 (length pairs) 2)])
       (validate-binder 'validate-core-form (list-ref pairs index)))]))

(define (validate-core-form form)
  (cond
    [(core-atom? form) (void)]
    [else
     (define elems (core-list-elements form))
     (when (and (pair? elems)
                (core-atom? (first elems))
                (member (core-atom-value (first elems)) '(λ Let Bind)))
       (validate-direct-binder form))
     (for ([element (in-list elems)]) (validate-core-form element))]))

(define (read-core-specimen input [source-name 'smusni])
  (define forms (read-core-forms input source-name))
  (unless (= (length forms) 1)
    (error 'read-core-specimen "expected exactly one term, got ~a" (length forms)))
  (define form (first forms))
  (unless (core-list? form)
    (error 'read-core-specimen "expected one list term, got ~e" form))
  (validate-core-form form)
  form)

(define (core->datum form)
  (match form
    [(core-atom value _ _ _ _ _) value]
    [(core-list elements _ _ _ _ _)
     `(node ,@(map core->datum elements))]))

(define (core->plain-datum form)
  (match form
    [(core-atom value _ _ _ _ _) value]
    [(core-list elements _ _ _ _ _)
     (map core->plain-datum elements)]))

(define (adapter-binder-pairs binder)
  (define groups
    (if (and (pair? binder) (list? (first binder))) binder (list binder)))
  (append*
   (for/list ([group (in-list groups)])
     (define separator (index-of group '::))
     (unless separator
       (error 'core->redex-adapter "malformed binder group: ~e" group))
     (define variables (take group separator))
     (define type-items (drop group (add1 separator)))
     (define type (if (= (length type-items) 1) (first type-items) type-items))
     (for/list ([variable (in-list variables)]) `(,variable ,type)))))

(define (plain->redex-binding datum)
  (define (walk value)
    (cond
      [(not (list? value)) value]
      [else
       (case (and (pair? value) (symbol? (first value)) (first value))
         [(λ)
          (match value
            [`(λ ,binder ,body)
             `(λ ,(adapter-binder-pairs binder) ,(walk body))]
            [_ (map walk value)])]
         [(Let)
          (match value
            [`(Let ,binder ,rhs ,body)
             (define pairs (adapter-binder-pairs binder))
             (unless (= (length pairs) 1)
               (error 'core->redex-adapter "Let binds one variable"))
             `(Let ,(first pairs) ,(walk rhs) ,(walk body))]
            [_ (map walk value)])]
         [(Bind)
          (define pieces (rest value))
          (define body (last pieces))
          (define alternating (drop-right pieces 1))
          (define grouped
            (for/list ([index (in-range 0 (length alternating) 2)])
              (define pairs
                (adapter-binder-pairs (list-ref alternating index)))
              (unless (= (length pairs) 1)
                (error 'core->redex-adapter "Bind group binds one variable"))
              (match-define (list variable type) (first pairs))
              `(,variable ,type ,(walk (list-ref alternating (add1 index))))))
          `(Bind ,grouped ,(walk body))]
         [else (map walk value)])]))
  (walk datum))

(define (core->redex-adapter form)
  (core-redex-adapter
   (plain->redex-binding (core->plain-datum form))
   form))

(define (redex-adapter->core adapter)
  (unless (core-redex-adapter? adapter)
    (raise-argument-error 'redex-adapter->core "core-redex-adapter?" adapter))
  (define original (core-redex-adapter-original adapter))
  (define expected
    (core-redex-adapter-term (core->redex-adapter original)))
  (unless (alpha-equivalent? SmusniCore expected
                             (core-redex-adapter-term adapter))
    (error 'redex-adapter->core
           "adapter term is not alpha-equivalent to its source-located AST"))
  ;; The validated metadata sidecar supplies the exact locations and site
  ;; identity; synthesizing fresh locations would not be lossless.
  original)
