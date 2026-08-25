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
(struct core-list (elements source line column position span) #:transparent)

(define-language SmusniSurface
  [atom variable-not-otherwise-mentioned natural string]
  [term atom (node term ...)])

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
