#lang racket

(require file/sha1
         racket/cmdline
         racket/file
         racket/list
         racket/match
         racket/path
         racket/runtime-path)

(provide (struct-out inventory)
         (struct-out row-decl)
         load-inventory
         inventory-name-declared?
         inventory-row
         write-assembled!
         check-assembled!)

(define-runtime-path tool-dir ".")
(define core-path (build-path tool-dir "inventory" "core.sexp"))
(define fixture-path (build-path tool-dir "inventory" "fixtures.sexp"))
(define assembled-path (build-path tool-dir "inventory" "assembled.sexp"))

(struct row-decl (name total event-mode citation) #:transparent)
(struct inventory (sorts subsorts type-forms constants forms rows core-digest fixture-digest)
  #:transparent)

(define (digest-file path)
  (call-with-input-file path sha1))

(define (read-one path)
  (call-with-input-file path read))

(define (load-inventory [core core-path] [fixtures fixture-path])
  (define core-data (read-one core))
  (define fixture-data (read-one fixtures))
  (define sorts (make-hash))
  (define subsorts '())
  (define type-forms (make-hash))
  (define constants (make-hash))
  (define forms (make-hash))
  (match core-data
    [`(smusni-core-inventory 1 ,entries ...)
     (for ([entry (in-list entries)])
       (match entry
         [`(sort ,(? symbol? name) ,(? string? citation))
          (hash-set! sorts name citation)]
         [`(subsort ,(? symbol? child) ,(? symbol? parent) ,(? string? citation))
          (set! subsorts (cons (list child parent citation) subsorts))]
         [`(type-form ,(? symbol? name) ,arity ,(? string? citation))
          (hash-set! type-forms name (list arity citation))]
         [`(constant ,(? symbol? name) ,type ,(? string? citation))
          (hash-set! constants name (list type citation))]
         [`(form ,(? symbol? name) ,status ,signature ,class ,reach ,(? string? citation))
          (hash-set! forms name (list status signature class reach citation))]
         [else (error 'load-inventory "invalid core inventory entry: ~e" entry)]))]
    [else (error 'load-inventory "unsupported core inventory header")])
  (define rows (make-hash))
  (match fixture-data
    [`(smusni-lexical-fixtures 1 ,entries ...)
     (for ([entry (in-list entries)])
       (match entry
         [`(row ,(? symbol? name) ,(? exact-positive-integer? total)
                ,event-mode ,(? string? citation))
          (hash-set! rows name (row-decl name total event-mode citation))]
         [else (error 'load-inventory "invalid fixture row: ~e" entry)]))]
    [else (error 'load-inventory "unsupported fixture inventory header")])
  (define names (append (hash-keys constants) (hash-keys forms) (hash-keys rows)))
  (unless (= (length names) (length (remove-duplicates names)))
    (error 'load-inventory "duplicate declared name across inventory classes"))
  (inventory sorts (reverse subsorts) type-forms constants forms rows
             (digest-file core) (digest-file fixtures)))

(define (inventory-name-declared? inv name)
  (or (hash-has-key? (inventory-constants inv) name)
      (hash-has-key? (inventory-type-forms inv) name)
      (hash-has-key? (inventory-forms inv) name)
      (hash-has-key? (inventory-rows inv) name)))

(define (inventory-row inv name)
  (hash-ref (inventory-rows inv) name #f))

(define (assembled-datum inv)
  `(smusni-assembled-inventory 1
     (core-sha1 ,(inventory-core-digest inv))
     (fixture-sha1 ,(inventory-fixture-digest inv))
     (sorts ,@(sort (hash-keys (inventory-sorts inv)) symbol<?))
     (type-forms ,@(sort (hash-keys (inventory-type-forms inv)) symbol<?))
     (constants ,@(sort (hash-keys (inventory-constants inv)) symbol<?))
     (forms ,@(sort (hash-keys (inventory-forms inv)) symbol<?))
     (fixture-rows ,@(sort (hash-keys (inventory-rows inv)) symbol<?))))

(define (render-assembled inv)
  (with-output-to-string
    (lambda () (pretty-write (assembled-datum inv)))))

(define (write-assembled! [inv (load-inventory)])
  (call-with-output-file assembled-path #:exists 'truncate/replace
    (lambda (out) (display (render-assembled inv) out))))

(define (check-assembled! [inv (load-inventory)])
  (unless (file-exists? assembled-path)
    (error 'check-assembled! "missing generated inventory/assembled.sexp"))
  (unless (string=? (file->string assembled-path) (render-assembled inv))
    (error 'check-assembled! "generated inventory/assembled.sexp is stale")))

(module+ main
  (define write? #f)
  (command-line
   #:program "inventory.rkt"
   #:once-each
   [("--write") "regenerate assembled.sexp" (set! write? #t)]
   [("--check") "check assembled.sexp (default)" (set! write? #f)])
  (define inv (load-inventory))
  (if write? (write-assembled! inv) (check-assembled! inv))
  (printf "inventory: ~a sorts, ~a type formers, ~a core forms, ~a fixture rows\n"
          (hash-count (inventory-sorts inv))
          (hash-count (inventory-type-forms inv))
          (hash-count (inventory-forms inv))
          (hash-count (inventory-rows inv))))
