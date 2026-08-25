#lang racket

(require file/sha1
         racket/cmdline
         racket/file
         racket/list
         racket/match
         racket/path
         racket/runtime-path
         racket/string)

(provide (struct-out fence)
         read-fences
         read-all-fences
         load-manifest
         classify-fences
         generated-corpus
         check-corpus!
         write-corpus!)

(define-runtime-path tool-dir ".")
(define repo-root (simplify-path (build-path tool-dir ".." "..")))
(define manifest-path (build-path tool-dir "inventory" "fences.sexp"))
(define corpus-dir (build-path tool-dir "corpus"))

(struct fence (source ordinal start-line content digest kind note issue)
  #:transparent)
(struct manifest-entry (source ordinal kind digest note issue) #:transparent)

(define fence-open-rx #px"^([[:space:]]*)```lisp[[:space:]]*$")
(define fence-close-rx #px"^[[:space:]]*```[[:space:]]*$")

(define (strip-indent line indent)
  (if (and (positive? (string-length indent))
           (string-prefix? line indent))
      (substring line (string-length indent))
      line))

(define (content-digest content)
  (sha1 (open-input-string content)))

(define (read-fences relative-source)
  (define path (build-path repo-root relative-source))
  (define lines (file->lines path #:mode 'text))
  (let loop ((rest lines)
             (line-number 1)
             (ordinal 0)
             (found '()))
    (if (null? rest)
        (reverse found)
        (let ((opening (regexp-match fence-open-rx (car rest))))
          (if (not opening)
              (loop (cdr rest) (add1 line-number) ordinal found)
              (let collect ((body-lines (cdr rest))
                            (current-line (add1 line-number))
                            (body '()))
                (cond
                  ((null? body-lines)
                   (error 'read-fences
                          "unterminated lisp fence in ~a at line ~a"
                          relative-source line-number))
                  ((regexp-match? fence-close-rx (car body-lines))
                   (define normalized-lines
                     (for/list ((line (in-list (reverse body))))
                       (strip-indent line (cadr opening))))
                   (define content
                     (string-append (string-join normalized-lines "\n") "\n"))
                   (define next-ordinal (add1 ordinal))
                   (loop (cdr body-lines)
                         (add1 current-line)
                         next-ordinal
                         (cons (fence relative-source
                                      next-ordinal
                                      (add1 line-number)
                                      content
                                      (content-digest content)
                                      #f #f #f)
                               found)))
                  (else
                   (collect (cdr body-lines)
                            (add1 current-line)
                            (cons (car body-lines) body))))))))))

(define (read-all-fences)
  (append (read-fences "samples.md")
          (read-fences "spec.md")))

(define valid-kinds '(specimen declaration expansion schema unchecked))

(define (datum->manifest-entry datum)
  (match datum
    [`(fence ,(? string? source) ,(? exact-positive-integer? ordinal)
             ,(? symbol? kind) ,(? string? digest))
     (manifest-entry source ordinal kind digest #f #f)]
    [`(fence ,(? string? source) ,(? exact-positive-integer? ordinal)
             ,(? symbol? kind) ,(? string? digest)
             (note ,(? string? note)))
     (manifest-entry source ordinal kind digest note #f)]
    [`(fence ,(? string? source) ,(? exact-positive-integer? ordinal)
             ,(? symbol? kind) ,(? string? digest)
             (note ,(? string? note)) (issue ,(? string? issue)))
     (manifest-entry source ordinal kind digest note issue)]
    [else (error 'load-manifest "invalid fence entry: ~e" datum)]))

(define (load-manifest [path manifest-path])
  (define datum (call-with-input-file path read))
  (match datum
    [`(smusni-fence-manifest 1 ,entries ...)
     (define parsed (map datum->manifest-entry entries))
     (for ([entry (in-list parsed)])
       (unless (member (manifest-entry-kind entry) valid-kinds)
         (error 'load-manifest "invalid fence kind: ~e" entry))
       (when (eq? (manifest-entry-kind entry) 'unchecked)
         (unless (and (manifest-entry-note entry)
                      (manifest-entry-issue entry))
           (error 'load-manifest
                  "unchecked fence requires note and durable issue: ~e"
                  entry))))
     parsed]
    [else (error 'load-manifest "unsupported manifest header: ~e" datum)]))

(define (entry-key source ordinal) (cons source ordinal))

(define (classify-fences fences entries)
  (define by-key (make-hash))
  (for ([entry (in-list entries)])
    (define key (entry-key (manifest-entry-source entry)
                           (manifest-entry-ordinal entry)))
    (when (hash-has-key? by-key key)
      (error 'classify-fences "duplicate manifest entry for ~e" key))
    (hash-set! by-key key entry))
  (define classified
    (for/list ([item (in-list fences)])
      (define key (entry-key (fence-source item) (fence-ordinal item)))
      (define entry
        (hash-ref by-key key
                  (lambda ()
                    (error 'classify-fences
                           "unclassified lisp fence ~a #~a (line ~a)"
                           (fence-source item) (fence-ordinal item)
                           (fence-start-line item)))))
      (unless (string=? (fence-digest item) (manifest-entry-digest entry))
        (error 'classify-fences
               "stale classification for ~a #~a: expected ~a, got ~a"
               (fence-source item) (fence-ordinal item)
               (manifest-entry-digest entry) (fence-digest item)))
      (hash-remove! by-key key)
      (struct-copy fence item
                   [kind (manifest-entry-kind entry)]
                   [note (manifest-entry-note entry)]
                   [issue (manifest-entry-issue entry)])))
  (unless (zero? (hash-count by-key))
    (error 'classify-fences "manifest contains stale entries: ~e"
           (sort (hash-keys by-key)
                 (lambda (left right)
                   (string<? (format "~a" left) (format "~a" right))))))
  classified)

(define (source-stem source)
  (path->string (path-replace-extension (file-name-from-path source) #"")))

(define (corpus-file-name item)
  (format "~a-~a.lisp"
          (source-stem (fence-source item))
          (~r (fence-ordinal item) #:min-width 3 #:pad-string "0")))

(define (render-fence item)
  (string-append
   "; GENERATED by tools/smusni-redex/extract.rkt; do not edit.\n"
   (format "; source: ~a:~a fence ~a; kind: ~a; sha1: ~a\n"
           (fence-source item) (fence-start-line item) (fence-ordinal item)
           (fence-kind item) (fence-digest item))
   (if (fence-note item) (format "; classification-note: ~a\n" (fence-note item)) "")
   (if (fence-issue item) (format "; durable-issue: ~a\n" (fence-issue item)) "")
   (fence-content item)))

(define (generated-corpus classified)
  (for/hash ([item (in-list classified)])
    (values (corpus-file-name item) (render-fence item))))

(define (existing-corpus-files)
  (if (directory-exists? corpus-dir)
      (for/list ([path (in-directory corpus-dir)]
                 #:when (and (file-exists? path)
                             (regexp-match? #px"[.]lisp$" (path->string path))))
        (path->string (file-name-from-path path)))
      '()))

(define (write-corpus! classified)
  (make-directory* corpus-dir)
  (define expected (generated-corpus classified))
  (for ([name (in-list (existing-corpus-files))]
        #:unless (hash-has-key? expected name))
    (delete-file (build-path corpus-dir name)))
  (for ([(name content) (in-hash expected)])
    (call-with-output-file (build-path corpus-dir name)
      #:exists 'truncate/replace
      (lambda (out) (display content out)))))

(define (check-corpus! classified)
  (define expected (generated-corpus classified))
  (define existing (existing-corpus-files))
  (define expected-names (sort (hash-keys expected) string<?))
  (define existing-names (sort existing string<?))
  (unless (equal? expected-names existing-names)
    (error 'check-corpus!
           "generated corpus file set is stale; expected ~e, found ~e"
           expected-names existing-names))
  (for ([name (in-list expected-names)])
    (define actual (file->string (build-path corpus-dir name)))
    (unless (string=? actual (hash-ref expected name))
      (error 'check-corpus! "generated corpus file is stale: ~a" name))))

(define (guess-kind item)
  (cond
    [(string=? (fence-source item) "samples.md") 'specimen]
    [else 'schema]))

(define (print-template fences)
  (displayln "(smusni-fence-manifest 1")
  (for ([item (in-list fences)])
    (printf "  (fence ~s ~a ~a ~s)\n"
            (fence-source item) (fence-ordinal item) (guess-kind item)
            (fence-digest item)))
  (displayln ")"))

(module+ main
  (define action 'check)
  (command-line
   #:program "extract.rkt"
   #:once-each
   [("--write") "regenerate checked-in corpus files" (set! action 'write)]
   [("--check") "verify manifest and checked-in corpus (default)" (set! action 'check)]
   [("--template") "print a manifest template" (set! action 'template)])
  (define fences (read-all-fences))
  (case action
    [(template) (print-template fences)]
    [else
     (define classified (classify-fences fences (load-manifest)))
     (case action
       [(write) (write-corpus! classified)]
       [(check) (check-corpus! classified)])
     (printf "fences: ~a classified (~a specimens, ~a schemata, ~a unchecked)\n"
             (length classified)
             (count (lambda (item) (eq? (fence-kind item) 'specimen)) classified)
             (count (lambda (item) (eq? (fence-kind item) 'schema)) classified)
             (count (lambda (item) (eq? (fence-kind item) 'unchecked)) classified))]))
