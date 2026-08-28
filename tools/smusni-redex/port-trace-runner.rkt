#lang racket

(require racket/cmdline
         racket/list
         racket/path
         "inventory.rkt"
         "syntax.rkt"
         "types.rkt")

(define test-path #f)
(define output-path #f)
(command-line
 #:program "port-trace-runner.rkt"
 #:args (test output)
 (set! test-path (path->complete-path test))
 (set! output-path (path->complete-path output)))

(define observations '())
(define (sorted-env env)
  (sort (hash->list env) symbol<? #:key car))

(define (observe node env inv)
  (set! observations
        (cons `(trace
                (test ,(path->string (file-name-from-path test-path)))
                (term ,(core->plain-datum node))
                (env ,(sorted-env env))
                (inventory ,(inventory-core-digest inv)
                           ,(inventory-fixture-digest inv)))
              observations)))

(parameterize ([current-infer-core-observer observe])
  (dynamic-require test-path #f))

(call-with-output-file output-path
  (lambda (out)
    (write `(smusni-port-trace 1 ,@(reverse observations)) out)
    (newline out))
  #:exists 'truncate/replace)
