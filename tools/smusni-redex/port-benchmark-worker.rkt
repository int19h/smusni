#lang racket

(require racket/cmdline
         "port-phase0.rkt")

(define mode #f)
(define runs #f)
(define output #f)
(command-line
 #:program "port-benchmark-worker.rkt"
 #:args (mode-text runs-text output-path)
 (set! mode (string->symbol mode-text))
 (set! runs (string->number runs-text))
 (set! output output-path))

(unless (member mode '(old-only new-only side-by-side))
  (error 'port-benchmark-worker "unsupported mode: ~e" mode))
(unless (exact-positive-integer? runs)
  (error 'port-benchmark-worker "runs must be positive: ~e" runs))

(define result
  (run-benchmark-mode mode
                      (specimen-benchmark-cases (load-port-corpus))
                      runs))
(call-with-output-file output
  (lambda (out)
    (write (benchmark-mode->datum result) out)
    (newline out))
  #:exists 'truncate/replace)
