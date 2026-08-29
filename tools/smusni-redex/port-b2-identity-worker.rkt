#lang racket

(require racket/match
         "port-b2-spike.rkt")

(command-line
 #:args (depths-datum repetitions-datum trial-datum)
 (define depths
   (match (read (open-input-string depths-datum))
     [(list (? exact-positive-integer? values) ...) values]
     [_ (raise-user-error 'port-b2-identity-worker "invalid depths")]))
 (define repetitions (string->number repetitions-datum))
 (define trial (string->number trial-datum))
 (unless (and (exact-positive-integer? repetitions)
              (exact-nonnegative-integer? trial))
   (raise-user-error 'port-b2-identity-worker "invalid numeric argument"))
 (write (run-b2-identity-trial depths repetitions trial))
 (newline))
