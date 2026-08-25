#lang racket

(require rackunit
         "../elaborate.rkt"
         "../syntax.rkt")

(define compact
  (read-core-specimen
   "(Assert (Bind {$x :: Entity} (Context) {(gerku $x)}))"
   'compact))
(define compact-elaboration (elaborate-core compact))
(check-not-false
 (member 'force-boundary-shorthand
         (map elaboration-choice-kind
              (elaboration-choices compact-elaboration))))
(check-equal? (length (elaboration-sites compact-elaboration)) 1)

(define already-closed
  (read-core-specimen "(Assert (Close (klama Speaker)))" 'closed))
(define closed-elaboration (elaborate-core already-closed))
(check-false
 (member 'force-boundary-shorthand
         (map elaboration-choice-kind
              (elaboration-choices closed-elaboration))))
(check-not-false
 (member 'Close
         (map elaboration-choice-kind
              (elaboration-choices closed-elaboration))))

(define two-sites
  (read-core-specimen
   "(Bind {$x :: Entity} (Context) {$y :: Entity} (Vague P) {(R $x $y)})"
   'sites))
(define site-values (elaboration-sites (elaborate-core two-sites)))
(check-equal? (map site-id-kind site-values) '(Context Vague))
(check-equal? (map site-id-ordinal site-values) '(1 2))

(displayln "elaboration tests: ok")

