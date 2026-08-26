#lang racket

(require racket/cmdline
         racket/file
         racket/list
         racket/match
         racket/runtime-path
         racket/set
         racket/string
         "elaborate.rkt"
         "extract.rkt"
         "inventory.rkt"
         "models/run.rkt"
         "syntax.rkt"
         "types.rkt")

(provide run-checks spec-rules spec-rule-ids load-rule-coverage rule-coverage-findings)

(define-runtime-path tool-dir ".")
(define expected-findings-path
  (build-path tool-dir "inventory" "expected-findings.sexp"))
(define rule-coverage-path
  (build-path tool-dir "inventory" "rule-coverage.sexp"))
(define spec-path (build-path tool-dir ".." ".." "spec.md"))

;; Rules are read from the normative text itself: every `- **Ln.m**` line
;; between the §11 and §12 headings of spec.md, with its kind — `map` (a
;; lowering judgment, the F₀ population) unless the label is followed by
;; *(gap)*, *(note)*, or *(reading)*. The manifest cites map rules only; the
;; ledger records the map rules no surface specimen cites yet, each with an
;; issue.
(define (spec-rules [path spec-path])
  (define lines (file->lines path))
  (define start (index-where lines (lambda (l) (string-prefix? l "## 11. "))))
  (define stop (index-where lines (lambda (l) (string-prefix? l "## 12. "))))
  (unless (and start stop (< start stop))
    (error 'spec-rules "spec.md §11/§12 headings not found"))
  (for*/list ([line (in-list (take (drop lines start) (- stop start)))]
              [m (in-value (regexp-match #px"^- \\*\\*(L[0-9]+\\.[0-9]+)\\*\\*(?: \\*\\((gap|note|reading)\\)\\*)? " line))]
              #:when m)
    (cons (cadr m) (string->symbol (or (caddr m) "map")))))

(define (spec-rule-ids [path spec-path])
  (map car (spec-rules path)))

;; Returns (values floor ledger). The floor is a ratchet: the number of rules
;; cited by specimens may never fall below it, and a commit that raises
;; coverage must raise the floor, so the recorded number is always exact and a
;; lowered floor is a visible diff.
(define (load-rule-coverage [path rule-coverage-path])
  (match (call-with-input-file path read)
    [`(smusni-rule-coverage 1 (cited-floor ,(? exact-nonnegative-integer? floor)) ,entries ...)
     (define ledger
       (for/list ([entry (in-list entries)])
         (match entry
           [`(uncovered ,(? string? id) ,(? string? issue))
            (unless (regexp-match? #px"^#[0-9]+$" issue)
              (error 'load-rule-coverage "uncovered ~a needs a durable issue like #9, got ~e" id issue))
            (cons id issue)]
           [else (error 'load-rule-coverage "invalid coverage entry: ~e" entry)])))
     (define ids (map car ledger))
     (unless (= (length ids) (set-count (list->set ids)))
       (error 'load-rule-coverage "duplicate uncovered entries in the ledger"))
     (values floor ledger)]
    [else (error 'load-rule-coverage "unsupported rule-coverage header (expect a cited-floor)")]))

;; Gate 3a (#9 M1): returns a list of (cons phase message) findings.
(define (rule-coverage-findings rules classified ledger floor)
  ;; `rules` is a list of (id . kind); only `map` rules are lowering judgments.
  (define kinds (for/hash ([r (in-list rules)]) (values (car r) (cdr r))))
  (define rule-ids (for/list ([r (in-list rules)] #:when (eq? (cdr r) 'map)) (car r)))
  (define known (list->set (map car rules)))
  (define cited (make-hash))
  (define findings '())
  (define (note! message) (set! findings (cons (cons 'rules-error message) findings)))
  (for ([item (in-list classified)] #:when (eq? (fence-kind item) 'specimen))
    (define rules (fence-rules item))
    (define core? (equal? (fence-origin item) "core"))
    (when (and (null? rules) (not core?))
      (note! (format "surface specimen ~a#~a cites no lowering rule"
                     (fence-source item) (fence-ordinal item))))
    (when (and core? (pair? rules))
      (note! (format "core specimen ~a#~a must not cite lowering rules (it lowers no surface Lojban)"
                     (fence-source item) (fence-ordinal item))))
    (for ([id (in-list rules)])
      (cond
        [(not (set-member? known id))
         (note! (format "specimen ~a#~a cites unknown rule ~a"
                        (fence-source item) (fence-ordinal item) id))]
        [(not (eq? (hash-ref kinds id) 'map))
         (note! (format "specimen ~a#~a cites ~a, a ~a rule, not a lowering judgment"
                        (fence-source item) (fence-ordinal item) id (hash-ref kinds id)))]
        [else (hash-set! cited id #t)])))
  (define ledgered (for/hash ([entry (in-list ledger)]) (values (car entry) (cdr entry))))
  (for ([(id issue) (in-hash ledgered)])
    (unless (set-member? known id)
      (note! (format "rule-coverage ledger names unknown rule ~a" id)))
    (when (and (set-member? known id) (not (eq? (hash-ref kinds id) 'map)))
      (note! (format "rule-coverage ledger lists ~a, a ~a rule; only lowering judgments are coverable" id (hash-ref kinds id))))
    (when (hash-has-key? cited id)
      (note! (format "rule-coverage ledger lists ~a as uncovered, but a specimen cites it" id))))
  (for ([id (in-list rule-ids)])
    (unless (or (hash-has-key? cited id) (hash-has-key? ledgered id))
      (note! (format "rule ~a is cited by no specimen and has no uncovered-ledger entry with an issue" id))))
  (when (< (hash-count cited) floor)
    (note! (format "rule coverage fell to ~a cited rules, below the ratchet floor ~a: add specimens, do not ledger" (hash-count cited) floor)))
  (when (> (hash-count cited) floor)
    (note! (format "rule coverage rose to ~a cited rules: raise (cited-floor ~a) in rule-coverage.sexp to ~a" (hash-count cited) floor (hash-count cited))))
  (values (reverse findings) (hash-count cited) (hash-count ledgered)))

(struct expected-finding (source ordinal digest phase pattern issue note)
  #:transparent)
(struct observed-finding (source ordinal digest phase message) #:transparent)

(define (load-expected-findings)
  (match (call-with-input-file expected-findings-path read)
    [`(smusni-expected-findings 1 ,entries ...)
     (for/list ([entry (in-list entries)])
       (match entry
         [`(finding ,source ,ordinal ,digest ,phase ,pattern ,issue ,note)
          (expected-finding source ordinal digest phase pattern issue note)]
         [else (error 'load-expected-findings "invalid expected finding: ~e" entry)]))]
    [else (error 'load-expected-findings "unsupported expected-findings header")]))

(define (finding-key source ordinal) (cons source ordinal))

(define schema-head-exemptions '(C D H P i-rel))

(define (metavariable-head? value)
  (or (member value schema-head-exemptions)
      (and (symbol? value)
           (string-contains? (symbol->string value) "…"))))

(define (collect-application-heads form)
  (define found (mutable-set))
  (define (walk node)
    (when (core-list? node)
      (define elements (core-list-elements node))
      (define head
        (and (pair? elements) (core-atom? (first elements))
             (symbol? (core-atom-value (first elements)))
             (core-atom-value (first elements))))
      (case head
        [(λ)
         ;; Binder telescopes contain type spines such as `(Entity)`, which
         ;; are not term applications and therefore do not have core heads.
         (set-add! found head)
         (when (= (length elements) 3) (walk (third elements)))]
        [(Let)
         (set-add! found head)
         (when (= (length elements) 4)
           (walk (third elements))
           (walk (fourth elements)))]
        [(Bind)
         (set-add! found head)
         (define tail (rest elements))
         (when (and (>= (length tail) 3) (odd? (length tail)))
           (define pairs (drop-right tail 1))
           (for ([index (in-range 1 (length pairs) 2)])
             (walk (list-ref pairs index)))
           (walk (last tail)))]
        [else
         (when head (set-add! found head))
         (for ([element (in-list elements)]) (walk element))])))
  (walk form)
  (set->list found))

(define (match-expected observed expected-by-key)
  (define key (finding-key (observed-finding-source observed)
                           (observed-finding-ordinal observed)))
  (define expected (hash-ref expected-by-key key #f))
  (and expected
       (string=? (observed-finding-digest observed)
                 (expected-finding-digest expected))
       (eq? (observed-finding-phase observed)
            (expected-finding-phase expected))
       (string-contains? (observed-finding-message observed)
                         (expected-finding-pattern expected))
       expected))

(define (run-checks #:strict? [strict? #f])
  (define inventory (load-inventory))
  (check-assembled! inventory)
  (define classified
    (classify-fences (read-all-fences) (load-manifest)))
  (check-corpus! classified)

  (define expected-findings (load-expected-findings))
  (define expected-by-key
    (for/hash ([finding (in-list expected-findings)])
      (values (finding-key (expected-finding-source finding)
                           (expected-finding-ordinal finding))
              finding)))
  (define matched-expected (make-hash))
  (define unexpected '())
  (define passed-fences 0)
  (define passed-terms 0)
  (define schema-count 0)
  (define expansion-count 0)
  (define declaration-count 0)
  (define site-count 0)
  (define choice-count 0)
  (define undeclared-heads (make-hash))

  (for ([item (in-list classified)])
    (with-handlers
        ([exn:fail?
          (lambda (exception)
            (set! unexpected
                  (cons (observed-finding
                         (fence-source item) (fence-ordinal item)
                         (fence-digest item) 'inventory-reader-error
                         (exn-message exception))
                        unexpected)))])
      (for ([form (in-list (read-core-forms (fence-content item)))])
        (for ([head (in-list (collect-application-heads form))]
              #:unless (or (inventory-name-declared? inventory head)
                           (metavariable-head? head)
                           (and (symbol? head)
                                (string-prefix? (symbol->string head) "$"))))
          (hash-update! undeclared-heads head
                        (lambda (locations)
                          (cons (format "~a#~a" (fence-source item)
                                        (fence-ordinal item))
                                locations))
                        '()))))
    (case (fence-kind item)
      [(specimen)
       (with-handlers
           ([exn:fail:smusni?
             (lambda (exception)
               (define observed
                 (observed-finding (fence-source item) (fence-ordinal item)
                                   (fence-digest item) 'type-error
                                   (exn-message exception)))
               (define expected (match-expected observed expected-by-key))
               (if expected
                   (hash-set! matched-expected
                              (finding-key (fence-source item)
                                           (fence-ordinal item))
                              expected)
                   (set! unexpected (cons observed unexpected))))]
            [exn:fail?
             (lambda (exception)
               (set! unexpected
                     (cons (observed-finding
                            (fence-source item) (fence-ordinal item)
                            (fence-digest item) 'checker-error
                            (exn-message exception))
                           unexpected)))])
         (define forms
           (read-core-forms (fence-content item)
                            (format "~a#~a" (fence-source item)
                                    (fence-ordinal item))))
         (for ([form (in-list forms)])
           (validate-core-form form)
           (define elaborated (elaborate-core form inventory))
           (set! site-count (+ site-count (length (elaboration-sites elaborated))))
           (set! choice-count
                 (+ choice-count (length (elaboration-choices elaborated))))
           (define result (infer-core (elaboration-ast elaborated) (hash) inventory))
           (unless (null? (typing-gaps result))
             (error 'check.rkt "unresolved typing gaps: ~a"
                    (string-join (typing-gaps result) "; ")))
           (set! passed-terms (add1 passed-terms)))
         (set! passed-fences (add1 passed-fences)))]
      [(schema)
       (read-core-forms (fence-content item)
                        (format "~a#~a" (fence-source item)
                                (fence-ordinal item)))
       (set! schema-count (add1 schema-count))]
      [(expansion)
       (read-core-forms (fence-content item)
                        (format "~a#~a" (fence-source item)
                                (fence-ordinal item)))
       (set! expansion-count (add1 expansion-count))]
      [(declaration)
       (read-core-forms (fence-content item)
                        (format "~a#~a" (fence-source item)
                                (fence-ordinal item)))
       (set! declaration-count (add1 declaration-count))]
      [(unchecked)
       (set! unexpected
             (cons (observed-finding
                    (fence-source item) (fence-ordinal item)
                    (fence-digest item) 'unchecked
                    (format "unchecked fence: ~a (~a)"
                            (fence-note item) (fence-issue item)))
                   unexpected))]))

  (for ([(head locations) (in-hash undeclared-heads)])
    (set! unexpected
          (cons (observed-finding
                 "inventory" 0 "n/a" 'inventory-error
                 (format "undeclared application head ~a at ~a"
                         head (string-join (remove-duplicates locations) ", ")))
                unexpected)))

  (define rules (spec-rules))
  (define rule-ids (map car rules))
  (define-values (coverage-floor coverage-ledger) (load-rule-coverage))
  (define-values (rule-findings cited-count ledgered-count)
    (rule-coverage-findings rules classified coverage-ledger coverage-floor))
  (for ([finding (in-list rule-findings)])
    (set! unexpected
          (cons (observed-finding "rules" 0 "n/a" (car finding) (cdr finding))
                unexpected)))

  (define stale-expected
    (for/list ([expected (in-list expected-findings)]
               #:unless (hash-has-key?
                         matched-expected
                         (finding-key (expected-finding-source expected)
                                      (expected-finding-ordinal expected))))
      expected))

  (printf "corpus: ~a fences classified; ~a specimen fences/~a terms pass\n"
          (length classified) passed-fences passed-terms)
  (printf "coverage: ~a schemata, ~a expansions, ~a declarations, 0 unchecked\n"
          schema-count expansion-count declaration-count)
  (printf "elaboration: ~a retrieval sites, ~a recorded choices\n"
          site-count choice-count)
  (define map-count (for/sum ([r (in-list rules)]) (if (eq? (cdr r) 'map) 1 0)))
  (printf "rules: ~a in spec §11 (~a lowering judgments = F₀; ~a gap/note/reading); ~a judgments cited by surface specimens (ratchet floor ~a); ~a uncovered (ledgered with issues)\n"
          (length rules) map-count (- (length rules) map-count) cited-count coverage-floor ledgered-count)
  ;; Coverage matrix regenerated from the manifest, one line per §11 family.
  (define cited-ids
    (for*/set ([item (in-list classified)] #:when (eq? (fence-kind item) 'specimen)
               [id (in-list (fence-rules item))]) id))
  (define families
    (remove-duplicates (for/list ([r (in-list rules)]) (car (string-split (car r) ".")))))
  (for ([fam (in-list families)])
    (define fam-rules (for/list ([r (in-list rules)] #:when (string-prefix? (car r) (string-append fam "."))) r))
    (define fam-map (for/list ([r (in-list fam-rules)] #:when (eq? (cdr r) 'map)) (car r)))
    (define fam-cited (for/list ([id (in-list fam-map)] #:when (set-member? cited-ids id)) id))
    (printf "  ~a: ~a judgments, ~a cited, ~a uncovered; ~a gap/note/reading\n"
            fam (length fam-map) (length fam-cited) (- (length fam-map) (length fam-cited))
            (- (length fam-rules) (length fam-map))))
  (printf "bounded pass-through typing rules: ~a\n"
          (string-join (map symbol->string pass-through-forms) ", "))
  (define sorted-matched-keys
    (sort (hash-keys matched-expected)
          (lambda (left right)
            (string<? (format "~a" left) (format "~a" right)))))
  (for ([key (in-list sorted-matched-keys)])
    (define finding (hash-ref matched-expected key))
    (printf "KNOWN ~a#~a [~a] ~a — ~a\n"
            (expected-finding-source finding)
            (expected-finding-ordinal finding)
            (expected-finding-issue finding)
            (expected-finding-pattern finding)
            (expected-finding-note finding)))
  (for ([finding (in-list (reverse unexpected))])
    (printf "UNEXPECTED ~a#~a [~a] ~a\n"
            (observed-finding-source finding)
            (observed-finding-ordinal finding)
            (observed-finding-phase finding)
            (observed-finding-message finding)))
  (for ([finding (in-list stale-expected)])
    (printf "STALE-EXPECTED ~a#~a [~a] no longer produces: ~a\n"
            (expected-finding-source finding)
            (expected-finding-ordinal finding)
            (expected-finding-issue finding)
            (expected-finding-pattern finding)))

  (define model-bank-ok? (run-model-bank))

  (define failure?
    (or (pair? unexpected)
        (pair? stale-expected)
        (not model-bank-ok?)
        (and strict? (positive? (hash-count matched-expected)))))
  (when (and strict? (positive? (hash-count matched-expected)))
    (printf "STRICT: ~a known findings remain\n" (hash-count matched-expected)))
  (if failure? 1 0))

(module+ main
  (define strict? #f)
  (command-line
   #:program "check.rkt"
   #:once-each
   [("--strict") "fail while any known corpus finding remains"
    (set! strict? #t)])
  (exit (run-checks #:strict? strict?)))
