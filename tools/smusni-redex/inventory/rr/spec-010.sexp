(smusni-rr-fixture 1
  (fence "spec.md" 10 "a15294b018e4042b2b06bd4bb50dd1c36d844909")
  (case 1 (rr
    (parse ("parses/spec-010.json" 1)) ; every rule; unresolved source
    (attach ()) (readings (global-exact)) ; L5.2
    (rows (gerku bajra))              ; L1.1, L5.2
    (stores ())
    (sites ((omit bajra-2 (deps ())) (omit bajra-3 (deps ()))
            (omit bajra-4 (deps ())))) ; L0.1
    (anaphora ()) (force ()))))
)
