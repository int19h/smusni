(smusni-rr-fixture 1
  (fence "spec.md" 10 "30c6bd5c2676ca42a0ec03c53a93c7fdcf91b92d")
  (case 1 (rr
    (parse ("parses/spec-010.json" 1)) ; every rule
    (attach ()) (readings (global-exact)) ; L5.2
    (rows (gerku bajra))              ; L1.1, L5.2
    (stores ())
    (sites ((omit nuclear-bajra-2 (deps ()))
            (omit nuclear-bajra-3 (deps ()))
            (omit nuclear-bajra-4 (deps ())))) ; L0.1
    (anaphora ()) (force ()))))
)
