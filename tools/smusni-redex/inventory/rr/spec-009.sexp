(smusni-rr-fixture
 1
 (fence "spec.md" 9 "51db28bc844d630b0bc9e4d9619cf3fb36107cda")
 (case 1
   (rr
    (parse ("parses/spec-009.json" 1))
    (attach ())
    (readings (global-exact))
    (rows (gerku bajra))
    (stores ())
    (sites ((omit nuclear-bajra-2 (deps ())) (omit nuclear-bajra-3 (deps ())) (omit nuclear-bajra-4 (deps ()))))
    (anaphora ())
    (force ())
    (references ()))))
