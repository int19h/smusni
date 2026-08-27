(smusni-rr-fixture 1
  (fence "spec.md" 1 "e11b80722140960fac027e32c07ce60254e32614")
  (case 1 (rr
    (parse ("parses/spec-001.json" 1)) ; every rule
    (attach ()) (readings ())
    (rows (klama))                    ; L1.1
    (stores ()) (sites ()) (anaphora ()) (force ()))))
)
