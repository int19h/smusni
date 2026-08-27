(smusni-rr-fixture 1
  (fence "spec.md" 2 "621187d74d9d9df8953e2e731ea712bb08a6e111")
  (case 1 (rr
    (parse ("parses/spec-002.json" 1)) ; every rule
    (attach ()) (readings ())
    (rows (klama))                    ; L1.4
    (stores ()) (sites ()) (anaphora ()) (force ()))))
)
