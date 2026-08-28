(smusni-rr-fixture 1
  (fence "spec.md" 4 "9d713f6c0194caa64dcf738c85bd1e2918b1b219")
  (case 1 (rr
    (parse ("parses/spec-004.json" 1)) ; every rule
    (attach ()) (readings ())
    (rows (tavla))                    ; L1.4
    (stores ()) (sites ()) (anaphora ()) (force ()))))
)
