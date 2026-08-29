(smusni-rr-fixture 1
  (fence "spec.md" 19 "a9c634f7bd73b38f2bdda307801f658a9257861d")
  (case 1 (rr
    (parse ("parses/spec-019.json" 1)) ; every rule
    (attach ()) (readings (zip))       ; L5.21
    (rows (tavla))                    ; L1.1, L5.21
    (stores ()) (sites ()) (anaphora ()) (force ()))))
