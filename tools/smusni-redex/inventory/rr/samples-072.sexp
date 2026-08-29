(smusni-rr-fixture 1
  (fence "samples.md" 72 "9e9e7af59a1f4e4f5eef994dd1d2f230dbaf21e4")
  (case 1 (rr
    (parse ("parses/samples-072.json" 1)) ; every rule
    (attach ()) (readings (actual importing witness-set)) ; L5.1, L5.2
    (rows (gerku mlatu tavla))           ; L5.1, L5.2, L1.1
    (stores ()) (sites ()) (anaphora ())
    (force (assert)))))                  ; L1.2
