(smusni-rr-fixture 1
  (fence "samples.md" 5 "bb3f45defaafb03d528961457a04e3c6f27cfd66")
  (case 1 (rr
    (parse ("parses/samples-005.json" 1)) ; every rule
    (attach ()) (readings (actual))       ; L1.3
    (rows (klama))                        ; L1.4
    (stores ()) (sites ()) (anaphora ())
    (force (assert)))))                   ; L1.2
)
