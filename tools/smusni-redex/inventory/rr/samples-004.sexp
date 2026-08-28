(smusni-rr-fixture 1
  (fence "samples.md" 4 "6ee5b8e402e2c2f6585d7ade3e4911d3faef1a2a")
  (case 1 (rr
    (parse ("parses/samples-004.json" 1)) ; every rule
    (attach ()) (readings (actual))       ; L1.3
    (rows (klama))                        ; L1.5
    (stores ()) (sites ()) (anaphora ())
    (force (assert)))))                   ; L1.2
)
