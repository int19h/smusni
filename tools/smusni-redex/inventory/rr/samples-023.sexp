(smusni-rr-fixture 1
  (fence "samples.md" 23 "51894d5541b6381e478bca7b33a039b6f96feab4")
  (case 1 (rr
    (parse ("parses/samples-023.json" 1)) ; every rule
    (attach ()) (readings (actual name))  ; L1.3, L3.3
    (rows (klama))                        ; L1.1
    (stores ()) (sites ()) (anaphora ())
    (force (assert)))))                   ; L1.2
