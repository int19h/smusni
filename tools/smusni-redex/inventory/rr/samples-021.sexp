(smusni-rr-fixture 1
  (fence "samples.md" 21 "2876852d13a2e58a91e2a64a38a429d66119040d")
  (case 1 (rr
    (parse ("parses/samples-021.json" 1)) ; every rule
    (attach ()) (readings (actual))       ; L1.3
    (rows (mlatu jbena))                  ; L1.1, L3.1
    (stores ()) (sites ()) (anaphora ())
    (force (assert)))))                   ; L1.2
