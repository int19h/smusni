(smusni-rr-fixture 1
  (fence "samples.md" 46 "16d5445b9f0efb113e3a9f4a03224a1f770d4959")
  (case 1 (rr
    (parse ("parses/samples-046.json" 1)) ; every rule
    (attach ()) (readings (actual full-product)) ; L1.3, L5.3
    (rows (gerku prenu nelci))            ; L1.1, L5.3
    (stores ()) (sites ()) (anaphora ())
    (force (assert)))))                   ; L1.2
