(smusni-rr-fixture 1
  (fence "samples.md" 22 "00fe2e7f046eae70ff325b29c40883a520b61c01")
  (case 1 (rr
    (parse ("parses/samples-022.json" 1)) ; every rule
    (attach ()) (readings (actual le))    ; L1.3, L3.2
    (rows (mlatu blabi skicu))            ; L1.1, L3.2
    (stores ()) (sites ()) (anaphora ())
    (force (assert)))))                   ; L1.2
