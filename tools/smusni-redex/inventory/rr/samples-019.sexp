(smusni-rr-fixture 1
  (fence "samples.md" 19 "9e3967b0e16d7c22d263f5dd3e873c8babd43e84")
  (case 1 (rr
    (parse ("parses/samples-019.json" 1)) ; every rule
    (attach ()) (readings (actual))       ; L1.3
    (rows (mlatu blabi))                  ; L1.1, L3.1
    (stores ()) (sites ()) (anaphora ())
    (force (assert)))))                   ; L1.2
