(smusni-rr-fixture 1
  (fence "samples.md" 22 "68fd3b480a697f1f7f5d93e6ad02cbfd92541bab")
  (case 1 (rr
    (parse ("parses/samples-022.json" 1)) ; every rule
    (attach ()) (readings (actual le))    ; L1.3, L3.2
    (rows (mlatu blabi skicu))            ; L1.1, L3.2
    (stores ()) (sites ()) (anaphora ())
    (force (assert)))))                   ; L1.2
)
