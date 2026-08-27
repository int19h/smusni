(smusni-rr-fixture 1
  (fence "samples.md" 17 "14a885a17c62156d54c7ed3a78b6b3908ef59371")
  (case 1 (rr
    (parse ("parses/samples-017.json" 1)) ; every rule
    (attach ()) (readings (actual))       ; L1.3
    (rows (klama stali))                  ; L1.1
    (stores ()) (sites ()) (anaphora ())
    (force (assert connected))))          ; L5.12
  (case 2 (rr
    (parse ("parses/samples-017.json" 2)) ; every rule
    (attach ()) (readings (actual))       ; L1.3
    (rows (klama stali))                  ; L1.1
    (stores ()) (sites ()) (anaphora ())
    (force (assert connected)))))         ; L5.12
)
