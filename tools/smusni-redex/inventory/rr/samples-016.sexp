(smusni-rr-fixture 1
  (fence "samples.md" 16 "33ea8bb4cdb9bbc90f7e759cd40eb0385ce8bef0")
  (case 1 (rr
    (parse ("parses/samples-016.json" 1)) ; every rule
    (attach ()) (readings (actual))       ; L1.3
    (rows (klama))                        ; L1.1
    (stores ()) (sites ()) (anaphora ())
    (force (assert)))))                   ; L5.8
)
