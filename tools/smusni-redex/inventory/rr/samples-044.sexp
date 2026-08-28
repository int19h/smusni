(smusni-rr-fixture 1
  (fence "samples.md" 44 "8eac378a0dbb7e9bb101843b6c5f2217febf3ca7")
  (case 1 (rr
    (parse ("parses/samples-044.json" 1)) ; every rule
    (attach ()) (readings (actual importing)) ; L1.3, L5.1
    (rows (gerku blabi))                  ; L1.1, L5.1
    (stores ()) (sites ()) (anaphora ())
    (force (assert)))))                   ; L1.2
)
