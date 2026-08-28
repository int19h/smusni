(smusni-rr-fixture 1
  (fence "samples.md" 71 "e5a3a20cbbc62b1cc8319b03e21c2980781391f5")
  (case 1 (rr
    (parse ("parses/samples-071.json" 1)) ; every rule
    (attach ()) (readings (actual importing)) ; L1.3, L5.1
    (rows (gerku mlatu tavla))           ; L5.1, L3.1, L1.1
    (stores ()) (sites ()) (anaphora ())
    (force (assert)))))                  ; L1.2
)
