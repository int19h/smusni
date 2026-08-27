(smusni-rr-fixture 1
  (fence "samples.md" 36 "dcea1ed0a217abde9363445f09a21d766080cca6")
  (case 1 (rr
    (parse ("parses/samples-036.json" 1)) ; every rule
    (attach ()) (readings (typical actual)) ; L3.4, L1.3
    (rows (mlatu cinri))                  ; L1.1, L3.4
    (stores ()) (sites ()) (anaphora ())
    (force (assert)))))                   ; L1.2
)
