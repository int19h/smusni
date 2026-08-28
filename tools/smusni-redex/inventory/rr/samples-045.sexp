(smusni-rr-fixture 1
  (fence "samples.md" 45 "1a575b6f5bb94517627d63ad1a30f80d0a825446")
  (case 1 (rr
    (parse ("parses/samples-045.json" 1)) ; every rule
    (attach ())
    (readings (actual inner-no))          ; L1.3, L3.10
    (rows (prenu jmaji))                  ; L0.1, L1.1
    (stores ())
    (sites ())
    (anaphora ())
    (force (assert)))))                   ; L1.2
)
