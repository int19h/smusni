(smusni-rr-fixture 1
  (fence "samples.md" 45 "7549d4565ac0ab1e545914425fc678ca69065913")
  (case 1 (rr
    (parse ("parses/samples-045.json" 1)) ; every rule
    (attach ()) (readings (actual))       ; L3.10
    (rows (prenu jmaji))                  ; L1.1, L3.10
    (stores ()) (sites ()) (anaphora ())
    (force (assert)))))                   ; L1.2
