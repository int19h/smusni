(smusni-rr-fixture 1
  (fence "samples.md" 58 "29a4047bce86b1331b60c73b6c86d3a1692b7f97")
  (case 1 (rr
    (parse ("parses/samples-058.json" 1)) ; every rule
    (attach ()) (readings (actual))       ; L1.3
    (rows (sutra klama))                  ; L1.10
    (stores ())
    (sites ((tanru-link sutra-klama (deps ())))) ; L1.10
    (anaphora ())
    (force (assert)))))                   ; L1.2
)
