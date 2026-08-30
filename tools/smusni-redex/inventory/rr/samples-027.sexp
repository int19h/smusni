(smusni-rr-fixture 1
  (fence "samples.md" 27 "72483335a75e31f291142a3eae2a3a1708356925")
  (case 1 (rr
    (parse ("parses/samples-027.json" 1)) ; every rule
    (attach ())
    (readings (joi-group))               ; L5.22
    (rows ())
    (stores ())
    (sites ((group-basis joi (deps ())))) ; L5.22
    (anaphora ())
    (force (mention)))))                 ; utterance consumer
