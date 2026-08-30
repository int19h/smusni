(smusni-rr-fixture 1
  (fence "samples.md" 59 "d18b550e979e80e4ef5a9c15530e135e9dc7f869")
  (case 1 (rr
    (parse ("parses/samples-059.json" 1)) ; every rule
    (attach ()) (readings (actual other-than)) ; L1.3, L5.11
    (rows (melbi))                        ; L1.1, L5.11
    (stores ())
    (sites ((contrast-domain melbi (deps ())))) ; L5.11
    (anaphora ())
    (force (assert)))))                   ; L1.2
