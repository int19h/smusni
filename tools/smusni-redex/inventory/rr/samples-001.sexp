(smusni-rr-fixture 1
  (fence "samples.md" 1 "738f3c4cc9a19d8708f73af84f65571286474905")
  (case 1
    (rr
      (parse ("parses/samples-001.json" 1)) ; every rule
      (attach ())
      (readings (actual))                   ; L1.3
      (rows (klama))                        ; L1.1
      (stores ())
      (sites ())
      (anaphora ())
      (force (assert))))                    ; L1.2
)
