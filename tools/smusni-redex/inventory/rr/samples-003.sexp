(smusni-rr-fixture 1
  (fence "samples.md" 3 "3db37afbd27c832ee661ef1fad0b621eb031fed6")
  (case 1 (rr
    (parse ("parses/samples-003.json" 1)) ; every rule
    (attach ()) (readings (actual))       ; L1.3
    (rows (klama))                        ; L1.4
    (stores ()) (sites ()) (anaphora ())
    (force (assert)))))                   ; L1.2
)
