(smusni-rr-fixture 1
  (fence "spec.md" 9 "4da2df77645deee22f6ddfbb87b1418fa7bfecc5")
  (case 1 (rr
    (parse ("parses/spec-009.json" 1)) ; every rule
    (attach ()) (readings (witness-set)) ; L5.2
    (rows (gerku bajra))              ; L1.1, L5.2
    (stores ()) (sites ()) (anaphora ()) (force ()))))
)
