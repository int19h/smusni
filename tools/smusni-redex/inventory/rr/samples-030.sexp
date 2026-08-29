(smusni-rr-fixture 1
  (fence "samples.md" 30 "bb927fff8f0424bed33e08d63acaa232f3cca35c")
  (case 1 (rr
    (parse ("parses/samples-030.json" 1)) ; every rule
    (attach ()) (readings (lohi))         ; L3.5, L3.6
    (rows (gerku selcmi))                 ; L3.5, L3.6
    (stores ()) (sites ()) (anaphora ())
    (force (mention)))))                  ; utterance consumer
