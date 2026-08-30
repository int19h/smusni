(smusni-rr-fixture 1
  (fence "samples.md" 34 "0381ec3ed5e5eefb48e813e4d611efdafc4c7e78")
  (case 1 (rr
    (parse ("parses/samples-034.json" 1)) ; every rule
    (attach ()) (readings (le inner-pa))  ; L3.2, L3.9
    (rows (prenu skicu))                  ; L3.2, L3.15
    (stores ())
    (sites ((group-basis luho (deps ())))) ; L3.14
    (anaphora ())
    (force (mention)))))                  ; utterance consumer
