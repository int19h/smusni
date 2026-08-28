(smusni-rr-fixture 1
  (fence "samples.md" 48 "7803f54fed3fbabeeb36b7fed9b4b6264bee058c")
  (case 1 (rr
    (parse ("parses/samples-048.json" 1)) ; every rule
    (attach ()) (readings (actual many))  ; L1.3, L5.28
    (rows (prenu klama))                  ; L1.1, L5.28
    (stores ())
    (sites ((threshold many (deps ()))))  ; L5.28
    (anaphora ())
    (force (assert)))))                   ; L1.2
)
