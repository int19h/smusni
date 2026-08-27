(smusni-rr-fixture 1
  (fence "samples.md" 63 "f31462b3d6837ee0ae528eb2c40090c63d648886")
  (case 1 (rr
    (parse ("parses/samples-063.json" 1)) ; every rule
    (attach ()) (readings (actual gradable)) ; L1.3, L5.29
    (rows (barda))                        ; L1.1, L5.29
    (stores ())
    (sites ((scale barda (deps ())) (cutoff barda (deps (scale))))) ; L5.29
    (anaphora ()) (force (assert))))      ; L1.2
  (case 2 (rr
    (parse ("parses/samples-063.json" 2)) ; every rule
    (attach ()) (readings (actual too-many)) ; L1.3, L5.28
    (rows (gerku klama))                  ; L1.1, L5.28
    (stores ())
    (sites ((purpose too-many (deps ())) (threshold too-many (deps (purpose))))) ; L5.28
    (anaphora ()) (force (assert))))      ; L1.2
  (case 3 (rr
    (parse ("parses/samples-063.json" 3)) ; every rule
    (attach ()) (readings (actual ellipsis)) ; L1.3, L1.8
    (rows ()) (stores ())
    (sites ((relation cohe (deps ()))))   ; L1.8
    (anaphora ()) (force (assert)))))     ; L1.2
)
