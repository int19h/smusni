(smusni-rr-fixture
 1
 (fence "samples.md" 64 "b53d5c6c6eafa47816dcb3dc8437b083cae3dd37")
 (case 1
   (rr
    (parse ("parses/samples-064.json" 1))
    (attach ())
    (readings (actual gradable))
    (rows (barda))
    (stores ())
    (sites ((scale barda (deps ())) (cutoff barda (deps (scale)))))
    (anaphora ())
    (force (assert))
    (references ())))
 (case 2
   (rr
    (parse ("parses/samples-064.json" 2))
    (attach ())
    (readings (actual too-many))
    (rows (gerku klama))
    (stores ())
    (sites ((purpose too-many (deps ())) (threshold too-many (deps (purpose)))))
    (anaphora ())
    (force (assert))
    (references ())))
 (case 3
   (rr
    (parse ("parses/samples-064.json" 3))
    (attach ())
    (readings (actual ellipsis))
    (rows ())
    (stores ())
    (sites ((relation cohe (deps ()))))
    (anaphora ())
    (force (assert))
    (references ()))))
