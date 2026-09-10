(smusni-rr-fixture
 1
 (fence "samples.md" 60 "d18b550e979e80e4ef5a9c15530e135e9dc7f869")
 (case 1
   (rr
    (parse ("parses/samples-060.json" 1))
    (attach ())
    (readings (actual other-than))
    (rows (melbi))
    (stores ())
    (sites ((contrast-domain melbi (deps ()))))
    (anaphora ())
    (force (assert))
    (references ()))))
