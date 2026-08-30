(smusni-b2-representation-spike
 1
 (base-head "582c2ffe44ab02e35f553b67c18de3daba010015")
 (scope A0-Synth A0-T-Natural A0-T-Top A0-T-Let)
 (cache-controls
  (capacity 256 (milliseconds 51.243 271.404 1430.017)
                (ratios 5.296 5.269))
  (capacity 4096 (milliseconds 53.704 287.462 1508.656)
                 (ratios 5.353 5.248))
  (disabled (milliseconds 94.487 501.673 3180.620)
            (ratios 5.309 6.340)))
 (identity-micro
  (depths 16 32 64)
  (per-call-ms 0.012513 0.012169 0.013439)
  (max-min-ratio 1.104)
  (material-monotone-growth #f)
  (limit 1.5)
  (command "SMUSNI_B2_R1_FULL=1 raco test tools/smusni-redex/tests/b2-spike-test.rkt")
  (result pass))
 (public-compile-and-judge
  (depths 16 32 64)
  (total-ms 1.588 4.375 12.240)
  (compile-ms 0.086 0.151 0.533)
  (judge-ms 1.501 4.223 11.706)
  (node-counts 97 193 385)
  (compile-count-per-query 1)
  (ratios 2.755 2.798)
  (limit 4.0)
  (result pass))
 (report-only-depth128
  (depths 32 64 128)
  (total-ms 3.861 10.569 35.458)
  (compile-ms 0.168 0.367 0.994)
  (judge-ms 3.691 10.200 34.462)
  (node-counts 193 385 769)
  (ratios 2.738 3.355))
 (disposition
  "The bounded four-rule representation spike clears R1 and both end-to-end growth stop conditions. Under the human-partner option-B decision, full A0/B1 representation migration is deferred until a practical typing trigger fires; B-family work continues on the raw judgment."))
