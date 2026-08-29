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
  (per-call-ms 0.012564 0.012403 0.012556)
  (max-min-ratio 1.013)
  (material-monotone-growth #f)
  (limit 1.5)
  (result pass))
 (public-compile-and-judge
  (depths 16 32 64)
  (total-ms 1.338 3.365 11.041)
  (compile-ms 0.077 0.111 0.281)
  (judge-ms 1.260 3.253 10.758)
  (node-counts 97 193 385)
  (compile-count-per-query 1)
  (ratios 2.515 3.281)
  (limit 4.0)
  (result pass))
 (disposition
  "The bounded four-rule representation spike clears R1 and both end-to-end growth stop conditions. Full A0/B1 rule migration remains unimplemented and requires separate review of this measured result."))
