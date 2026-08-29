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
  (per-call-ms 0.012896 0.012520 0.013352)
  (max-min-ratio 1.066)
  (material-monotone-growth #f)
  (limit 1.5)
  (result pass))
 (public-compile-and-judge
  (depths 16 32 64)
  (total-ms 1.448 4.027 11.760)
  (compile-ms 0.068 0.136 0.365)
  (judge-ms 1.379 3.890 11.394)
  (node-counts 97 193 385)
  (compile-count-per-query 1)
  (ratios 2.781 2.921)
  (limit 4.0)
  (result pass))
 (report-only-depth128
  (depths 32 64 128)
  (total-ms 3.398 10.212 36.646)
  (compile-ms 0.158 0.335 0.978)
  (judge-ms 3.239 9.875 35.666)
  (node-counts 193 385 769)
  (ratios 3.005 3.589))
 (disposition
  "The bounded four-rule representation spike clears R1 and both end-to-end growth stop conditions. Full A0/B1 rule migration remains unimplemented and requires separate review of this measured result."))
