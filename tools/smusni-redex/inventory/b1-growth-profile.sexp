(smusni-b1-growth-profile
 1
 (base-head "5015362bc72930318fcbdb20beefd0cd5e3ab94a")
 (depths 16 32 64)
 (before-ms 39.470 203.902 1116.855)
 (after-local-ms 34.012 184.243 919.325)
 (before-ratios 5.166 5.477)
 (after-local-ratios 5.417 4.990)
 (attribution
  (depth16-rules (A0-Synth 1) (A0-T-Let 16) (A0-T-Natural 16) (A0-T-Top 1))
  (check-synth-calls 0)
  (env-lookup-calls 0)
  (compatible-natural-us-per-call 0.0063)
  (merge-empty-records-us-per-call 0.1327)
  (shadow-constant-env-ms 2.307 10.788 53.152)
  (shadow-growing-env-ms 3.247 16.952 82.121)
  (shadow-no-binding-ms 0.991 3.903 19.420))
 (mitigation "Binder rules now extend a generic environment through one host-backed metafunction, and lookup is one host association search; no rule re-matches the full environment tail.")
 (conclusion "Compatibility and record canonicalization are negligible; removing environment splits helps but repeated Redex full-subterm/cache-key matching remains superlinear and requires a larger judgment-representation redesign before family growth continues."))
