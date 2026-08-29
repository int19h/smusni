# Platform pilot

This tree contains non-normative platform-selection evidence for issue #74.
It does not change Smusni semantics or the authority of `spec.md`.

- `lean/` pins Lean and Plausible and contains the Step −1 smoke.
- `rocq/` pins the jointly supported Rocq plugin tuple and contains the composed
  Autosubst/Equations/QuickChick/extraction smoke.
- `isabelle/` contains the Isabelle quotient/lifting/Nitpick smoke.
- `PROVISIONING.md` records exact versions, constraints, timings, failures, and
  what was not established generally.

Run `./pilot/check-provisioning.sh` after provisioning the external toolchains.
The script reads `ROCQ_SWITCH` (default `smusni-pilot-rocq`) and
`ISABELLE_BIN` (default `isabelle`, with this VM's installed bundle as fallback).
