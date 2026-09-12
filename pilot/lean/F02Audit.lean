import SmusniF02
import F02AuditSupport

/-! Enumerate every declaration belonging to a SmusniF02 module, including
generated helpers. Inspect transitive kernel axioms, not just source spellings.
This audit is a check, not an axiom in any theorem. -/
run_cmd F02Audit.check
