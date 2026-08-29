Require Import Step0.

(* The required producer-plus-derived-checker path.  Run only through
   run-validation.sh, which applies explicit wall/RSS bounds. *)
QuickChickWith step0_args synth_generated.
QuickChickWith step0_args check_generated.
