Require Import Step0.

(* Run only through run-bounded.sh.  The derived checker exhausts practical
   memory while validating generic structural shrinks. *)
QuickChickWith shrink_args synth_derivation_preserving_shrinks.
QuickChickWith shrink_args check_derivation_preserving_shrinks.
