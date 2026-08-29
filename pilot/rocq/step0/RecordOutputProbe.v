From Stdlib Require Import List Arith Bool String.
From QuickChick Require Import QuickChick.

Import ListNotations.
Set Warnings "-deprecated-dirpath-Coq,-deprecated-since-9.0,-non-recursive".

Inductive probe_term :=
| ProbeNat (literal : nat)
| ProbePair (first_term second_term : probe_term).
Inductive probe_type := ProbeNatural | ProbePairType.
Inductive probe_rule := ProbeNaturalRule | ProbePairRule.

QCDerive (Show, Arbitrary, Shrink) for probe_term.
QCDerive (Show, Arbitrary, Shrink) for probe_type.
QCDerive (Show, Arbitrary, Shrink) for probe_rule.

Record packed_output : Type := MkPackedOutput {
  packed_term : probe_term;
  packed_type : probe_type;
  packed_trace : list probe_rule
}.

Inductive packed_typing : packed_output -> Prop :=
| PackedNatural : forall literal,
    packed_typing
      (MkPackedOutput (ProbeNat literal) ProbeNatural [ProbeNaturalRule])
| PackedPair :
    forall first_term second_term first_trace second_trace,
    packed_typing
      (MkPackedOutput first_term ProbeNatural first_trace) ->
    packed_typing
      (MkPackedOutput second_term ProbeNatural second_trace) ->
    packed_typing
      (MkPackedOutput (ProbePair first_term second_term) ProbePairType
        (ProbePairRule :: first_trace ++ second_trace)).

(* This is the viable direct-output representation: a single packed output
   avoids the tuple plugin anomaly without duplicating the typing clauses. *)
QCDerive ArbitrarySizedSuchThat for
  (fun generated => packed_typing generated).
