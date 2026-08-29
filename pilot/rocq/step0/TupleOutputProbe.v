From Stdlib Require Import List Arith Bool String.
From QuickChick Require Import QuickChick.

Import ListNotations.
Set Warnings "-deprecated-dirpath-Coq,-deprecated-since-9.0,-non-recursive".

Inductive probe_term :=
| ProbeNat (literal : nat)
| ProbePair (first second : probe_term).

Inductive probe_type := ProbeNatural | ProbePairType.
Inductive probe_rule := ProbeNaturalRule | ProbePairRule.

QCDerive (Show, Arbitrary, Shrink) for probe_term.
QCDerive (Show, Arbitrary, Shrink) for probe_type.
QCDerive (Show, Arbitrary, Shrink) for probe_rule.

Inductive tuple_typing : probe_term -> probe_type -> list probe_rule -> Prop :=
| TupleNatural : forall literal,
    tuple_typing (ProbeNat literal) ProbeNatural [ProbeNaturalRule]
| TuplePair : forall first second first_trace second_trace,
    tuple_typing first ProbeNatural first_trace ->
    tuple_typing second ProbeNatural second_trace ->
    tuple_typing (ProbePair first second) ProbePairType
      (ProbePairRule :: first_trace ++ second_trace).

(* Expected QuickChick 2.2.0 result: internal depDriver pattern-match anomaly. *)
QCDerive ArbitrarySizedSuchThat for
  (fun generated =>
    let '(value, (value_type, value_trace)) := generated in
    tuple_typing value value_type value_trace).
