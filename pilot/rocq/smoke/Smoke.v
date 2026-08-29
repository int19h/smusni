From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From Equations Require Import Equations.
From QuickChick Require Import QuickChick.
Require Import Generated.

Import Core.

Check tm.
Check lam.
Check subst_tm.
Check idSubst_tm.

Equations smokeFlip (value : bool) : bool :=
smokeFlip true := false;
smokeFlip false := true.

Check smokeFlip_equation_1.
Check smokeFlip_elim.

Inductive SmokeChoice : Type :=
  | chooseLeft
  | chooseRight.

QCDerive Show for SmokeChoice.
QCDerive Arbitrary for SmokeChoice.

Definition smokeChoiceTotal (_ : SmokeChoice) : bool := true.
QuickChick smokeChoiceTotal.

Definition extractedSmoke (value : nat) : nat := S value.
Extraction "smoke_extract.ml" extractedSmoke.
