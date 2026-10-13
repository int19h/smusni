import SmusniPositive.Controls

namespace SmusniPositive.Controls
open SmusniF02
universe v

/-- This control alone fixes an infinite ground-address supply and one unary key. -/
abbrev chainSignature : Signature where
  Ground := Nat
  Name := Unit
  Key := Unit
  Predicate := Empty
  siteArity _ := 1
  predicateArity := Empty.elim

def chainCode (n : Nat) : Code chainSignature :=
  closed (.ctx () (fun _ => .literal n) (.holdsVar 0))
def chainResolver : Context chainSignature := fun _ args => some (chainCode (args 0 + 1))
def ChainRegion (c : Code chainSignature) : Prop := ∃ n, c = chainCode n ∨ c = holdsCode (chainCode n)

/-- A syntax discriminator for this distinct-code control, not an evaluator. -/
def chainAddress : Code chainSignature → Option Nat
  | .mk (.ctx _ args _) g _ => some ((args 0).eval g)
  | _ => none

theorem chain_codes_injective {n m : Nat} (eq : chainCode n = chainCode m) : n = m :=
  Option.some.inj (congrArg chainAddress eq)

theorem chain_region_step {W : Type v} (M : Model chainSignature W) (i : Input chainSignature W)
    (atChain : i.context = chainResolver) :
    ∀ c, ChainRegion c → ∀ X b, Step M X c i b → ∃ d, ChainRegion d ∧ X d i b := by
  intro c member X b step
  rcases member with ⟨n, rfl | rfl⟩
  · change ∃ q, i.context () (fun _ : Fin 1 => n) = some q ∧ X (holdsCode q) i b at step
    obtain ⟨q, found, next⟩ := step
    rw [atChain] at found
    have eq : chainCode (n+1) = q := Option.some.inj found
    subst q
    exact ⟨holdsCode (chainCode (n+1)), ⟨n+1, Or.inr rfl⟩, next⟩
  · exact ⟨chainCode n, ⟨n, Or.inl rfl⟩, step⟩

theorem chain_event_region_step {W : Type v} (i : Input chainSignature W)
    (atChain : i.context = chainResolver) :
    ∀ c, ChainRegion c → ∀ X token, EventStep X c i token → ∃ d, ChainRegion d ∧ X d i token := by
  intro c member X token step
  rcases member with ⟨n, rfl | rfl⟩
  · change ∃ q, i.context () (fun _ : Fin 1 => n) = some q ∧ X (holdsCode q) i token at step
    obtain ⟨q, found, next⟩ := step
    rw [atChain] at found
    have eq : chainCode (n+1) = q := Option.some.inj found
    subst q
    exact ⟨holdsCode (chainCode (n+1)), ⟨n+1, Or.inr rfl⟩, next⟩
  · exact ⟨chainCode n, ⟨n, Or.inl rfl⟩, step⟩

theorem chain_no_evidence {W : Type v} (M : Model chainSignature W) (c : Code chainSignature)
    (member : ChainRegion c) (w : W) (s : RawState chainSignature) (b : Bool) :
    ¬Evidence M c ⟨chainResolver, w, s⟩ b :=
  copying_region_absent M _ ChainRegion (chain_region_step M _ rfl) member

theorem chain_no_event_evidence {W : Type v} (c : Code chainSignature) (member : ChainRegion c)
    (w : W) (beta : RawState chainSignature) (token : Code chainSignature) :
    ¬EventEvidence c ⟨chainResolver, w, beta⟩ token :=
  event_copying_region_absent _ ChainRegion (chain_event_region_step _ rfl) member

theorem chain_observations {W : Type v} (M : Model chainSignature W) (n : Nat) (w : W)
    (s beta : RawState chainSignature) :
    value M (chainCode n) ⟨chainResolver, w, s⟩ = .u ∧
    event (chainCode n) ⟨chainResolver, w, beta⟩ = none ∧
    value M (holdsCode (chainCode n)) ⟨chainResolver, w, s⟩ = .u ∧
    event (holdsCode (chainCode n)) ⟨chainResolver, w, beta⟩ = none := by
  have codeMem : ChainRegion (chainCode n) := ⟨n, Or.inl rfl⟩
  have bodyMem : ChainRegion (holdsCode (chainCode n)) := ⟨n, Or.inr rfl⟩
  exact ⟨(value_undefined M _ _).mpr ⟨chain_no_evidence M _ codeMem w s true, chain_no_evidence M _ codeMem w s false⟩,
    (event_none _ _).mpr (chain_no_event_evidence _ codeMem w beta),
    (value_undefined M _ _).mpr ⟨chain_no_evidence M _ bodyMem w s true, chain_no_evidence M _ bodyMem w s false⟩,
    (event_none _ _).mpr (chain_no_event_evidence _ bodyMem w beta)⟩
end SmusniPositive.Controls
