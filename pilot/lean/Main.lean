import Plausible

open Plausible

inductive SmokeToken where
  | allowed
  | blocked
  deriving Repr, DecidableEq, Arbitrary

def isAllowed : SmokeToken → Bool
  | .allowed => true
  | .blocked => false

def accepted (token : SmokeToken) : Decidable (isAllowed token = true) :=
  inferInstance

#eval isAllowed .allowed
#eval Plausible.Testable.check <|
  ∀ n : Nat, n + 0 = n

def main : IO Unit := do
  IO.println s!"allowed={isAllowed .allowed}; blocked={isAllowed .blocked}"
