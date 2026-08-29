import SmusniPilot.Inventory

namespace SmusniPilot

inductive Ty where
  | named (name : TypeName) (arguments : List Ty)
  | variable (name : String)
  | index (value : String)
  deriving Repr, BEq, Inhabited

structure FreeId where
  domain : String
  serial : Nat
  deriving Repr, DecidableEq, BEq, Inhabited

structure SiteId where
  document : String
  occurrence : Nat
  expansionRole : String
  deriving Repr, DecidableEq, BEq, Inhabited

inductive SiteRole where
  | context
  | vague
  deriving Repr, DecidableEq, BEq, Inhabited

inductive Dependency (scope : Nat) where
  | bound (index : Fin scope)
  | free (identity : FreeId)
  | site (identity : SiteId)
  deriving Repr, DecidableEq, BEq

structure Site (scope : Nat) where
  identity : SiteId
  role : SiteRole
  dependencies : List (Dependency scope)
  rrLink : Option String := none
  deriving Repr, DecidableEq, BEq

end SmusniPilot
