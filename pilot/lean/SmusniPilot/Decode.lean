import SmusniPilot.Surface
import SmusniPilot.Binding

namespace SmusniPilot

structure Binder where
  spelling : String
  type : Ty
  deriving Repr

def typeName? (raw : String) : Option TypeName :=
  (TypeName.ofName ("sort:" ++ raw)).orElse fun _ =>
  (TypeName.ofName ("type-form:" ++ raw)).orElse fun _ =>
  TypeName.ofName ("type:" ++ raw)

partial def decodeTy : SurfaceTerm → Except String Ty
  | .empty _ => .ok (.named .typeFormRow [])
  | .atom (.symbol name) =>
      if name.toNat?.isSome then .ok (.index name)
      else match typeName? name with
        | some typeName => .ok (.named typeName [])
        | none => .ok (.variable name)
  | .form _ (.lexical name) [] => decodeTy (.atom (.symbol name))
  | term@(.form _ (.lexical name) arguments) => do
      if name.toNat?.isSome then pure (.index term.toSExpr.render)
      else
        let some typeName := typeName? name
          | .error s!"unknown type former {name}"
        let decoded ← arguments.mapM decodeTy
        pure (.named typeName decoded)
  | .application _ function [] => decodeTy function
  | .application _ function arguments =>
      return .named .typeFormRow (← (function :: arguments).mapM decodeTy)
  | term => .error s!"not a type expression: {repr term}"

def typeFromParts : List SurfaceTerm → Except String Ty
  | [] => .error "binder is missing a type"
  | [single] => decodeTy single
  | .atom (.symbol head) :: tail =>
      decodeTy (.form .paren (.lexical head) tail)
  | _ => .error "malformed binder type"

def splitBinderParts : List SurfaceTerm →
    Except String (List String × List SurfaceTerm)
  | [] => .error "binder is missing ::"
  | .atom (.symbol "::") :: typeParts => pure ([], typeParts)
  | .atom (.symbol spelling) :: rest => do
      let (spellings, typeParts) ← splitBinderParts rest
      pure (spelling :: spellings, typeParts)
  | _ => .error "binder names must be symbols"

def decodeBinderDescriptor : SurfaceTerm → Except String (List Binder)
  | .form _ (.lexical firstSpelling) arguments => do
      let (otherSpellings, typeParts) ← splitBinderParts arguments
      let type ← typeFromParts typeParts
      pure <| (firstSpelling :: otherSpellings).map fun spelling =>
        { spelling, type }
  | term => .error s!"malformed binder: {repr term}"

def decodeBinder (term : SurfaceTerm) : Except String Binder := do
  match ← decodeBinderDescriptor term with
  | [binder] => pure binder
  | _ => .error "Bind requires one binder after normalization"

def decodeBinderGroup : SurfaceTerm → Except String (List Binder)
  | term@(.form _ (.lexical _) _) => decodeBinderDescriptor term
  | .application _ first rest => do
      pure (← (first :: rest).mapM decodeBinderDescriptor).flatten
  | term => .error s!"malformed binder group: {repr term}"

def lookupBound (name : String) : (environment : List String) →
    Option (Fin environment.length)
  | [] => none
  | current :: rest =>
      if name == current then some 0
      else (lookupBound name rest).map Fin.succ

structure DecodeNote where
  document : String
  ordinal : Nat
  binderSpellings : List String
  sourceOrder : List Nat
  deriving Repr, Inhabited

structure DecodeState where
  nextSite : Nat := 0
  nextSource : Nat := 0
  sourceNotes : List DecodeNote := []
  deriving Repr, Inhabited

def DecodeState.recordSource (state : DecodeState) (document : String)
    (binderSpellings : List String) : DecodeState :=
  { state with
    nextSource := state.nextSource + 1
    sourceNotes := state.sourceNotes ++ [{
      document
      ordinal := state.nextSource
      binderSpellings
      sourceOrder := [state.nextSource]
    }] }

def freshSite (document expansionRole : String) (role : SiteRole)
    {scope : Nat} (dependencies : List (Dependency scope))
    (state : DecodeState) : Site scope × DecodeState :=
  let identity : SiteId :=
    { document, occurrence := state.nextSite, expansionRole }
  let afterSource := state.recordSource document []
  ({ identity, role, dependencies, rrLink := some document },
    { afterSource with nextSite := state.nextSite + 1 })

def applyAll {scope : Nat} (function : Term scope) :
    TermList scope → Term scope
  | .nil => function
  | .cons argument rest => applyAll (.apply function argument) rest

mutual
  partial def decodeCore (document : String) (environment : List String)
      (surface : SurfaceTerm) (state : DecodeState) :
      Except String (Term environment.length × DecodeState) := do
    match surface with
    | .atom (.string value) =>
        pure (.lexical value .nil, state)
    | .atom (.symbol value) =>
        if let some literal := value.toNat? then
          pure (.natural literal, state)
        else if value.startsWith "$" then
          match lookupBound value environment with
          | some index => pure (.bound index, state)
          | none => pure (.free { domain := value, serial := 0 }, state)
        else
          match Primitive.ofName ("term:" ++ value) with
          | some primitive => pure (.primitive primitive .nil, state)
          | none => pure (.lexical value .nil, state)
    | .empty _ => pure (.primitive .list .nil, state)
    | .application _ function arguments =>
        let (decodedFunction, afterFunction) ←
          decodeCore document environment function state
        let (decodedArguments, afterArguments) ←
          decodeCoreList document environment arguments afterFunction
        pure (applyAll decodedFunction decodedArguments, afterArguments)
    | .form _ (.defined head) _ =>
        .error s!"defined surface form awaits M2: {head.name}"
    | .form _ (.gap head) _ =>
        .error s!"gap/prose-only head has no CoreTerm: {head.name}"
    | .form _ (.tool head) _ =>
        .error s!"tool-only head has no CoreTerm: {head.name}"
    | .form _ (.lexical predicate) arguments =>
        let (decoded, after) ←
          decodeCoreList document environment arguments state
        pure (.lexical predicate decoded, after)
    | .form _ (.primitive .lambda) [binders, body] =>
        let decodedBinders ← decodeBinderGroup binders
        decodeLambdas document environment decodedBinders body
          (state.recordSource document (decodedBinders.map (·.spelling)))
    | .form _ (.primitive .bind) [binderTerm, computation, body] =>
        let binder ← decodeBinder binderTerm
        let state := state.recordSource document [binder.spelling]
        let (decodedComputation, afterComputation) ←
          decodeCore document environment computation state
        let (decodedBody, afterBody) ←
          decodeCore document (binder.spelling :: environment) body
            afterComputation
        pure (.bind binder.type decodedComputation decodedBody, afterBody)
    | .form _ (.primitive .context) arguments =>
        let (decoded, afterArguments) ←
          decodeCoreList document environment arguments state
        let dependencies := decoded.dependencies
        let (site, afterSite) :=
          freshSite document "written-context" .context dependencies
            afterArguments
        pure (.context site decoded, afterSite)
    | .form _ (.primitive .vague) [constraint] =>
        let (decoded, afterConstraint) ←
          decodeCore document environment constraint state
        let (site, afterSite) :=
          freshSite document "written-vague" .vague decoded.dependencies
            afterConstraint
        pure (.vague site decoded, afterSite)
    | .form _ (.primitive .application) (function :: arguments) =>
        let (decodedFunction, afterFunction) ←
          decodeCore document environment function state
        let (decodedArguments, afterArguments) ←
          decodeCoreList document environment arguments afterFunction
        pure (applyAll decodedFunction decodedArguments, afterArguments)
    | .form _ (.primitive .lexicalPredication)
        (.atom (.symbol predicate) :: arguments) =>
        let (decoded, after) ←
          decodeCoreList document environment arguments state
        pure (.lexical predicate decoded, after)
    | .form _ (.primitive operator) arguments =>
        let (decoded, after) ←
          decodeCoreList document environment arguments state
        pure (.primitive operator decoded, after)

  partial def decodeCoreList (document : String) (environment : List String) :
      List SurfaceTerm → DecodeState →
      Except String (TermList environment.length × DecodeState)
    | [], state => pure (.nil, state)
    | head :: tail, state => do
        let (decodedHead, afterHead) ←
          decodeCore document environment head state
        let (decodedTail, afterTail) ←
          decodeCoreList document environment tail afterHead
        pure (.cons decodedHead decodedTail, afterTail)

  partial def decodeLambdas (document : String) (environment : List String) :
      List Binder → SurfaceTerm → DecodeState →
      Except String (Term environment.length × DecodeState)
    | [], body, state => decodeCore document environment body state
    | binder :: rest, body, state => do
        let (decodedBody, afterBody) ←
          decodeLambdas document (binder.spelling :: environment) rest body state
        pure (.lambda binder.type decodedBody, afterBody)
end

def decodeClosedCore (document : String) (surface : SurfaceTerm) :
    Except String (Term 0 × DecodeState) :=
  decodeCore document [] surface {}

end SmusniPilot
