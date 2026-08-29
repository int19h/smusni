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

mutual
partial def decodeTy : SurfaceTerm → Except String Ty
  | .empty _ => .ok (.named .typeFormRow [])
  | .atom (.symbol name) =>
      if name.toNat?.isSome then .ok (.index name)
      else match typeName? name with
        | some typeName => .ok (.named typeName [])
        | none => .ok (.variable name)
  | .form _ (.unknown name) [] => decodeTy (.atom (.symbol name))
  | .form _ (.unknown "Fn") [parameters, result] =>
      return .function false (← decodeTyParameters parameters) (← decodeTy result)
  | .form _ (.unknown "EFn") [parameters, result] =>
      return .function true (← decodeTyParameters parameters) (← decodeTy result)
  | term@(.form _ (.unknown name) arguments) => do
      if name.toNat?.isSome then pure (.index term.toSExpr.render)
      else
        let some typeName := typeName? name
          | .error s!"unknown type former {name}"
        let decoded ← arguments.mapM decodeTy
        pure (.named typeName decoded)
  | .form _ (.primitive head) arguments => do
      let raw := rawTermName head.name
      let some typeName := typeName? raw
        | .error s!"term primitive {raw} is not also a type former"
      pure (.named typeName (← arguments.mapM decodeTy))
  | .application _ function [] => decodeTy function
  | .application _ function arguments =>
      return .named .typeFormRow (← (function :: arguments).mapM decodeTy)
  | term => .error s!"not a type expression: {repr term}"

partial def decodeTyParameters : SurfaceTerm → Except String (List Ty)
  | .empty _ => pure []
  | .application _ function [] => return [← decodeTy function]
  | .application _ function arguments => (function :: arguments).mapM decodeTy
  | .form _ kind arguments =>
      let head := .atom (.symbol kind.spelling)
      (head :: arguments).mapM decodeTy
  | term => return [← decodeTy term]
end

def typeFromParts : List SurfaceTerm → Except String Ty
  | [] => .error "binder is missing a type"
  | [single] => decodeTy single
  | .atom (.symbol head) :: tail =>
      decodeTy (.form .paren (.unknown head) tail)
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
  | .form _ (.variable firstSpelling) arguments => do
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
  | term@(.form _ (.variable _) _) => decodeBinderDescriptor term
  | .application _ first rest => do
      pure (← (first :: rest).mapM decodeBinderDescriptor).flatten
  | term => .error s!"malformed binder group: {repr term}"

def decodeBindClauses : List SurfaceTerm →
    Except String (List (Binder × SurfaceTerm) × SurfaceTerm)
  | [body] => pure ([], body)
  | binderTerm :: computation :: rest => do
      let binder ← decodeBinder binderTerm
      let (tail, body) ← decodeBindClauses rest
      pure ((binder, computation) :: tail, body)
  | _ => .error "Bind requires binder/computation pairs and one body"

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
  sites : List SiteEntry := []
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
    (rrLink : Option String)
    {scope : Nat} (dependencies : List (Dependency scope))
    (state : DecodeState) : SiteId × DecodeState :=
  let identity : SiteId :=
    { document, occurrence := state.nextSite, expansionRole }
  let entry : SiteEntry :=
    { identity, role
      dependencies := dependencies.map SerializedDependency.ofDependency
      rrLink }
  let afterSource := state.recordSource document []
  (identity,
    { afterSource with
      nextSite := state.nextSite + 1
      sites := state.sites ++ [entry] })

def applyAll {scope : Nat} (function : Term scope) :
    TermList scope → Term scope
  | .nil => function
  | arguments => .apply function arguments

mutual
  partial def decodeCore (document : String) (lexicalHeads freeNames : List String)
      (rrLink : Option String) (environment : List String)
      (surface : SurfaceTerm) (state : DecodeState) :
      Except String (Term environment.length × DecodeState) := do
    match surface with
    | .atom (.string value) =>
        pure (.string value, state)
    | .atom (.symbol value) =>
        if let some literal := value.toNat? then
          pure (.natural literal, state)
        else if value.startsWith ":" then
          pure (.index value, state)
        else if value.startsWith "$" then
          match lookupBound value environment with
          | some index => pure (.bound index, state)
          | none =>
              if freeNames.contains value then
                pure (.free { domain := value, serial := 0 }, state)
              else .error s!"undeclared free variable {value}"
        else if lexicalHeads.contains value then
          pure (.lexical value .nil, state)
        else
          match FirstOrderPrimitive.ofName ("term:" ++ value) with
          | some primitive => pure (.primitive primitive .nil, state)
          | none =>
              match SurfaceHead.ofName ("term:" ++ value) with
              | some defined =>
                  .error s!"defined surface atom awaits M2: {defined.name}"
              | none =>
                  match GapHead.ofName ("term:" ++ value) with
                  | some gap => .error s!"gap/prose-only atom: {gap.name}"
                  | none =>
                      match ToolHead.ofName ("term:" ++ value) with
                      | some tool => .error s!"tool-only atom: {tool.name}"
                      | none => .error s!"unclassified atom {value}"
    | .empty _ => pure (.primitive .list .nil, state)
    | .application _ function arguments =>
        let (decodedFunction, afterFunction) ←
          decodeCore document lexicalHeads freeNames rrLink environment
            function state
        let (decodedArguments, afterArguments) ←
          decodeCoreList document lexicalHeads freeNames rrLink environment
            arguments afterFunction
        pure (applyAll decodedFunction decodedArguments, afterArguments)
    | .form _ (.defined head) _ =>
        .error s!"defined surface form awaits M2: {head.name}"
    | .form _ (.gap head) _ =>
        .error s!"gap/prose-only head has no CoreTerm: {head.name}"
    | .form _ (.tool head) _ =>
        .error s!"tool-only head has no CoreTerm: {head.name}"
    | .form _ (.unknown head) _ =>
        .error s!"unclassified term head {head}"
    | .form _ (.variable name) arguments =>
        let (decodedFunction, afterFunction) ←
          decodeCore document lexicalHeads freeNames rrLink environment
            (.atom (.symbol name)) state
        let (decodedArguments, afterArguments) ←
          decodeCoreList document lexicalHeads freeNames rrLink environment
            arguments afterFunction
        pure (applyAll decodedFunction decodedArguments, afterArguments)
    | .form _ (.lexical predicate) arguments =>
        let (decoded, after) ←
          decodeCoreList document lexicalHeads freeNames rrLink environment
            arguments state
        pure (.lexical predicate decoded, after)
    | .form _ (.primitive .lambda) [binders, body] =>
        let decodedBinders ← decodeBinderGroup binders
        decodeLambdas document lexicalHeads freeNames rrLink environment
          decodedBinders body
          (state.recordSource document (decodedBinders.map (·.spelling)))
    | .form _ (.primitive .bind) arguments =>
        let (clauses, body) ← decodeBindClauses arguments
        decodeBinds document lexicalHeads freeNames rrLink environment
          clauses body state
    | .form _ (.primitive .context) arguments =>
        let (decoded, afterArguments) ←
          decodeCoreList document lexicalHeads freeNames rrLink environment
            arguments state
        let dependencies := decoded.dependencies
        let (site, afterSite) :=
          freshSite document "written-context" .context rrLink dependencies
            afterArguments
        pure (.context site decoded, afterSite)
    | .form _ (.primitive .vague) [constraint] =>
        let (decoded, afterConstraint) ←
          decodeCore document lexicalHeads freeNames rrLink environment
            constraint state
        let (site, afterSite) :=
          freshSite document "written-vague" .vague rrLink
            decoded.dependencies afterConstraint
        pure (.vague site decoded, afterSite)
    | .form _ (.primitive .application) (function :: arguments) =>
        let (decodedFunction, afterFunction) ←
          decodeCore document lexicalHeads freeNames rrLink environment
            function state
        let (decodedArguments, afterArguments) ←
          decodeCoreList document lexicalHeads freeNames rrLink environment
            arguments afterFunction
        pure (applyAll decodedFunction decodedArguments, afterArguments)
    | .form _ (.primitive .lexicalPredication)
        (.atom (.symbol predicate) :: arguments) =>
        let (decoded, after) ←
          decodeCoreList document lexicalHeads freeNames rrLink environment
            arguments state
        pure (.lexical predicate decoded, after)
    | .form _ (.primitive operator) arguments =>
        let some firstOrder := FirstOrderPrimitive.ofName operator.name
          | .error s!"structural primitive {operator.name} has invalid shape"
        let (decoded, after) ←
          decodeCoreList document lexicalHeads freeNames rrLink environment
            arguments state
        pure (.primitive firstOrder decoded, after)

  partial def decodeCoreList (document : String)
      (lexicalHeads freeNames : List String) (rrLink : Option String)
      (environment : List String) :
      List SurfaceTerm → DecodeState →
      Except String (TermList environment.length × DecodeState)
    | [], state => pure (.nil, state)
    | head :: tail, state => do
        let positional :
            Except String (TermList environment.length × DecodeState) := do
          let (decodedHead, afterHead) ←
            decodeCore document lexicalHeads freeNames rrLink environment head state
          let (decodedTail, afterTail) ←
            decodeCoreList document lexicalHeads freeNames rrLink environment
              tail afterHead
          pure (.positional decodedHead decodedTail, afterTail)
        match head, tail with
        | .atom (.symbol label), value :: rest =>
            if label.startsWith ":" then
              let (decodedHead, afterHead) ←
                decodeCore document lexicalHeads freeNames rrLink environment
                  value state
              let (decodedTail, afterTail) ←
                decodeCoreList document lexicalHeads freeNames rrLink environment
                  rest afterHead
              pure (.labelled label decodedHead decodedTail, afterTail)
            else positional
        | _, _ => positional

  partial def decodeLambdas (document : String)
      (lexicalHeads freeNames : List String) (rrLink : Option String)
      (environment : List String) :
      List Binder → SurfaceTerm → DecodeState →
      Except String (Term environment.length × DecodeState)
    | [], body, state =>
        decodeCore document lexicalHeads freeNames rrLink environment body state
    | binder :: rest, body, state => do
        let (decodedBody, afterBody) ←
          decodeLambdas document lexicalHeads freeNames rrLink
            (binder.spelling :: environment) rest body state
        pure (.lambda binder.type decodedBody, afterBody)

  partial def decodeBinds (document : String)
      (lexicalHeads freeNames : List String) (rrLink : Option String)
      (environment : List String) :
      List (Binder × SurfaceTerm) → SurfaceTerm → DecodeState →
      Except String (Term environment.length × DecodeState)
    | [], body, state =>
        decodeCore document lexicalHeads freeNames rrLink environment body state
    | (binder, computation) :: rest, body, state => do
        let state := state.recordSource document [binder.spelling]
        let (decodedComputation, afterComputation) ←
          decodeCore document lexicalHeads freeNames rrLink environment
            computation state
        let (decodedBody, afterBody) ←
          decodeBinds document lexicalHeads freeNames rrLink
            (binder.spelling :: environment) rest body afterComputation
        pure (.bind binder.type decodedComputation decodedBody, afterBody)
end

def decodeClosedCore (document : String) (surface : SurfaceTerm) :
    Except String (Term 0 × DecodeState) :=
  decodeCore document [] [] Option.none [] surface {}

def decodeClosedCoreWith (document : String) (lexicalHeads freeNames : List String)
    (rrLink : Option String) (surface : SurfaceTerm) :
    Except String (Term 0 × DecodeState) :=
  decodeCore document lexicalHeads freeNames rrLink [] surface {}

end SmusniPilot
