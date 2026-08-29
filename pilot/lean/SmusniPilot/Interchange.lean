import SmusniPilot.Decode

namespace SmusniPilot

namespace Interchange

def symbol (value : String) : SExpr := .atom (.symbol value)
def string (value : String) : SExpr := .atom (.string value)
def list (items : List SExpr) : SExpr := .list .paren items
def vector (items : List SExpr) : SExpr := .list .square items

def expectSymbol : SExpr → Except String String
  | .atom (.symbol value) => .ok value
  | value => .error s!"expected symbol, got {repr value}"

def expectString : SExpr → Except String String
  | .atom (.string value) => .ok value
  | value => .error s!"expected string, got {repr value}"

def expectNat (value : SExpr) : Except String Nat := do
  let raw ← expectSymbol value
  let some result := raw.toNat?
    | .error s!"expected natural, got {raw}"
  pure result

def encodeTy : Ty → SExpr
  | .named name arguments =>
      list [symbol "ty", string name.name, vector (arguments.map encodeTy)]
  | .variable name => list [symbol "type-variable", string name]
  | .index value => list [symbol "type-index", string value]
  | .function effectful parameters result =>
      list [symbol (if effectful then "effectful-function-type" else "function-type"),
        vector (parameters.map encodeTy), encodeTy result]

partial def decodeTy : SExpr → Except String Ty
  | .list .paren
      [ .atom (.symbol "ty"), .atom (.string rawName),
        .list .square arguments ] => do
      let some name := TypeName.ofName rawName
        | .error s!"unknown encoded type {rawName}"
      pure (.named name (← arguments.mapM decodeTy))
  | .list .paren
      [.atom (.symbol "type-variable"), .atom (.string name)] =>
      pure (.variable name)
  | .list .paren
      [.atom (.symbol "type-index"), .atom (.string value)] =>
      pure (.index value)
  | .list .paren
      [.atom (.symbol "function-type"), .list .square parameters, result] =>
      return .function false (← parameters.mapM decodeTy) (← decodeTy result)
  | .list .paren
      [ .atom (.symbol "effectful-function-type"),
        .list .square parameters, result ] =>
      return .function true (← parameters.mapM decodeTy) (← decodeTy result)
  | value => .error s!"malformed encoded type: {repr value}"

def encodeFreeId (identity : FreeId) : SExpr :=
  list [symbol "free-id", string identity.domain, symbol (toString identity.serial)]

def decodeFreeId : SExpr → Except String FreeId
  | .list .paren
      [.atom (.symbol "free-id"), .atom (.string domain), serial] => do
      pure { domain, serial := ← expectNat serial }
  | value => .error s!"malformed free id: {repr value}"

def encodeSiteId (identity : SiteId) : SExpr :=
  list [symbol "site-id", string identity.document,
    symbol (toString identity.occurrence), string identity.expansionRole]

def decodeSiteId : SExpr → Except String SiteId
  | .list .paren
      [ .atom (.symbol "site-id"), .atom (.string document), occurrence,
        .atom (.string expansionRole) ] => do
      pure { document, occurrence := ← expectNat occurrence, expansionRole }
  | value => .error s!"malformed site id: {repr value}"

def encodeRole : SiteRole → SExpr
  | .context => symbol "context"
  | .vague => symbol "vague"

def decodeRole : SExpr → Except String SiteRole
  | .atom (.symbol "context") => .ok .context
  | .atom (.symbol "vague") => .ok .vague
  | value => .error s!"malformed site role: {repr value}"

def encodeDependency {scope : Nat} : Dependency scope → SExpr
  | .bound index => list [symbol "bound", symbol (toString index.val)]
  | .free identity => list [symbol "free", encodeFreeId identity]
  | .site identity => list [symbol "site", encodeSiteId identity]

def decodeDependency (scope : Nat) : SExpr → Except String (Dependency scope)
  | .list .paren [.atom (.symbol "bound"), rawIndex] => do
      let index ← expectNat rawIndex
      if inBounds : index < scope then pure (.bound ⟨index, inBounds⟩)
      else .error s!"bound dependency {index} outside scope {scope}"
  | .list .paren [.atom (.symbol "free"), rawIdentity] =>
      return .free (← decodeFreeId rawIdentity)
  | .list .paren [.atom (.symbol "site"), rawIdentity] =>
      return .site (← decodeSiteId rawIdentity)
  | value => .error s!"malformed dependency: {repr value}"

def encodeSite {scope : Nat} (site : Site scope) : SExpr :=
  list [symbol "site", encodeSiteId site.identity, encodeRole site.role,
    vector (site.dependencies.map encodeDependency),
    match site.rrLink with
      | Option.none => list [symbol "none"]
      | Option.some link => list [symbol "some", string link]]

def decodeSite (scope : Nat) : SExpr → Except String (Site scope)
  | .list .paren
      [ .atom (.symbol "site"), rawIdentity, rawRole,
        .list .square rawDependencies, rawLink ] => do
      let rrLink ← match rawLink with
        | .list .paren [.atom (.symbol "none")] => pure Option.none
        | .list .paren [.atom (.symbol "some"), .atom (.string link)] =>
            pure (Option.some link)
        | _ => .error "malformed RR link"
      pure {
        identity := ← decodeSiteId rawIdentity
        role := ← decodeRole rawRole
        dependencies := ← rawDependencies.mapM (decodeDependency scope)
        rrLink
      }
  | value => .error s!"malformed site: {repr value}"

mutual
  partial def encodeTerm {scope : Nat} : Term scope → SExpr
    | .bound index => list [symbol "bound", symbol (toString index.val)]
    | .free identity => list [symbol "free", encodeFreeId identity]
    | .natural literal => list [symbol "natural", symbol (toString literal)]
    | .string literal => list [symbol "string", string literal]
    | .index literal => list [symbol "index", string literal]
    | .lambda binderType body =>
        list [symbol "lambda", encodeTy binderType, encodeTerm body]
    | .bind binderType computation body =>
        list [symbol "bind", encodeTy binderType,
          encodeTerm computation, encodeTerm body]
    | .apply function arguments =>
        list [symbol "apply", encodeTerm function, encodeTerms arguments]
    | .lexical predicate arguments =>
        list [symbol "lexical", string predicate, encodeTerms arguments]
    | .context site arguments =>
        list [symbol "context", encodeSiteId site, encodeTerms arguments]
    | .vague site constraint =>
        list [symbol "vague", encodeSiteId site, encodeTerm constraint]
    | .primitive operator arguments =>
        list [symbol "primitive", string operator.name, encodeTerms arguments]

  partial def encodeTerms {scope : Nat} : TermList scope → SExpr
    | .nil => vector []
    | .positional head tail =>
        match encodeTerms tail with
        | .list .square rest =>
            vector (list [symbol "positional", encodeTerm head] :: rest)
        | _ => vector [list [symbol "positional", encodeTerm head]]
    | .labelled label head tail =>
        match encodeTerms tail with
        | .list .square rest =>
            vector (list [symbol "labelled", string label, encodeTerm head] :: rest)
        | _ => vector [list [symbol "labelled", string label, encodeTerm head]]
end

mutual
  partial def decodeTerm (scope : Nat) : SExpr → Except String (Term scope)
    | .list .paren [.atom (.symbol "bound"), rawIndex] => do
        let index ← expectNat rawIndex
        if inBounds : index < scope then pure (.bound ⟨index, inBounds⟩)
        else .error s!"bound variable {index} outside scope {scope}"
    | .list .paren [.atom (.symbol "free"), rawIdentity] =>
        return .free (← decodeFreeId rawIdentity)
    | .list .paren [.atom (.symbol "natural"), literal] =>
        return .natural (← expectNat literal)
    | .list .paren [.atom (.symbol "string"), .atom (.string literal)] =>
        return .string literal
    | .list .paren [.atom (.symbol "index"), .atom (.string literal)] =>
        return .index literal
    | .list .paren [.atom (.symbol "lambda"), rawType, body] =>
        return .lambda (← decodeTy rawType) (← decodeTerm (scope + 1) body)
    | .list .paren
        [.atom (.symbol "bind"), rawType, computation, body] =>
        return .bind (← decodeTy rawType) (← decodeTerm scope computation)
          (← decodeTerm (scope + 1) body)
    | .list .paren [.atom (.symbol "apply"), function, arguments] =>
        return .apply (← decodeTerm scope function) (← decodeTerms scope arguments)
    | .list .paren
        [.atom (.symbol "lexical"), .atom (.string predicate), arguments] =>
        return .lexical predicate (← decodeTerms scope arguments)
    | .list .paren [.atom (.symbol "context"), rawSite, arguments] =>
        return .context (← decodeSiteId rawSite)
          (← decodeTerms scope arguments)
    | .list .paren [.atom (.symbol "vague"), rawSite, constraint] =>
        return .vague (← decodeSiteId rawSite)
          (← decodeTerm scope constraint)
    | .list .paren
        [ .atom (.symbol "primitive"), .atom (.string rawOperator),
          arguments ] => do
        let some operator := FirstOrderPrimitive.ofName rawOperator
          | .error s!"unknown primitive {rawOperator}"
        return .primitive operator (← decodeTerms scope arguments)
    | value => .error s!"malformed encoded term: {repr value}"

  partial def decodeTerms (scope : Nat) : SExpr → Except String (TermList scope)
    | .list .square [] => pure .nil
    | .list .square
        (.list .paren [.atom (.symbol "positional"), head] :: tail) =>
        return .positional (← decodeTerm scope head)
          (← decodeTerms scope (.list .square tail))
    | .list .square
        ( .list .paren
            [.atom (.symbol "labelled"), .atom (.string label), head] :: tail) =>
        return .labelled label (← decodeTerm scope head)
          (← decodeTerms scope (.list .square tail))
    | value => .error s!"malformed encoded term list: {repr value}"
end

def renderCanonicalTerm {scope : Nat} (term : Term scope) : String :=
  (encodeTerm term).render

def decodeCanonicalTerm (scope : Nat) (source : String) :
    Except String (Term scope) :=
  SExpr.parse source >>= decodeTerm scope

structure SourceNote where
  document : String
  ordinal : Nat
  binderSpellings : List String
  sourceOrder : List Nat
  line : Option Nat := Option.none
  column : Option Nat := Option.none
  deriving Repr, DecidableEq, BEq

def SourceNote.ofDecodeNote (note : DecodeNote) : SourceNote :=
  { document := note.document
    ordinal := note.ordinal
    binderSpellings := note.binderSpellings
    sourceOrder := note.sourceOrder }

structure Bundle (scope : Nat) where
  version : Nat
  term : Term scope
  sites : List SiteEntry
  sourceMap : List SourceNote
  deriving Repr

def validateSiteDependencies (sites : List SiteEntry) :
    List SerializedDependency → Except String Unit
  | [] => pure ()
  | .site identity :: rest =>
      if sites.any fun candidate => candidate.identity == identity then
        validateSiteDependencies sites rest
      else .error s!"dangling site dependency: {repr identity}"
  | _ :: rest => validateSiteDependencies sites rest

def validateSiteUse (sites : List SiteEntry) (use : SiteUse) :
    Except String Unit :=
  match sites.find? fun candidate =>
      candidate.identity == use.identity with
  | none => .error s!"missing site sidecar entry: {repr use.identity}"
  | some entry =>
      if entry.role != use.role then
        .error s!"site role conflicts with term occurrence: {repr use.identity}"
      else
        -- The binding layer calls this same typed deserializer before applying
        -- a total `Site.rename`/`Site.substitute` transform.
        match SiteEntry.toSite use.scope entry with
        | .error message => .error message
        | .ok _ => validateSiteDependencies sites entry.dependencies

theorem validateSiteUse_deserializes (sites : List SiteEntry) (use : SiteUse)
    (success : validateSiteUse sites use = .ok ()) :
    ∃ entry site,
      sites.find? (fun candidate => candidate.identity == use.identity) =
        some entry ∧
      SiteEntry.toSite use.scope entry = .ok site := by
  unfold validateSiteUse at success
  cases lookup : sites.find? (fun candidate => candidate.identity == use.identity)
  with
  | none => simp [lookup] at success
  | some entry =>
      cases roleConflict : entry.role != use.role with
      | true => simp [lookup, roleConflict] at success
      | false =>
          cases typed : SiteEntry.toSite use.scope entry with
          | error message => simp [lookup, roleConflict, typed] at success
          | ok site => exact ⟨entry, site, rfl, typed⟩

def dependencySiteUses (sites : List SiteEntry) (scope : Nat) :
    List SerializedDependency → Except String (List SiteUse)
  | [] => pure []
  | .site identity :: rest => do
      let some entry := sites.find? fun candidate =>
          candidate.identity == identity
        | .error s!"dangling site dependency: {repr identity}"
      pure ({ identity, role := entry.role, scope } ::
        (← dependencySiteUses sites scope rest))
  | _ :: rest => dependencySiteUses sites scope rest

def enqueueNewSiteUses (seen pending : List SiteUse) :
    List SiteUse → List SiteUse
  | [] => pending
  | use :: rest =>
      if seen.contains use || pending.contains use then
        enqueueNewSiteUses seen pending rest
      else enqueueNewSiteUses seen (pending ++ [use]) rest

def reachableSiteUsesLoop (sites : List SiteEntry) :
    Nat → List SiteUse → List SiteUse → Except String (List SiteUse)
  | 0, [], seen => pure seen
  | 0, _ :: _, _ => .error "site dependency closure exceeded finite table bound"
  | _ + 1, [], seen => pure seen
  | fuel + 1, use :: pending, seen => do
      validateSiteUse sites use
      let some entry := sites.find? fun candidate =>
          candidate.identity == use.identity
        | .error s!"missing site sidecar entry: {repr use.identity}"
      let children ← dependencySiteUses sites use.scope entry.dependencies
      let next := enqueueNewSiteUses (use :: seen) pending children
      reachableSiteUsesLoop sites fuel next (use :: seen)

def reachableSiteUses (sites : List SiteEntry) (roots : List SiteUse) :
    Except String (List SiteUse) :=
  let initial := roots.eraseDups
  let fuel := (sites.length + 1) * (initial.length + 1)
  reachableSiteUsesLoop sites fuel initial []

def Bundle.validateWithUses {scope : Nat} (bundle : Bundle scope) :
    Except String (List SiteUse) := do
  if bundle.version != 1 then
    .error s!"unsupported interchange version {bundle.version}"
  let uses := bundle.term.siteUses
  for entry in bundle.sites do
    let copies := bundle.sites.filter fun other =>
      other.identity == entry.identity
    if copies.length != 1 then
      .error s!"duplicate site sidecar entry: {repr entry.identity}"
  let reachable ← reachableSiteUses bundle.sites uses
  for entry in bundle.sites do
    if !(reachable.any fun use => use.identity == entry.identity) then
      .error s!"unreachable site sidecar entry: {repr entry.identity}"
  pure reachable

def Bundle.validate {scope : Nat} (bundle : Bundle scope) :
    Except String Unit := do
  let _ ← bundle.validateWithUses
  pure ()

theorem validateWithUses_implies_validate {scope : Nat} (bundle : Bundle scope)
    (uses : List SiteUse) (success : bundle.validateWithUses = .ok uses) :
    bundle.validate = .ok () := by
  unfold Bundle.validate
  rw [success]
  rfl

def Bundle.ofSurface (document : String) (surface : SurfaceTerm) :
    Except String (Bundle 0) := do
  let (term, state) ← decodeClosedCore document surface
  let bundle : Bundle 0 := {
    version := 1
    term
    sites := state.sites
    sourceMap := state.sourceNotes.map SourceNote.ofDecodeNote
  }
  bundle.validate
  pure bundle

def Bundle.ofSurfaceWith (document : String) (lexicalHeads freeNames : List String)
    (rrLink : Option String) (surface : SurfaceTerm) :
    Except String (Bundle 0) := do
  let (term, state) ←
    decodeClosedCoreWith document lexicalHeads freeNames rrLink surface
  let bundle : Bundle 0 := {
    version := 1
    term
    sites := state.sites
    sourceMap := state.sourceNotes.map SourceNote.ofDecodeNote
  }
  bundle.validate
  pure bundle

def encodeSerializedDependency : SerializedDependency → SExpr
  | .bound index => list [symbol "bound", symbol (toString index)]
  | .free identity => list [symbol "free", encodeFreeId identity]
  | .site identity => list [symbol "site", encodeSiteId identity]

def decodeSerializedDependency : SExpr → Except String SerializedDependency
  | .list .paren [.atom (.symbol "bound"), index] =>
      return .bound (← expectNat index)
  | .list .paren [.atom (.symbol "free"), identity] =>
      return .free (← decodeFreeId identity)
  | .list .paren [.atom (.symbol "site"), identity] =>
      return .site (← decodeSiteId identity)
  | value => .error s!"malformed serialized dependency: {repr value}"

def encodeSiteEntry (entry : SiteEntry) : SExpr :=
  list [symbol "site-entry", encodeSiteId entry.identity, encodeRole entry.role,
    vector (entry.dependencies.map encodeSerializedDependency),
    match entry.rrLink with
      | Option.none => list [symbol "none"]
      | Option.some link => list [symbol "some", string link]]

def decodeSiteEntry : SExpr → Except String SiteEntry
  | .list .paren
      [ .atom (.symbol "site-entry"), identity, role,
        .list .square dependencies, rawLink ] => do
      let rrLink ← match rawLink with
        | .list .paren [.atom (.symbol "none")] => pure Option.none
        | .list .paren [.atom (.symbol "some"), .atom (.string link)] =>
            pure (Option.some link)
        | _ => .error "malformed site-entry RR link"
      pure {
        identity := ← decodeSiteId identity
        role := ← decodeRole role
        dependencies := ← dependencies.mapM decodeSerializedDependency
        rrLink
      }
  | value => .error s!"malformed site entry: {repr value}"

def encodeOptionalNat : Option Nat → SExpr
  | Option.none => list [symbol "none"]
  | Option.some value => list [symbol "some", symbol (toString value)]

def decodeOptionalNat : SExpr → Except String (Option Nat)
  | .list .paren [.atom (.symbol "none")] => pure Option.none
  | .list .paren [.atom (.symbol "some"), value] =>
      return Option.some (← expectNat value)
  | value => .error s!"malformed optional natural: {repr value}"

def encodeSourceNote (note : SourceNote) : SExpr :=
  list [symbol "source-note", string note.document,
    symbol (toString note.ordinal),
    vector (note.binderSpellings.map string),
    vector (note.sourceOrder.map (fun value => symbol (toString value))),
    encodeOptionalNat note.line, encodeOptionalNat note.column]

def decodeSourceNote : SExpr → Except String SourceNote
  | .list .paren
      [ .atom (.symbol "source-note"), .atom (.string document), ordinal,
        .list .square rawSpellings, .list .square rawOrder, rawLine,
        rawColumn ] => do
      pure {
        document
        ordinal := ← expectNat ordinal
        binderSpellings := ← rawSpellings.mapM expectString
        sourceOrder := ← rawOrder.mapM expectNat
        line := ← decodeOptionalNat rawLine
        column := ← decodeOptionalNat rawColumn
      }
  | value => .error s!"malformed source note: {repr value}"

def Bundle.encode {scope : Nat} (bundle : Bundle scope) : SExpr :=
  list [symbol "smusni-interchange", symbol (toString bundle.version),
    list [symbol "term", encodeTerm bundle.term],
    list [symbol "sites", vector (bundle.sites.map encodeSiteEntry)],
    list [symbol "source-map", vector (bundle.sourceMap.map encodeSourceNote)]]

def Bundle.decode (scope : Nat) : SExpr → Except String (Bundle scope)
  | .list .paren
      [ .atom (.symbol "smusni-interchange"), rawVersion,
        .list .paren [.atom (.symbol "term"), rawTerm],
        .list .paren [.atom (.symbol "sites"), .list .square rawSites],
        .list .paren
          [.atom (.symbol "source-map"), .list .square rawSourceMap] ] => do
      let bundle : Bundle scope := {
        version := ← expectNat rawVersion
        term := ← decodeTerm scope rawTerm
        sites := ← rawSites.mapM decodeSiteEntry
        sourceMap := ← rawSourceMap.mapM decodeSourceNote
      }
      bundle.validate
      pure bundle
  | value => .error s!"malformed interchange bundle: {repr value}"

end Interchange

end SmusniPilot
