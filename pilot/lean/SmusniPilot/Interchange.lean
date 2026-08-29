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
    | .lambda binderType body =>
        list [symbol "lambda", encodeTy binderType, encodeTerm body]
    | .bind binderType computation body =>
        list [symbol "bind", encodeTy binderType,
          encodeTerm computation, encodeTerm body]
    | .apply function argument =>
        list [symbol "apply", encodeTerm function, encodeTerm argument]
    | .lexical predicate arguments =>
        list [symbol "lexical", string predicate, encodeTerms arguments]
    | .context site arguments =>
        list [symbol "context", encodeSite site, encodeTerms arguments]
    | .vague site constraint =>
        list [symbol "vague", encodeSite site, encodeTerm constraint]
    | .primitive operator arguments =>
        list [symbol "primitive", string operator.name, encodeTerms arguments]

  partial def encodeTerms {scope : Nat} : TermList scope → SExpr
    | .nil => vector []
    | .cons head tail =>
        match encodeTerms tail with
        | .list .square rest => vector (encodeTerm head :: rest)
        | _ => vector [encodeTerm head]
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
    | .list .paren [.atom (.symbol "lambda"), rawType, body] =>
        return .lambda (← decodeTy rawType) (← decodeTerm (scope + 1) body)
    | .list .paren
        [.atom (.symbol "bind"), rawType, computation, body] =>
        return .bind (← decodeTy rawType) (← decodeTerm scope computation)
          (← decodeTerm (scope + 1) body)
    | .list .paren [.atom (.symbol "apply"), function, argument] =>
        return .apply (← decodeTerm scope function) (← decodeTerm scope argument)
    | .list .paren
        [.atom (.symbol "lexical"), .atom (.string predicate), arguments] =>
        return .lexical predicate (← decodeTerms scope arguments)
    | .list .paren [.atom (.symbol "context"), rawSite, arguments] =>
        return .context (← decodeSite scope rawSite)
          (← decodeTerms scope arguments)
    | .list .paren [.atom (.symbol "vague"), rawSite, constraint] =>
        return .vague (← decodeSite scope rawSite)
          (← decodeTerm scope constraint)
    | .list .paren
        [ .atom (.symbol "primitive"), .atom (.string rawOperator),
          arguments ] => do
        let some operator := Primitive.ofName rawOperator
          | .error s!"unknown primitive {rawOperator}"
        return .primitive operator (← decodeTerms scope arguments)
    | value => .error s!"malformed encoded term: {repr value}"

  partial def decodeTerms (scope : Nat) : SExpr → Except String (TermList scope)
    | .list .square [] => pure .nil
    | .list .square (head :: tail) =>
        return .cons (← decodeTerm scope head)
          (← decodeTerms scope (.list .square tail))
    | value => .error s!"malformed encoded term list: {repr value}"
end

inductive SerializedDependency where
  | bound (index : Nat)
  | free (identity : FreeId)
  | site (identity : SiteId)
  deriving Repr, DecidableEq, BEq

structure SiteEntry where
  identity : SiteId
  role : SiteRole
  dependencies : List SerializedDependency
  rrLink : Option String := Option.none
  deriving Repr, DecidableEq, BEq

structure SourceNote where
  document : String
  ordinal : Nat
  binderSpellings : List String
  sourceOrder : List Nat
  line : Option Nat := Option.none
  column : Option Nat := Option.none
  deriving Repr, DecidableEq, BEq

def SerializedDependency.ofDependency {scope : Nat} :
    Dependency scope → SerializedDependency
  | .bound index => .bound index.val
  | .free identity => .free identity
  | .site identity => .site identity

def SiteEntry.ofSite {scope : Nat} (site : Site scope) : SiteEntry :=
  { identity := site.identity
    role := site.role
    dependencies := site.dependencies.map SerializedDependency.ofDependency
    rrLink := site.rrLink }

mutual
  def Term.siteEntries {scope : Nat} : Term scope → List SiteEntry
    | .bound _ | .free _ | .natural _ => []
    | .lambda _ body => Term.siteEntries body
    | .bind _ computation body =>
        Term.siteEntries computation ++ Term.siteEntries body
    | .apply function argument =>
        Term.siteEntries function ++ Term.siteEntries argument
    | .lexical _ arguments => TermList.siteEntries arguments
    | .context site arguments =>
        SiteEntry.ofSite site :: TermList.siteEntries arguments
    | .vague site constraint => SiteEntry.ofSite site :: Term.siteEntries constraint
    | .primitive _ arguments => TermList.siteEntries arguments

  def TermList.siteEntries {scope : Nat} : TermList scope → List SiteEntry
    | .nil => []
    | .cons head tail => Term.siteEntries head ++ TermList.siteEntries tail
end

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

def Bundle.ofSurface (document : String) (surface : SurfaceTerm) :
    Except String (Bundle 0) := do
  let (term, state) ← decodeClosedCore document surface
  pure {
    version := 1
    term
    sites := Term.siteEntries term
    sourceMap := state.sourceNotes.map SourceNote.ofDecodeNote
  }

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
      pure {
        version := ← expectNat rawVersion
        term := ← decodeTerm scope rawTerm
        sites := ← rawSites.mapM decodeSiteEntry
        sourceMap := ← rawSourceMap.mapM decodeSourceNote
      }
  | value => .error s!"malformed interchange bundle: {repr value}"

end Interchange

end SmusniPilot
