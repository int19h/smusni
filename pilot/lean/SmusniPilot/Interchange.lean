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

def decodeDependency (scope : Nat) : SExpr → Except String (Dependency scope)
  | .list .paren [.atom (.symbol "bound"), rawIndex] => do
      let index ← expectNat rawIndex
      if inBounds : index < scope then pure (.bound ⟨index, inBounds⟩)
      else .error s!"bound dependency {index} outside scope {scope}"
  | .list .paren [.atom (.symbol "free"), rawIdentity] =>
      return .free (← decodeFreeId rawIdentity)
  | .list .paren [.atom (.symbol "site"), rawIdentity] => do
      let identity ← decodeSiteId rawIdentity
      .error s!"legacy site dependency is not a semantic profile: {repr identity}"
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

/-!
The C-spike coherence object is the single semantic validity invariant.  Raw
ingestion must construct it; certified binding operations must transform it.
The executable validator is being migrated to this structure so it no longer
has a second fuel/order-sensitive notion of reachability.
-/
structure TypedSiteUseWitness {scope : Nat} (bundle : Bundle scope)
    (use : SiteUse) where
  entry : SiteEntry
  entryInTable : entry ∈ bundle.sites
  entryIdentity : entry.identity = use.identity
  entryRole : entry.role = use.role
  site : Site use.scope
  typed : SiteEntry.toSite use.scope entry = .ok site

structure BundleCoherence {scope : Nat} (bundle : Bundle scope) where
  uses : List SiteUse
  usesUnique : uses.Nodup
  rootsCovered : ∀ use, use ∈ bundle.term.siteUses → use ∈ uses
  scopeBound : ∀ use, use ∈ uses → scope ≤ use.scope
  witness : ∀ use, use ∈ uses → TypedSiteUseWitness bundle use
  profileAgreement : ∀ occurrence,
    occurrence ∈ bundle.term.siteOccurrences →
      ∃ present : occurrence.use ∈ uses,
        (witness occurrence.use present).entry.dependencies =
          occurrence.support
  tableUnique : (bundle.sites.map (fun entry => entry.identity)).Nodup
  tableCovered : ∀ entry, entry ∈ bundle.sites →
    ∃ occurrence, occurrence ∈ bundle.term.siteOccurrences ∧
      occurrence.use.identity = entry.identity

def buildTypedSiteUseWitness {scope : Nat} (bundle : Bundle scope)
    (use : SiteUse) : Except String (TypedSiteUseWitness bundle use) := do
  match lookup : bundle.sites.find? (fun entry =>
      entry.identity == use.identity) with
  | none => .error s!"missing site sidecar entry: {repr use.identity}"
  | some entry =>
      if identityMatches : entry.identity = use.identity then
        if roleMatches : entry.role = use.role then
          match typed : SiteEntry.toSite use.scope entry with
          | .error message => .error message
          | .ok site =>
              have entryInTable : entry ∈ bundle.sites := by
                exact List.mem_of_find?_eq_some lookup
              pure {
                entry := entry
                entryInTable := entryInTable
                entryIdentity := identityMatches
                entryRole := roleMatches
                site := site
                typed := typed }
        else .error s!"site role conflicts with occurrence: {repr use.identity}"
      else .error s!"site lookup identity mismatch: {repr use.identity}"

def dedupSiteUses : List SiteUse → List SiteUse
  | [] => []
  | use :: rest =>
      let tail := dedupSiteUses rest
      if tail.contains use then tail else use :: tail

@[simp] theorem mem_dedupSiteUses (use : SiteUse) (uses : List SiteUse) :
    use ∈ dedupSiteUses uses ↔ use ∈ uses := by
  induction uses with
  | nil => simp [dedupSiteUses]
  | cons head tail ih =>
      simp only [dedupSiteUses]
      split <;> grind

theorem nodup_dedupSiteUses (uses : List SiteUse) :
    (dedupSiteUses uses).Nodup := by
  induction uses with
  | nil => simp [dedupSiteUses]
  | cons head tail ih =>
      simp only [dedupSiteUses]
      split
      · exact ih
      · constructor <;> grind

theorem Term.scope_le_of_mem_siteUses {scope : Nat} (term : Term scope)
    (use : SiteUse) (present : use ∈ term.siteUses) :
    scope ≤ use.scope := by
  revert use
  induction term using Term.rec
    (motive_2 := fun scope terms => ∀ use, use ∈ terms.siteUses →
      scope ≤ use.scope) <;>
    intros <;>
    simp_all [Term.siteUses, TermList.siteUses] <;>
    grind

def witnessFromResult {scope : Nat} {bundle : Bundle scope} :
    (result : List (Sigma fun use => TypedSiteUseWitness bundle use)) →
    (use : SiteUse) → use ∈ result.map Sigma.fst →
      TypedSiteUseWitness bundle use
  | [], use, present => by simp at present
  | ⟨candidate, witness⟩ :: rest, use, present =>
      if same : candidate = use then
        same ▸ witness
      else
        witnessFromResult rest use (by
          simp only [List.map_cons, List.mem_cons] at present
          rcases present with equal | later
          · exact False.elim (same equal.symm)
          · exact later)

theorem witnessFromResult_mem {scope : Nat} {bundle : Bundle scope}
    (result : List (Sigma fun use => TypedSiteUseWitness bundle use))
    (use : SiteUse) (present : use ∈ result.map Sigma.fst) :
    (⟨use, witnessFromResult result use present⟩ :
      Sigma fun use => TypedSiteUseWitness bundle use) ∈ result := by
  induction result with
  | nil => simp at present
  | cons head rest ih =>
      rcases head with ⟨candidate, witness⟩
      simp only [List.map_cons, List.mem_cons] at present
      simp only [witnessFromResult]
      split
      · next same =>
          subst candidate
          exact List.mem_cons_self
      · next different =>
          apply List.mem_cons_of_mem
          apply ih

def buildTypedUses {scope : Nat} (bundle : Bundle scope) :
    (uses : List SiteUse) →
      Except String (List (Sigma fun use => TypedSiteUseWitness bundle use))
  | [] => .ok []
  | use :: rest => do
      let witness ← buildTypedSiteUseWitness bundle use
      let tail ← buildTypedUses bundle rest
      pure (⟨use, witness⟩ :: tail)

theorem buildTypedUses_projection {scope : Nat} (bundle : Bundle scope) :
    ∀ (uses : List SiteUse)
      (result : List (Sigma fun use => TypedSiteUseWitness bundle use)),
      buildTypedUses bundle uses = .ok result →
        result.map Sigma.fst = uses
  | [], result, success => by
      simp only [buildTypedUses, Except.ok.injEq] at success
      subst result
      rfl
  | use :: rest, result, success => by
      simp only [buildTypedUses] at success
      cases first : buildTypedSiteUseWitness bundle use with
      | error message =>
          simp [first, bind, Except.bind] at success
      | ok witness =>
          rw [first] at success
          cases tailResult : buildTypedUses bundle rest with
          | error message =>
              simp [tailResult, bind, Except.bind] at success
          | ok tail =>
              rw [tailResult] at success
              cases success
              simp [buildTypedUses_projection bundle rest tail tailResult]

def buildTypedRootUses {scope : Nat} (bundle : Bundle scope) :
    Except String (List (Sigma fun use => TypedSiteUseWitness bundle use)) :=
  buildTypedUses bundle (dedupSiteUses bundle.term.siteUses)

structure OccurrenceProfilesWitness {scope : Nat} (bundle : Bundle scope)
    (result : List (Sigma fun use => TypedSiteUseWitness bundle use))
    (occurrences : List SiteOccurrence) : Type where
  agreement : ∀ occurrence, occurrence ∈ occurrences →
    ∃ present : occurrence.use ∈ result.map Sigma.fst,
      (witnessFromResult result occurrence.use present).entry.dependencies =
        occurrence.support

def checkOccurrenceProfiles {scope : Nat} (bundle : Bundle scope)
    (result : List (Sigma fun use => TypedSiteUseWitness bundle use)) :
    (occurrences : List SiteOccurrence) →
    (coverage : ∀ occurrence, occurrence ∈ occurrences →
      occurrence.use ∈ result.map Sigma.fst) →
      Except String (OccurrenceProfilesWitness bundle result occurrences)
  | [], _ => .ok { agreement := by simp }
  | occurrence :: rest, coverage =>
      let present := coverage occurrence (by simp)
      let selected := witnessFromResult result occurrence.use present
      if profilesMatch : selected.entry.dependencies = occurrence.support then
        match checkOccurrenceProfiles bundle result rest
            (fun candidate candidatePresent =>
              coverage candidate (by simp [candidatePresent])) with
        | .error message => .error message
        | .ok tail => .ok {
            agreement := by
              intro candidate candidatePresent
              simp only [List.mem_cons] at candidatePresent
              rcases candidatePresent with isHead | inRest
              · subst candidate
                exact ⟨present, profilesMatch⟩
              · exact tail.agreement candidate inRest }
      else Except.error (s!"site profile disagrees with term operands: " ++
        s!"{repr occurrence.use.identity}")

structure SiteTableUniqueWitness (sites : List SiteEntry) : Type where
  unique : (sites.map fun entry => entry.identity).Nodup

def checkSiteTableUnique : (sites : List SiteEntry) →
    Except String (SiteTableUniqueWitness sites)
  | [] => .ok { unique := by simp }
  | entry :: rest =>
      if duplicate : entry.identity ∈ rest.map (fun candidate =>
          candidate.identity) then
        .error s!"duplicate site sidecar entry: {repr entry.identity}"
      else
        match checkSiteTableUnique rest with
        | .error message => .error message
        | .ok restUnique =>
            .ok {
              unique := by
                simp only [List.map_cons, List.nodup_cons]
                exact ⟨duplicate, restUnique.unique⟩ }

structure SiteTableCoverageWitness (occurrences : List SiteOccurrence)
    (sites : List SiteEntry) : Type where
  covered : ∀ entry, entry ∈ sites →
    ∃ occurrence, occurrence ∈ occurrences ∧
      occurrence.use.identity = entry.identity

def checkSiteTableCovered (occurrences : List SiteOccurrence) :
    (sites : List SiteEntry) →
      Except String (SiteTableCoverageWitness occurrences sites)
  | [] => .ok { covered := by simp }
  | entry :: rest =>
      match lookup : occurrences.find? (fun occurrence =>
          occurrence.use.identity == entry.identity) with
      | none =>
          .error s!"unreachable site sidecar entry: {repr entry.identity}"
      | some occurrence =>
          match checkSiteTableCovered occurrences rest with
          | .error message => .error message
          | .ok restCovered =>
              .ok {
                covered := by
                  intro candidate present
                  simp only [List.mem_cons] at present
                  rcases present with isEntry | inRest
                  · subst candidate
                    refine ⟨occurrence, List.mem_of_find?_eq_some lookup, ?_⟩
                    have found := List.find?_some lookup
                    simpa using found
                  · exact restCovered.covered candidate inRest }

def Bundle.buildCoherence {scope : Nat} (bundle : Bundle scope) :
    Except String (BundleCoherence bundle) := do
  if bundle.version != 1 then
    .error s!"unsupported interchange version {bundle.version}"
  let tableUnique ← checkSiteTableUnique bundle.sites
  match rootsSuccess : buildTypedRootUses bundle with
  | .error message => .error message
  | .ok result =>
      let uses := result.map Sigma.fst
      have projection : uses = dedupSiteUses bundle.term.siteUses :=
        buildTypedUses_projection bundle
          (dedupSiteUses bundle.term.siteUses) result rootsSuccess
      have occurrenceCoverage : ∀ occurrence,
          occurrence ∈ bundle.term.siteOccurrences → occurrence.use ∈ uses := by
        intro occurrence occurrencePresent
        rw [projection]
        apply (mem_dedupSiteUses occurrence.use _).mpr
        rw [← bundle.term.siteOccurrences_uses]
        exact List.mem_map.mpr
          ⟨occurrence, occurrencePresent, rfl⟩
      let profiles ← checkOccurrenceProfiles bundle result
        bundle.term.siteOccurrences occurrenceCoverage
      match checkSiteTableCovered bundle.term.siteOccurrences bundle.sites with
      | .error message => .error message
      | .ok tableCovered =>
          .ok {
            uses := uses
            usesUnique := by
              rw [projection]
              exact nodup_dedupSiteUses _
            rootsCovered := by
              intro use present
              rw [projection]
              exact (mem_dedupSiteUses use _).mpr present
            scopeBound := by
              intro use present
              rw [projection] at present
              exact Term.scope_le_of_mem_siteUses bundle.term use
                ((mem_dedupSiteUses use _).mp present)
            witness := fun use present =>
              witnessFromResult result use present
            profileAgreement := profiles.agreement
            tableUnique := tableUnique.unique
            tableCovered := tableCovered.covered }

def Bundle.validateWithUses {scope : Nat} (bundle : Bundle scope) :
    Except String (List SiteUse) := do
  let coherence ← bundle.buildCoherence
  pure coherence.uses

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
