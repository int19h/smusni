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
  witness : ∀ use, use ∈ uses → TypedSiteUseWitness bundle use
  edgesClosed : ∀ use (present : use ∈ uses)
      (dependency : SerializedDependency) (_dependencyPresent :
        dependency ∈ (witness use present).entry.dependencies)
      (identity : SiteId),
      dependency = .site identity →
        ∃ child, child ∈ uses ∧ child.identity = identity ∧
          child.scope = use.scope
  tableUnique : (bundle.sites.map (fun entry => entry.identity)).Nodup
  tableCovered : ∀ entry, entry ∈ bundle.sites →
    ∃ use, use ∈ uses ∧ use.identity = entry.identity

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

def siteUseUniverse {scope : Nat} (bundle : Bundle scope) : List SiteUse :=
  let roots := bundle.term.siteUses
  let scopes := (roots.map (fun use => use.scope)).eraseDups
  let tableUses := scopes.flatMap fun occurrenceScope =>
    bundle.sites.map fun entry => {
      identity := entry.identity
      role := entry.role
      scope := occurrenceScope }
  dedupSiteUses (roots ++ tableUses)

def cSpikeDependencySiteUses (sites : List SiteEntry) (scope : Nat) :
    List SerializedDependency → Except String (List SiteUse)
  | [] => pure []
  | .site identity :: rest => do
      let some entry := sites.find? fun candidate =>
          candidate.identity == identity
        | .error s!"dangling site dependency: {repr identity}"
      pure ({ identity, role := entry.role, scope } ::
        (← cSpikeDependencySiteUses sites scope rest))
  | _ :: rest => cSpikeDependencySiteUses sites scope rest

theorem dependency_mem_cSpikeDependencySiteUses (sites : List SiteEntry)
    (scope : Nat) (dependencies : List SerializedDependency)
    (children : List SiteUse)
    (success : cSpikeDependencySiteUses sites scope dependencies = .ok children)
    (identity : SiteId) (present : .site identity ∈ dependencies) :
    ∃ child, child ∈ children ∧ child.identity = identity ∧
      child.scope = scope := by
  induction dependencies generalizing children with
  | nil => simp at present
  | cons dependency rest ih =>
      cases dependency with
      | bound index =>
          apply ih children
          · exact success
          · simpa using present
      | free freeIdentity =>
          apply ih children
          · exact success
          · simpa using present
      | site headIdentity =>
          simp only [cSpikeDependencySiteUses] at success
          cases lookup : sites.find? (fun candidate =>
              candidate.identity == headIdentity) with
          | none => simp [lookup] at success
          | some entry =>
              simp only [lookup, bind, Except.bind] at success
              cases tailResult : cSpikeDependencySiteUses sites scope rest with
              | error message => simp [tailResult] at success
              | ok tail =>
                  rw [tailResult] at success
                  let headChild : SiteUse :=
                    SiteUse.mk headIdentity entry.role scope
                  change Except.ok (headChild :: tail) =
                    Except.ok children at success
                  cases success
                  simp only [List.mem_cons] at present
                  rcases present with head | later
                  · cases head
                    exact ⟨headChild, by simp [headChild]⟩
                  · obtain ⟨child, childMem, childIdentity, childScope⟩ :=
                      ih tail tailResult later
                    exact ⟨child, by simp [childMem], childIdentity, childScope⟩

theorem scope_mem_of_mem_siteUseUniverse {scope : Nat}
    (bundle : Bundle scope) (current : SiteUse)
    (present : current ∈ siteUseUniverse bundle) :
    current.scope ∈
      (bundle.term.siteUses.map (fun use => use.scope)).eraseDups := by
  simp only [siteUseUniverse, mem_dedupSiteUses, List.mem_append] at present
  rcases present with root | table
  · have mapped : current.scope ∈
        bundle.term.siteUses.map (fun use => use.scope) :=
      List.mem_map.mpr ⟨current, root, rfl⟩
    simpa using mapped
  · simp only [List.mem_flatMap] at table
    rcases table with ⟨occurrenceScope, scopeMem, tableMem⟩
    have currentScope : current.scope = occurrenceScope := by
      simp only [List.mem_map] at tableMem
      rcases tableMem with ⟨entry, _entryMem, entryEq⟩
      subst current
      rfl
    rw [currentScope]
    exact scopeMem

theorem child_entry_of_mem_cSpikeDependencySiteUses
    (sites : List SiteEntry) (scope : Nat) :
    ∀ (dependencies : List SerializedDependency) (children : List SiteUse),
      cSpikeDependencySiteUses sites scope dependencies = .ok children →
      ∀ child, child ∈ children →
        ∃ entry, entry ∈ sites ∧
          child = SiteUse.mk entry.identity entry.role scope
  | [], children, success, child, present => by
      simp only [cSpikeDependencySiteUses, pure, Except.pure,
        Except.ok.injEq] at success
      subst success
      simp at present
  | .site identity :: rest, children, success, child, present => by
      simp only [cSpikeDependencySiteUses] at success
      cases lookup : sites.find? (fun candidate =>
          candidate.identity == identity) with
      | none => simp [lookup] at success
      | some entry =>
          rw [lookup] at success
          have identityEq : entry.identity = identity := by
            have found := List.find?_some lookup
            simpa using found
          cases recursive : cSpikeDependencySiteUses sites scope rest with
          | error message => simp [recursive, Functor.map, Except.map] at success
          | ok tail =>
              simp only [recursive, bind, Except.bind, pure, Except.pure,
                Except.ok.injEq] at success
              subst success
              simp only [List.mem_cons] at present
              rcases present with rfl | inTail
              · exact ⟨entry, List.mem_of_find?_eq_some lookup,
                  by simp [identityEq]⟩
              · exact child_entry_of_mem_cSpikeDependencySiteUses
                  sites scope rest tail recursive child inTail
  | .bound index :: rest, children, success, child, present => by
      simp only [cSpikeDependencySiteUses] at success
      exact child_entry_of_mem_cSpikeDependencySiteUses
        sites scope rest children success child present
  | .free identity :: rest, children, success, child, present => by
      simp only [cSpikeDependencySiteUses] at success
      exact child_entry_of_mem_cSpikeDependencySiteUses
        sites scope rest children success child present

theorem child_mem_siteUseUniverse {scope : Nat} (bundle : Bundle scope)
    (current : SiteUse) (currentMem : current ∈ siteUseUniverse bundle)
    (dependencies : List SerializedDependency) (children : List SiteUse)
    (success : cSpikeDependencySiteUses bundle.sites current.scope
      dependencies = .ok children)
    (child : SiteUse) (present : child ∈ children) :
    child ∈ siteUseUniverse bundle := by
  obtain ⟨entry, entryMem, rfl⟩ :=
    child_entry_of_mem_cSpikeDependencySiteUses bundle.sites
      current.scope dependencies children success child present
  have scopeMem :=
    scope_mem_of_mem_siteUseUniverse bundle current currentMem
  simp only [siteUseUniverse, mem_dedupSiteUses, List.mem_append,
    List.mem_flatMap, List.mem_map]
  exact Or.inr ⟨current.scope, scopeMem, entry, entryMem, rfl⟩

def cSpikeEnqueue (seen pending : List SiteUse) :
    List SiteUse → List SiteUse
  | [] => pending
  | use :: rest =>
      if seen.contains use || pending.contains use then
        cSpikeEnqueue seen pending rest
      else cSpikeEnqueue seen (pending ++ [use]) rest

theorem mem_cSpikeEnqueue_of_mem_pending (seen pending additions : List SiteUse)
    (use : SiteUse) (present : use ∈ pending) :
    use ∈ cSpikeEnqueue seen pending additions := by
  induction additions generalizing pending with
  | nil => exact present
  | cons head tail ih =>
      simp only [cSpikeEnqueue]
      split
      · exact ih pending present
      · exact ih (pending ++ [head]) (List.mem_append_left _ present)

theorem mem_cSpikeEnqueue_iff (blocked pending additions : List SiteUse)
    (use : SiteUse) :
    use ∈ cSpikeEnqueue blocked pending additions ↔
      use ∈ pending ∨ (use ∈ additions ∧ use ∉ blocked) := by
  induction additions generalizing pending with
  | nil => simp [cSpikeEnqueue]
  | cons head tail ih =>
      simp only [cSpikeEnqueue]
      split <;> simp_all <;> grind

theorem nodup_cSpikeEnqueue (blocked pending additions : List SiteUse)
    (pendingUnique : pending.Nodup) :
    (cSpikeEnqueue blocked pending additions).Nodup := by
  induction additions generalizing pending with
  | nil => exact pendingUnique
  | cons head tail ih =>
      simp only [cSpikeEnqueue]
      split
      · exact ih pending pendingUnique
      · apply ih (pending ++ [head])
        apply List.nodup_append.mpr
        refine ⟨pendingUnique, by simp, ?_⟩
        intro a inPending b inSingleton
        simp only [List.mem_singleton] at inSingleton
        subst b
        intro equal
        subst a
        exact (by simp_all)

structure ClosureTraversalInvariant {scope : Nat} (bundle : Bundle scope)
    (universeUses unseen pending : List SiteUse)
    (seen : List (Sigma fun use => TypedSiteUseWitness bundle use)) : Prop where
  unseenUnique : unseen.Nodup
  pendingUnique : pending.Nodup
  seenUnique : (seen.map Sigma.fst).Nodup
  pendingInUnseen : ∀ use, use ∈ pending → use ∈ unseen
  seenDisjointUnseen : ∀ use, use ∈ seen.map Sigma.fst → use ∉ unseen
  partition : ∀ use, use ∈ universeUses ↔
    use ∈ unseen ∨ use ∈ seen.map Sigma.fst
  childrenAccounted : ∀ use witness,
    (⟨use, witness⟩ : Sigma fun use => TypedSiteUseWitness bundle use) ∈ seen →
    ∀ identity, .site identity ∈ witness.entry.dependencies →
      ∃ child,
        (child ∈ pending ∨ child ∈ seen.map Sigma.fst) ∧
        child.identity = identity ∧ child.scope = use.scope

theorem termRoot_mem_siteUseUniverse {scope : Nat} (bundle : Bundle scope)
    (use : SiteUse) (present : use ∈ bundle.term.siteUses) :
    use ∈ siteUseUniverse bundle := by
  simp [siteUseUniverse, present]

theorem initialClosureTraversalInvariant {scope : Nat} (bundle : Bundle scope) :
    ClosureTraversalInvariant bundle (siteUseUniverse bundle)
      (siteUseUniverse bundle) (dedupSiteUses bundle.term.siteUses) [] := by
  refine {
    unseenUnique := nodup_dedupSiteUses _
    pendingUnique := nodup_dedupSiteUses _
    seenUnique := by simp
    pendingInUnseen := ?_
    seenDisjointUnseen := by simp
    partition := by simp
    childrenAccounted := by simp }
  intro use present
  exact termRoot_mem_siteUseUniverse bundle use (by simpa using present)

theorem closureTraversalInvariant_step {scope : Nat}
    (bundle : Bundle scope) (unseen : List SiteUse)
    (current : SiteUse) (pending : List SiteUse)
    (seen : List (Sigma fun use => TypedSiteUseWitness bundle use))
    (invariant : ClosureTraversalInvariant bundle (siteUseUniverse bundle)
      unseen (current :: pending) seen)
    (witness : TypedSiteUseWitness bundle current)
    (children : List SiteUse)
    (childrenSuccess : cSpikeDependencySiteUses bundle.sites current.scope
      witness.entry.dependencies = .ok children) :
    ClosureTraversalInvariant bundle (siteUseUniverse bundle)
      (unseen.erase current)
      (cSpikeEnqueue (current :: seen.map Sigma.fst) pending children)
      (⟨current, witness⟩ :: seen) := by
  have currentInUnseen : current ∈ unseen :=
    invariant.pendingInUnseen current (by simp)
  have currentInUniverse : current ∈ siteUseUniverse bundle :=
    (invariant.partition current).mpr (Or.inl currentInUnseen)
  have pendingFacts := List.nodup_cons.mp invariant.pendingUnique
  have currentNotPending : current ∉ pending := pendingFacts.1
  have pendingUnique : pending.Nodup := pendingFacts.2
  have currentNotSeen : current ∉ seen.map Sigma.fst := by
    intro currentSeen
    exact invariant.seenDisjointUnseen current currentSeen currentInUnseen
  refine {
    unseenUnique := invariant.unseenUnique.erase current
    pendingUnique := nodup_cSpikeEnqueue _ _ _ pendingUnique
    seenUnique := by
      simp only [List.map_cons]
      exact List.nodup_cons.mpr ⟨currentNotSeen, invariant.seenUnique⟩
    pendingInUnseen := ?_
    seenDisjointUnseen := ?_
    partition := ?_
    childrenAccounted := ?_ }
  · intro use queuedMem
    rcases (mem_cSpikeEnqueue_iff
      (current :: seen.map Sigma.fst) pending children use).mp queuedMem with
      inPending | ⟨inChildren, notBlocked⟩
    · have oldUnseen := invariant.pendingInUnseen use (by simp [inPending])
      have notCurrent : use ≠ current := by
        intro equal
        subst use
        exact currentNotPending inPending
      exact invariant.unseenUnique.mem_erase_iff.mpr
        ⟨notCurrent, oldUnseen⟩
    · have inUniverse := child_mem_siteUseUniverse bundle current
        currentInUniverse witness.entry.dependencies children childrenSuccess
        use inChildren
      rcases (invariant.partition use).mp inUniverse with
        inUnseen | inSeen
      · have notCurrent : use ≠ current := by
          intro equal
          subst use
          exact notBlocked (by simp)
        exact invariant.unseenUnique.mem_erase_iff.mpr
          ⟨notCurrent, inUnseen⟩
      · exact False.elim (notBlocked (by simp [inSeen]))
  · intro use inNewSeen inNewUnseen
    simp only [List.map_cons, List.mem_cons] at inNewSeen
    rcases inNewSeen with isCurrent | inOldSeen
    · subst use
      exact invariant.unseenUnique.not_mem_erase inNewUnseen
    · exact invariant.seenDisjointUnseen use inOldSeen
        (List.mem_of_mem_erase inNewUnseen)
  · intro use
    rw [invariant.partition use]
    simp only [List.map_cons, List.mem_cons]
    constructor
    · intro oldState
      rcases oldState with inUnseen | inSeen
      · by_cases isCurrent : use = current
        · exact Or.inr (Or.inl isCurrent)
        · exact Or.inl <|
            invariant.unseenUnique.mem_erase_iff.mpr
              ⟨isCurrent, inUnseen⟩
      · exact Or.inr (Or.inr inSeen)
    · intro newState
      rcases newState with inErased | isCurrentOrSeen
      · exact Or.inl (List.mem_of_mem_erase inErased)
      · rcases isCurrentOrSeen with isCurrent | inSeen
        · subst use
          exact Or.inl currentInUnseen
        · exact Or.inr inSeen
  · intro use useWitness inNewSeen identity dependencyPresent
    simp only [List.mem_cons] at inNewSeen
    rcases inNewSeen with isCurrent | inOldSeen
    · cases isCurrent
      obtain ⟨child, childMem, childIdentity, childScope⟩ :=
        dependency_mem_cSpikeDependencySiteUses bundle.sites current.scope
          witness.entry.dependencies children childrenSuccess identity
          dependencyPresent
      refine ⟨child, ?_, childIdentity, childScope⟩
      by_cases blocked : child ∈ current :: seen.map Sigma.fst
      · exact Or.inr (by simpa using blocked)
      · exact Or.inl <| (mem_cSpikeEnqueue_iff
          (current :: seen.map Sigma.fst) pending children child).mpr
            (Or.inr ⟨childMem, blocked⟩)
    · obtain ⟨child, childState, childIdentity, childScope⟩ :=
        invariant.childrenAccounted use useWitness inOldSeen identity
          dependencyPresent
      refine ⟨child, ?_, childIdentity, childScope⟩
      rcases childState with inOldPending | inOldSeenUses
      · simp only [List.mem_cons] at inOldPending
        rcases inOldPending with isCurrent | inPending
        · exact Or.inr (by simp [isCurrent])
        · exact Or.inl <| mem_cSpikeEnqueue_of_mem_pending
            (current :: seen.map Sigma.fst) pending children child inPending
      · exact Or.inr (by simp [inOldSeenUses])

def buildClosureUsesLoop {scope : Nat} (bundle : Bundle scope) :
    (unseen pending : List SiteUse) →
    (seen : List (Sigma fun use => TypedSiteUseWitness bundle use)) →
    Except String (List (Sigma fun use => TypedSiteUseWitness bundle use))
  | _, [], seen => pure seen
  | unseen, use :: pending, seen =>
      if _available : unseen.contains use then
        match buildTypedSiteUseWitness bundle use with
        | .error message => .error message
        | .ok witness =>
            match cSpikeDependencySiteUses bundle.sites use.scope
                witness.entry.dependencies with
            | .error message => .error message
            | .ok children =>
                let queued := cSpikeEnqueue
                  (use :: seen.map Sigma.fst) pending children
                buildClosureUsesLoop bundle (unseen.erase use) queued
                  (⟨use, witness⟩ :: seen)
      else .error s!"closure queue invariant violated: {repr use}"
termination_by unseen pending _ => (unseen.length, pending.length)
decreasing_by
  · have member : use ∈ unseen := List.contains_iff_mem.mp _available
    have shorter : (unseen.erase use).length < unseen.length := by
      have positive := List.length_pos_of_mem member
      rw [List.length_erase_of_mem member]
      omega
    exact Prod.Lex.left queued.length (use :: pending).length shorter

def buildTypedClosureUses {scope : Nat} (bundle : Bundle scope) :
    Except String (List (Sigma fun use => TypedSiteUseWitness bundle use)) :=
  let roots := dedupSiteUses bundle.term.siteUses
  buildClosureUsesLoop bundle (siteUseUniverse bundle) roots []

theorem buildClosureUsesLoop_success {scope : Nat}
    (bundle : Bundle scope) (unseen pending : List SiteUse)
    (seen result : List (Sigma fun use => TypedSiteUseWitness bundle use))
    (invariant : ClosureTraversalInvariant bundle (siteUseUniverse bundle)
      unseen pending seen)
    (success : buildClosureUsesLoop bundle unseen pending seen = .ok result) :
    (∃ finalUnseen, ClosureTraversalInvariant bundle (siteUseUniverse bundle)
      finalUnseen [] result) ∧
    (∀ use, use ∈ pending ∨ use ∈ seen.map Sigma.fst →
      use ∈ result.map Sigma.fst) := by
  fun_induction buildClosureUsesLoop <;> simp_all
  case case1 unseen seen =>
    cases success
    constructor
    · exact ⟨unseen, invariant⟩
    · intro entry present
      exact ⟨entry, present, rfl⟩
  case case4 unseen current pending seen witness children queued available
      witnessEq childrenEq ih =>
    have nextInvariant := closureTraversalInvariant_step bundle unseen current
      pending seen invariant witness children childrenEq
    have queuedInvariant : ClosureTraversalInvariant bundle
        (siteUseUniverse bundle) (unseen.erase current) queued
        (⟨current, witness⟩ :: seen) := by
      simpa [queued] using nextInvariant
    have recursiveSuccess :
        buildClosureUsesLoop bundle (unseen.erase current) queued
          (⟨current, witness⟩ :: seen) = .ok result := by
      simpa [queued, List.pmap_eq_map_attach] using success
    obtain ⟨terminal, preserved⟩ := ih queuedInvariant recursiveSuccess
    constructor
    · exact terminal
    intro use present
    apply preserved use
    rcases present with pendingOrCurrent | alreadySeen
    · rcases pendingOrCurrent with isCurrent | inPending
      · exact Or.inr (Or.inl isCurrent)
      · exact Or.inl <|
          mem_cSpikeEnqueue_of_mem_pending _ _ _ use inPending
    · exact Or.inr (Or.inr alreadySeen)

theorem buildClosureUsesLoop_preserves_invariant {scope : Nat}
    (bundle : Bundle scope) (unseen pending : List SiteUse)
    (seen result : List (Sigma fun use => TypedSiteUseWitness bundle use))
    (invariant : ClosureTraversalInvariant bundle (siteUseUniverse bundle)
      unseen pending seen)
    (success : buildClosureUsesLoop bundle unseen pending seen = .ok result) :
    ∃ finalUnseen, ClosureTraversalInvariant bundle (siteUseUniverse bundle)
      finalUnseen [] result :=
  (buildClosureUsesLoop_success bundle unseen pending seen result invariant
    success).1

theorem buildClosureUsesLoop_preserves_pending {scope : Nat}
    (bundle : Bundle scope) (unseen pending : List SiteUse)
    (seen result : List (Sigma fun use => TypedSiteUseWitness bundle use))
    (invariant : ClosureTraversalInvariant bundle (siteUseUniverse bundle)
      unseen pending seen)
    (success : buildClosureUsesLoop bundle unseen pending seen = .ok result) :
    ∀ use, use ∈ pending ∨ use ∈ seen.map Sigma.fst →
      use ∈ result.map Sigma.fst :=
  (buildClosureUsesLoop_success bundle unseen pending seen result invariant
    success).2

theorem buildTypedClosureUses_rootsCovered {scope : Nat}
    (bundle : Bundle scope)
    (result : List (Sigma fun use => TypedSiteUseWitness bundle use))
    (success : buildTypedClosureUses bundle = .ok result) :
    ∀ use, use ∈ bundle.term.siteUses → use ∈ result.map Sigma.fst := by
  intro use present
  apply buildClosureUsesLoop_preserves_pending bundle
    (siteUseUniverse bundle) (dedupSiteUses bundle.term.siteUses) [] result
    (initialClosureTraversalInvariant bundle) success use
  exact Or.inl (by simpa using present)

theorem buildTypedClosureUses_terminalInvariant {scope : Nat}
    (bundle : Bundle scope)
    (result : List (Sigma fun use => TypedSiteUseWitness bundle use))
    (success : buildTypedClosureUses bundle = .ok result) :
    ∃ finalUnseen, ClosureTraversalInvariant bundle (siteUseUniverse bundle)
      finalUnseen [] result := by
  apply buildClosureUsesLoop_preserves_invariant bundle
    (siteUseUniverse bundle) (dedupSiteUses bundle.term.siteUses) [] result
    (initialClosureTraversalInvariant bundle)
  exact success

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

structure SiteTableCoverageWitness (uses : List SiteUse)
    (sites : List SiteEntry) : Type where
  covered : ∀ entry, entry ∈ sites →
    ∃ use, use ∈ uses ∧ use.identity = entry.identity

def checkSiteTableCovered (uses : List SiteUse) :
    (sites : List SiteEntry) →
      Except String (SiteTableCoverageWitness uses sites)
  | [] => .ok { covered := by simp }
  | entry :: rest =>
      match lookup : uses.find? (fun use => use.identity == entry.identity) with
      | none =>
          .error s!"unreachable site sidecar entry: {repr entry.identity}"
      | some use =>
          match checkSiteTableCovered uses rest with
          | .error message => .error message
          | .ok restCovered =>
              .ok {
                covered := by
                  intro candidate present
                  simp only [List.mem_cons] at present
                  rcases present with isEntry | inRest
                  · subst candidate
                    refine ⟨use, List.mem_of_find?_eq_some lookup, ?_⟩
                    have found := List.find?_some lookup
                    simpa using found
                  · exact restCovered.covered candidate inRest }

def Bundle.buildCoherence {scope : Nat} (bundle : Bundle scope) :
    Except String (BundleCoherence bundle) := do
  if bundle.version != 1 then
    .error s!"unsupported interchange version {bundle.version}"
  let tableUnique ← checkSiteTableUnique bundle.sites
  match closureSuccess : buildTypedClosureUses bundle with
  | .error message => .error message
  | .ok result =>
      let uses := result.map Sigma.fst
      match checkSiteTableCovered uses bundle.sites with
      | .error message => .error message
      | .ok tableCovered =>
          have terminal := buildTypedClosureUses_terminalInvariant bundle result
            closureSuccess
          .ok {
            uses := uses
            usesUnique := by
              obtain ⟨_finalUnseen, finalInvariant⟩ := terminal
              exact finalInvariant.seenUnique
            rootsCovered := by
              exact buildTypedClosureUses_rootsCovered bundle result
                closureSuccess
            witness := fun use present =>
              witnessFromResult result use present
            edgesClosed := by
              intro use present dependency dependencyPresent identity isSite
              subst dependency
              obtain ⟨finalUnseen, finalInvariant⟩ := terminal
              obtain ⟨child, childState, childIdentity, childScope⟩ :=
                finalInvariant.childrenAccounted use
                  (witnessFromResult result use present)
                  (witnessFromResult_mem result use present)
                  identity dependencyPresent
              rcases childState with inPending | inResult
              · simp at inPending
              · exact ⟨child, inResult, childIdentity, childScope⟩
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
