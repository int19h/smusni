import SmusniPilot.InterchangeLaws

namespace SmusniPilot

def entityTy : Ty := .named .sortEntity []

def writtenSite {scope : Nat} (ordinal : Nat) (role : SiteRole)
    (dependencies : List (Dependency scope) := []) : Site scope :=
  { identity := {
      document := "examples"
      occurrence := ordinal
      expansionRole := match role with
        | .context => "written-context"
        | .vague => "written-vague" }
    role
    dependencies }

def eraseNamedIdentity (_binderSpelling : String) : Term 0 :=
  .lambda entityTy (.bound 0)

theorem binder_spelling_is_nonsemantic (first second : String) :
    eraseNamedIdentity first = eraseNamedIdentity second := rfl

def sharedSiteFunction : Term 0 :=
  .lambda entityTy
    (.context (writtenSite (scope := 0) 0 .context).identity .nil)

def sharedSiteUsedTwice : Term 0 :=
  .primitive .and <|
    .positional (.apply sharedSiteFunction (.positional (.natural 1) .nil)) <|
    .positional (.apply sharedSiteFunction (.positional (.natural 2) .nil)) .nil

def copiedSites : Term 0 :=
  .primitive .and <|
    .positional
      (.context (writtenSite (scope := 0) 0 .context).identity .nil) <|
    .positional
      (.context (writtenSite (scope := 0) 1 .context).identity .nil) .nil

theorem sharing_preserves_one_site_identity :
    sharedSiteUsedTwice.siteIds =
      [(writtenSite (scope := 0) 0 .context).identity,
       (writtenSite (scope := 0) 0 .context).identity] :=
  rfl

theorem copying_mints_distinct_site_identities :
    copiedSites.siteIds =
      [(writtenSite (scope := 0) 0 .context).identity,
       (writtenSite (scope := 0) 1 .context).identity] :=
  rfl

def dependentSite : Site 1 := writtenSite 7 .context [.bound 0]

def replacementFree : FreeId := { domain := "$replacement", serial := 0 }

theorem dependency_substitution_is_capture_avoiding :
    dependentSite.substitute (fun _ => .free replacementFree) =
      (writtenSite 7 .context [.free replacementFree] : Site 0) :=
  rfl

def exampleBundle : Interchange.Bundle 0 :=
  { version := 1
    term := copiedSites
    sites := [
      { identity := (writtenSite (scope := 0) 0 .context).identity
        role := .context
        dependencies := [] },
      { identity := (writtenSite (scope := 0) 1 .context).identity
        role := .context
        dependencies := [] }
    ]
    sourceMap := [
      { document := "examples"
        ordinal := 0
        binderSpellings := ["$display"]
        sourceOrder := [0, 1]
        line := some 1
        column := some 1 }
    ] }

example :
    (Interchange.BundleDatum.ofBundle exampleBundle).toBundle = exampleBundle :=
  Interchange.BundleDatum.toBundle_ofBundle exampleBundle

def generatedCoreTerms : List (Term 0) :=
  let primitiveTerms := FirstOrderPrimitive.all.zipIdx.map fun (operator, index) =>
    .primitive operator (.positional (.natural index) .nil)
  let siteTerms := (List.range 128).map fun ordinal =>
    .context (writtenSite (scope := 0) ordinal .context).identity
      (.positional (.natural ordinal) .nil)
  let binderTerms := (List.range 64).map fun literal =>
    .lambda entityTy (.apply (.bound 0) (.positional (.natural literal) .nil))
  primitiveTerms ++ siteTerms ++ binderTerms

def generatedBundle (term : Term 0) : Interchange.Bundle 0 :=
  let sites := term.siteIds.eraseDups.map fun identity =>
    { identity, role := .context, dependencies := [] }
  { version := 1, term, sites, sourceMap := [] }

def runGeneratedRoundTrips : IO Nat := do
  for (term, index) in generatedCoreTerms.zipIdx do
    let bundle := generatedBundle term
    let encoded := Interchange.Bundle.encode bundle
    let decoded ← IO.ofExcept (Interchange.Bundle.decode 0 encoded)
    if !(Interchange.Bundle.encode decoded == encoded) then
      throw <| IO.userError s!"generated bundle round trip failed at {index}"
    let canonical := Interchange.renderCanonicalTerm term
    let decodedTerm ← IO.ofExcept
      (Interchange.decodeCanonicalTerm 0 canonical)
    if Interchange.renderCanonicalTerm decodedTerm != canonical then
      throw <| IO.userError s!"generated canonical term round trip failed at {index}"
  pure generatedCoreTerms.length

def runLocalGates : IO Unit := do
  let source := "{λ ; comment\n [$x :: Entity] \"text\"}"
  let parsed ← IO.ofExcept (SExpr.parse source)
  let reparsed ← IO.ofExcept (SExpr.parse parsed.render)
  if !(reparsed == parsed) then
    throw <| IO.userError "generic S-expression canonical round trip failed"
  let encoded := Interchange.Bundle.encode exampleBundle
  let decoded ← IO.ofExcept (Interchange.Bundle.decode 0 encoded)
  if !(Interchange.Bundle.encode decoded == encoded) then
    throw <| IO.userError "bundle textual round trip failed"
  if decoded.term.siteIds != exampleBundle.term.siteIds then
    throw <| IO.userError "bundle textual site round trip failed"
  if sharedSiteUsedTwice.siteIds.head? != sharedSiteUsedTwice.siteIds.getLast? then
    throw <| IO.userError "shared site identity was rekeyed"
  if copiedSites.siteIds.head? == copiedSites.siteIds.getLast? then
    throw <| IO.userError "copied occurrences reused a site identity"
  let missing := { exampleBundle with sites := exampleBundle.sites.drop 1 }
  if missing.validate.isOk then
    throw <| IO.userError "missing site sidecar entry was accepted"
  let extraEntry : SiteEntry :=
    { identity :=
        { document := "extra"
          occurrence := 99
          expansionRole := "written-context" }
      role := .context, dependencies := [] }
  let extra := { exampleBundle with sites := exampleBundle.sites ++ [extraEntry] }
  if extra.validate.isOk then
    throw <| IO.userError "extra site sidecar entry was accepted"
  let duplicate :=
    { exampleBundle with sites := exampleBundle.sites ++ [exampleBundle.sites.head!] }
  if duplicate.validate.isOk then
    throw <| IO.userError "duplicate site sidecar entry was accepted"
  let conflictingEntry :=
    { exampleBundle.sites.head! with role := SiteRole.vague }
  let conflict :=
    { exampleBundle with sites := conflictingEntry :: exampleBundle.sites.tail }
  if conflict.validate.isOk then
    throw <| IO.userError "conflicting site role was accepted"
  let scopedId : SiteId :=
    { document := "scope"
      occurrence := 0
      expansionRole := "written-context" }
  let scopedBundle : Interchange.Bundle 0 :=
    { version := 1
      term := .context scopedId .nil
      sites := [
        { identity := scopedId
          role := .context
          dependencies := [.bound 0] }
      ]
      sourceMap := [] }
  if scopedBundle.validate.isOk then
    throw <| IO.userError "out-of-scope site dependency was accepted"
  let alphaX := SurfaceTerm.ofSExpr
    (← IO.ofExcept (SExpr.parse "(λ ($x :: Entity) $x)"))
  let alphaY := SurfaceTerm.ofSExpr
    (← IO.ofExcept (SExpr.parse "(λ ($renamed :: Entity) $renamed)"))
  let bundleX ← IO.ofExcept (Interchange.Bundle.ofSurface "alpha" alphaX)
  let bundleY ← IO.ofExcept (Interchange.Bundle.ofSurface "alpha" alphaY)
  if Interchange.renderCanonicalTerm bundleX.term !=
      Interchange.renderCanonicalTerm bundleY.term then
    throw <| IO.userError "alpha-renamed binders changed CoreTerm"
  if bundleX.sourceMap.head?.bind (·.binderSpellings.head?) ==
      bundleY.sourceMap.head?.bind (·.binderSpellings.head?) then
    throw <| IO.userError "source map discarded binder spelling provenance"

end SmusniPilot
