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
  .lambda entityTy (.context (writtenSite 0 .context) .nil)

def sharedSiteUsedTwice : Term 0 :=
  .primitive .and <|
    .cons (.apply sharedSiteFunction (.natural 1)) <|
    .cons (.apply sharedSiteFunction (.natural 2)) .nil

def copiedSites : Term 0 :=
  .primitive .and <|
    .cons (.context (writtenSite 0 .context) .nil) <|
    .cons (.context (writtenSite 1 .context) .nil) .nil

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

def dependentSiteTerm : Term 1 :=
  .context (writtenSite 7 .context [.bound 0]) .nil

def replacementFree : FreeId := { domain := "$replacement", serial := 0 }

theorem dependency_substitution_is_capture_avoiding :
    dependentSiteTerm.substitute (fun _ => .free replacementFree) =
      (.context (writtenSite 7 .context [.free replacementFree]) .nil : Term 0) :=
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
  let primitiveTerms := Primitive.all.zipIdx.map fun (operator, index) =>
    .primitive operator (.cons (.natural index) .nil)
  let siteTerms := (List.range 128).map fun ordinal =>
    .context (writtenSite ordinal .context) (.cons (.natural ordinal) .nil)
  let binderTerms := (List.range 64).map fun literal =>
    .lambda entityTy (.apply (.bound 0) (.natural literal))
  primitiveTerms ++ siteTerms ++ binderTerms

def runGeneratedRoundTrips : IO Nat := do
  for (term, index) in generatedCoreTerms.zipIdx do
    let bundle : Interchange.Bundle 0 :=
      { version := 1, term, sites := [], sourceMap := [] }
    let encoded := Interchange.Bundle.encode bundle
    let decoded ← IO.ofExcept (Interchange.Bundle.decode 0 encoded)
    if !(Interchange.Bundle.encode decoded == encoded) then
      throw <| IO.userError s!"generated bundle round trip failed at {index}"
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
  let alphaX := SurfaceTerm.ofSExpr
    (← IO.ofExcept (SExpr.parse "(λ ($x :: Entity) $x)"))
  let alphaY := SurfaceTerm.ofSExpr
    (← IO.ofExcept (SExpr.parse "(λ ($renamed :: Entity) $renamed)"))
  let bundleX ← IO.ofExcept (Interchange.Bundle.ofSurface "alpha" alphaX)
  let bundleY ← IO.ofExcept (Interchange.Bundle.ofSurface "alpha" alphaY)
  if !(Interchange.encodeTerm bundleX.term == Interchange.encodeTerm bundleY.term) then
    throw <| IO.userError "alpha-renamed binders changed CoreTerm"
  if bundleX.sourceMap.head?.bind (·.binderSpellings.head?) ==
      bundleY.sourceMap.head?.bind (·.binderSpellings.head?) then
    throw <| IO.userError "source map discarded binder spelling provenance"

end SmusniPilot
