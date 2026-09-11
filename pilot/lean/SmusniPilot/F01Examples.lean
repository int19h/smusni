import SmusniPilot.M2Cases
import SmusniPilot.BindingLaws
import SmusniPilot.InterchangeLaws

namespace SmusniPilot
namespace F01

open M2

def form (source := "$source") (content := "($P $x)")
    (continuation := "(Do (Perform Host (Assert (Bind [$y :: Referents Entity] $read ($P $y)))))")
    (role := "Host") (reference := "Referents Entity")
    (readType := "RefComp (Referents Entity)")
    (occurrenceType := "ActOccurrence Assertion") (force := "Assert") : String :=
  "{PerformSource " ++ role ++ " [$x :: " ++ reference ++ "] " ++ source ++
    " (" ++ force ++ " " ++ content ++ ") [$read :: " ++ readType ++
    "] [$o :: " ++ occurrenceType ++ "] " ++ continuation ++ "}"

def close (body : String) : String :=
  "{λ [[$source :: RefComp (Referents Entity)] [$P :: Fn ((Referents Entity)) Content]] " ++ body ++ "}"

def decode (text : String) : Except String (Term 0 × DecodeState) := do
  decodeSourceCore "f01-control" [] Environment.empty (SurfaceTerm.ofSExpr (← SExpr.parse text))

def expectRejected (text : String) : IO Unit := do
  match decode text with
  | .error _ => pure ()
  | .ok (term, _) =>
      if (synth Environment.empty term).isOk then
        throw <| IO.userError s!"F01 accepted malformed or ill-typed control: {text}"

def expectTyped (text : String) : IO (Term 0) := do
  let (term, _) ← IO.ofExcept (decode text)
  let result ← IO.ofExcept ((synth Environment.empty term).mapError (fun e => e.detail))
  if !result.trace.contains .f01TPerformSource ||
      !result.trace.all typingRuleImplemented then
    throw <| IO.userError "F01 typing path lacks its explicit rule or leaves the proved typing domain"
  let encoded := Interchange.renderCanonicalTerm term
  let roundtrip ← IO.ofExcept (Interchange.decodeCanonicalTerm 0 encoded)
  if Interchange.renderCanonicalTerm roundtrip != encoded then
    throw <| IO.userError "F01 interchange roundtrip changed scoped arms"
  pure term

-- Compile-time generic laws apply to arbitrary arms, not just the controls.
example {n : Nat} (r : Ty) (s : Term n) (c : Term (n+1)) (d : Term (n+2)) :
    (Term.performSource r s c d).rename (fun i => i) = .performSource r s c d :=
  Term.rename_identity _

example {n : Nat} (r : Ty) (s : Term n) (c : Term (n+1)) (d : Term (n+2)) :
    (Interchange.TermDatum.ofTerm (.performSource r s c d)).toTerm =
      .performSource r s c d := Interchange.TermDatum.toTerm_ofTerm _

def run : IO Unit := do
  let baseline ← expectTyped (close (form))
  let omitted ← expectTyped (close (form (role := "")))
  if Interchange.renderCanonicalTerm baseline != Interchange.renderCanonicalTerm omitted then
    throw <| IO.userError "F01 Host shorthand changed the core"
  let renamed := (close (form)).replace "$x" "$first" |>.replace "$read" "$again" |>.replace "$o ::" "$occ ::"
  let renamed ← expectTyped renamed
  if Interchange.renderCanonicalTerm renamed != Interchange.renderCanonicalTerm baseline then
    throw <| IO.userError "F01 alpha-renaming changed binding"
  let _ ← expectTyped (close (form (source := "(Refer $P)")))
  let _ ← expectTyped (close (form (source := "(Context)") (content := "($P Speaker)")
    (continuation := "(Do (Perform (Assert ($P Speaker))))") (reference := "Referents (Set Entity)")
    (readType := "RefComp (Referents (Set Entity))")))
  let _ ← expectTyped (close (form (continuation := form (source := "$read"))))
  let _ ← expectTyped ("{λ [[$x :: RefComp (Referents Entity)] [$P :: Fn ((Referents Entity)) Content]] " ++
    form (source := "$x") ++ "}")
  let negatives := [
    form (role := "AttachedDisplay"), form (role := "$source"),
    form (force := "Ask"), form (reference := "Entity"),
    form (readType := "RefComp Entity"), form (occurrenceType := "ActOccurrence Question"),
    form (source := "$x"), form (source := "$read"), form (source := "$o"),
    form (source := "(Context $x)"), form (source := "(Context $read)"),
    form (source := "(Context $o)"),
    form (source := "(Context)") (content := "($P Speaker)")
      (continuation := "(Do (Perform (Assert ($P Speaker))))") (reference := "Referents (Set Content)")
      (readType := "RefComp (Referents (Set Content))"),
    form (content := "(Bind [$z :: Referents Entity] (Context $read) ($P $z))"),
    form (content := "(Bind [$z :: Referents Entity] (Context $o) ($P $z))"),
    form (source := "Speaker"), form (content := "$read"), form (content := "$o"),
    form (content := "Speaker"), form (continuation := "(Do (Perform (Assert ($P $x))))"),
    form (continuation := "($P Speaker)"),
    form (continuation := "(Do (Perform 3 (Assert ($P Speaker))))"),
    (form).replace "[$read ::" "[$o ::", (form).replace "(Assert ($P $x))" "(Assert ($P $x) ($P $x))",
    (form).replace "PerformSource Host" "PerformSource Host Host"]
  for text in negatives do expectRejected (close text)

  -- Source-facing normalization consumes declared types, not Assert spelling.
  -- The structural M1 decoder and deep synth remain canonical-only APIs.
  for act in ["$A", "(Assert ($P Speaker))",
      "((λ [$saved :: Act Assertion] $saved) $A)",
      "((λ [$saved :: Act Assertion] $saved) (Assert ($P Speaker)))"] do
    let source := fun d => "{λ [$A :: Act Assertion] " ++ close (form (continuation := d)) ++ "}"
    let variants := [source act, source ("(Do " ++ act ++ ")"),
      source ("(Do (Perform Host " ++ act ++ "))")]
    let mut canonical : Option String := none
    for text in variants do
      let term ← expectTyped text
      let encoded := Interchange.renderCanonicalTerm term
      if let some first := canonical then
        if encoded != first then throw <| IO.userError "F01 Act/Do/Perform notation disagrees"
      else canonical := some encoded
      let again ← IO.ofExcept ((normalizeSourceTerm Environment.empty term).mapError (fun e => e.detail))
      if Interchange.renderCanonicalTerm again != encoded then
        throw <| IO.userError "F01 source normalization double-performed an Act"
    let surface := SurfaceTerm.ofSExpr (← IO.ofExcept (SExpr.parse (source act)))
    let (raw, _) ← IO.ofExcept (decodeClosedCore "f01-raw" surface)
    if (synth Environment.empty raw).isOk then
      throw <| IO.userError "F01 deep typing silently admitted unnormalized Act as Discourse"
    let (normalized, _) ← IO.ofExcept ((synthesizeSource Environment.empty raw).mapError (fun e => e.detail))
    if some (Interchange.renderCanonicalTerm normalized) != canonical then
      throw <| IO.userError "F01 source-facing synthesis disagrees with decoder"

  let external : Environment 0 := { Environment.empty with free := [
    ({domain := "$S", serial := 0}, Ty.refComp (Ty.referents Ty.entity)),
    ({domain := "$P", serial := 0}, Ty.pureFn [Ty.referents Ty.entity] Ty.content),
    ({domain := "$A", serial := 0}, Ty.act Ty.assertion)] }
  for act in ["$A", "(Let [$saved :: Act Assertion] $A $saved)"] do
    let mut first : Option String := none
    for d in [act, "(Do " ++ act ++ ")", "(Do (Perform Host " ++ act ++ "))"] do
      let surface := SurfaceTerm.ofSExpr (← IO.ofExcept (SExpr.parse (form (source := "$S") (continuation := d))))
      let (term, state) ← IO.ofExcept ((elaborateSurface "f01-source-api" [] ["$S", "$P", "$A"] none [] external none surface {}).mapError (fun e => e.detail))
      if state.core.sourceNotation != (d != "(Do (Perform Host " ++ act ++ "))") then
        throw <| IO.userError "F01 source normalization lost its changed-input disposition"
      let _ ← IO.ofExcept ((synth external term).mapError (fun e => e.detail))
      let encoded := Interchange.renderCanonicalTerm term
      if let some prior := first then
        if encoded != prior then throw <| IO.userError "F01 production elaborator Act notation mismatch"
      else first := some encoded

  -- Canonical force decoding exposes the previously unsupported performance
  -- Bind typing consumers. Retain their real premises and reject Content or
  -- reference-computation bodies rather than expanding the result category.
  let boundPerformance := fun body => close <|
    "(Bind [$next :: ActOccurrence Assertion] (Perform Host (Assert ($P Speaker))) " ++ body ++ ")"
  for body in ["(Assert ($P Speaker))", "(Do (Perform Host (Assert ($P Speaker))))",
      "(Perform Host (Assert ($P Speaker)))"] do
    let surface := SurfaceTerm.ofSExpr (← IO.ofExcept (SExpr.parse (boundPerformance body)))
    let (raw, _) ← IO.ofExcept (decodeClosedCore "f01-performance-bind" surface)
    let result ← IO.ofExcept ((synth Environment.empty raw).mapError (fun e => e.detail))
    if !result.trace.all typingRuleImplemented then
      throw <| IO.userError "performance Bind consumer lacks its typing proof"
  for body in ["($P Speaker)", "$source"] do
    let surface := SurfaceTerm.ofSExpr (← IO.ofExcept (SExpr.parse (boundPerformance body)))
    let (raw, _) ← IO.ofExcept (decodeClosedCore "f01-invalid-performance-bind" surface)
    if (synth Environment.empty raw).isOk then
      throw <| IO.userError "performance Bind accepted a non-performance body"
  IO.println "F01-A1: four Act expressions x three source spellings; free-env Act/Let production paths; all three performance-Bind modes and two wrong-body controls PASS"

  -- Sites exercise all three arms at distinct depths. They are supplied
  -- syntactic sites; these controls do not certify source-family eligibility.
  let siteText := close (form (source := "(Context $source)")
    (content := "(Bind [$z :: Referents Entity] (Context $x) ($P $z))")
    (continuation := "(Do (Perform (Assert (Bind [$y :: Referents Entity] (Vague (λ [$r :: Referents Entity] ($P $r))) ($P $y)))))"))
  let (siteTerm, state) ← IO.ofExcept (decode siteText)
  if siteTerm.siteUses.map (·.scope) != [2, 3, 4] || state.sites.length != 3 then
    throw <| IO.userError "F01 source/content/continuation site depths are not n/n+1/n+2"
  if siteTerm.siteIds != (siteTerm.rename (fun i => (Fin.elim0 i : Fin 1))).siteIds then
    throw <| IO.userError "F01 renaming minted or reordered sites"
  let (_, _, _, _, _, _) ← IO.ofExcept <| decodePerformSourceParts
    (match SurfaceTerm.ofSExpr (← IO.ofExcept (SExpr.parse (form))) with
      | .form _ _ args => args
      | _ => [])
  match baseline with
  | .lambda _ (.lambda _ (.performSource _ _ content _)) =>
      match content with
      | .apply (.bound _) (.positional (.bound _) .nil) => pure ()
      | _ => throw <| IO.userError "F01 decoder wrapped its resolved Content arm"
  | _ => throw <| IO.userError "F01 decoder did not retain the direct constructor"
  IO.println s!"F01 structural controls: 7 positive typed/roundtrip paths, {negatives.length} rejections, alpha/Host/site-depth/payload controls; no runtime model"

end F01
end SmusniPilot
