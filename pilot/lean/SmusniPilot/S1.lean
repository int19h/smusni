import Lean
import SmusniPilot.Decode
import SmusniPilot.Interchange

namespace SmusniPilot

open Lean

def pinnedM1BaseHead : String :=
  "892a7040d4f3786be42635089b6aac7743ba6b74"

structure S1Counts where
  total_cases : Nat
  primitive_core : Nat
  pending_milestone_2 : Nat
  out_of_slice : Nat
  l5_30_cases : Nat
  typed_records : Nat
  skeleton_probe_records : Nat
  deriving FromJson

structure S1CaseRecord where
  id : String
  tag : String
  term_sha256 : String
  heads : Array String
  defined_heads : Array String
  offending_heads : Array String
  l5_30 : Bool
  provenance : Json
  deriving FromJson

structure S1TypedRecord where
  path : String
  schema : String
  sha256 : String
  skeleton_probe : Option Bool := none
  deriving FromJson

structure S1Sources where
  constructor_matrix_sha256 : String
  fixtures : String
  fixtures_sha256 : String
  inventory_hashes : Array String
  port_corpus : String
  port_corpus_sha256 : String
  rr_syntax_normalization : String
  deriving FromJson

structure S1Manifest where
  schema : String
  version : Nat
  base_head : String
  sources : S1Sources
  counts : S1Counts
  cases : Array S1CaseRecord
  typed_records : Array S1TypedRecord
  deriving FromJson

structure CorpusCase where
  id : String
  provenance : SExpr
  term : SExpr
  environment : SExpr
  inventory : List String
  deriving Repr

def SExpr.stringValue? : SExpr → Option String
  | .atom (.string value) => some value
  | _ => none

def SExpr.field? (name : String) : List SExpr → Option SExpr
  | [] => none
  | .list _ (.atom (.symbol actual) :: values) :: rest =>
      if actual == name then
        match values with
        | [single] => some single
        | many => some (.list .paren many)
      else field? name rest
  | _ :: rest => field? name rest

def SExpr.stringList : SExpr → Except String (List String)
  | .list _ items => items.mapM fun
      | .atom (.string value) => pure value
      | value => .error s!"expected string list item, got {repr value}"
  | value => .error s!"expected list of strings, got {repr value}"

def decodeCorpusCase : SExpr → Except String CorpusCase
  | .list _ (.atom (.symbol "case") :: fields) => do
      let some rawId := SExpr.field? "id" fields
        | .error "corpus case missing id"
      let some id := rawId.stringValue?
        | .error "corpus case id is not a string"
      let some provenance := SExpr.field? "provenance" fields
        | .error s!"corpus case {id} missing provenance"
      let some term := SExpr.field? "term" fields
        | .error s!"corpus case {id} missing term"
      let some environment := SExpr.field? "env" fields
        | .error s!"corpus case {id} missing env"
      let some rawInventory := SExpr.field? "inventory" fields
        | .error s!"corpus case {id} missing inventory hashes"
      let inventory ← rawInventory.stringList
      pure { id, provenance, term, environment, inventory }
  | value => .error s!"malformed corpus case: {repr value}"

def decodeCorpus : SExpr → Except String (List CorpusCase)
  | .list _ items => do
      let some casesNode := SExpr.field? "cases" items
        | .error "port corpus missing cases"
      match casesNode with
      | SExpr.list _ cases => cases.mapM decodeCorpusCase
      | _ => .error "port corpus cases field is not a list"
  | _ => .error "port corpus root is not a list"

def decodeLexicalHeads : SExpr → Except String (List String)
  | .list _ (_header :: _version :: rows) =>
      pure <| rows.filterMap fun
        | .list _ (.atom (.symbol "row") :: .atom (.symbol head) :: _) =>
            some head
        | _ => none
  | _ => .error "malformed lexical fixture inventory"

partial def undeclaredVariables (freeNames boundNames : List String) :
    SurfaceTerm → List String
  | .atom (.symbol name) =>
      if name.startsWith "$" &&
          !boundNames.contains name && !freeNames.contains name then [name]
      else []
  | .atom _ | .empty _ => []
  | .form _ (.defined _) _ => []
  | .form _ (.primitive .lambda) [binders, body] =>
      match decodeBinderGroup binders with
      | .ok decoded =>
          undeclaredVariables freeNames
            (decoded.map (·.spelling) ++ boundNames) body
      | .error _ => ["$malformed-lambda-binder"]
  | .form _ (.primitive .bind) arguments =>
      match decodeBindClauses arguments with
      | .ok (clauses, body) =>
          let rec visit (currentBound : List String) :
              List (Binder × SurfaceTerm) → List String
            | [] => undeclaredVariables freeNames currentBound body
            | (binder, computation) :: rest =>
                undeclaredVariables freeNames currentBound computation ++
                  visit (binder.spelling :: currentBound) rest
          visit boundNames clauses
      | .error error => ["$malformed-bind-binder:" ++ error]
  | term@(.form _ (.variable name) arguments) =>
      if term.isBinderDescriptor then []
      else
        (if boundNames.contains name || freeNames.contains name then [] else [name]) ++
          arguments.flatMap (undeclaredVariables freeNames boundNames)
  | .form _ _ arguments =>
      arguments.flatMap (undeclaredVariables freeNames boundNames)
  | .application _ function arguments =>
      undeclaredVariables freeNames boundNames function ++
        arguments.flatMap (undeclaredVariables freeNames boundNames)

def expectedTag (lexicalHeads freeNames : List String)
    (surface : SurfaceTerm) : String :=
  if !(surface.offendingHeadsWith lexicalHeads).isEmpty ||
      !(undeclaredVariables freeNames [] surface).isEmpty then "out-of-slice"
  else if !(surface.definedHeadsWith lexicalHeads).isEmpty then
    "pending-milestone-2"
  else "primitive-core"

def freeNamesFromEnvironment : SExpr → List String
  | .list _ entries => entries.filterMap fun
      | .list _ (.atom (.symbol name) :: _) =>
          if name.startsWith "$" then some name else none
      | _ => none
  | _ => []

def padOrdinal (ordinal : Nat) : String :=
  let raw := toString ordinal
  if raw.length == 1 then "00" ++ raw
  else if raw.length == 2 then "0" ++ raw
  else raw

partial def rrLinkFromProvenance : SExpr → Option String
  | .list _ (.atom (.symbol "fence") :: .atom (.string source) ::
      .atom (.symbol rawOrdinal) :: _) => do
      let ordinal ← rawOrdinal.toNat?
      let stem := (source.dropEnd 3).toString
      pure s!"tools/smusni-redex/inventory/rr/{stem}-{padOrdinal ordinal}.sexp"
  | .list _ items => items.findSome? rrLinkFromProvenance
  | _ => none

partial def provenanceHasFenceKind (wanted : String) : SExpr → Bool
  | .list _
      (.atom (.symbol "fence") :: _source :: _ordinal ::
       .atom (.symbol kind) :: _) => kind == wanted
  | .list _ items => items.any (provenanceHasFenceKind wanted)
  | _ => false

def findManifestCase (manifest : S1Manifest) (id : String) :
    Option S1CaseRecord :=
  manifest.cases.find? fun record => record.id == id

def sha256File (root path : String) : IO String := do
  let output ← IO.Process.output {
    cmd := "sha256sum"
    args := #[root ++ "/" ++ path]
  }
  if output.exitCode != 0 then
    throw <| IO.userError s!"sha256sum failed for {path}: {output.stderr}"
  pure <| (output.stdout.splitOn " ").head!.trimAscii.toString

def rrFieldNames : List String :=
  ["parse", "attach", "readings", "rows", "stores", "sites", "anaphora",
   "force"]

def validateRRCase : SExpr → Except String Unit
  | .list _
      [.atom (.symbol "case"), .atom (.symbol rawIndex),
       .list _ (.atom (.symbol "rr") :: fields)] => do
      if rawIndex.toNat?.isNone then .error "RR case index is not natural"
      let names ← fields.mapM fun
        | .list _ [.atom (.symbol name), _] => pure name
        | _ => .error "RR field is not a name/value pair"
      if names.length != names.eraseDups.length then
        .error "RR case has a duplicate field"
      else if names.any fun name => !rrFieldNames.contains name then
        .error "RR case has an unknown field"
      else if rrFieldNames.any fun name => !names.contains name then
        .error "RR case is missing a required field"
      else pure ()
  | _ => .error "malformed RR case"

def validateRRFixture : SExpr → Except String Unit
  | .list _
      (.atom (.symbol "smusni-rr-fixture") :: .atom (.symbol "1") ::
       fence :: cases) => do
      match fence with
      | .list _
          [.atom (.symbol "fence"), .atom (.string _),
           .atom (.symbol ordinal), .atom (.string _)] =>
          if ordinal.toNat?.isNone then .error "RR fence ordinal is not natural"
          else cases.forM validateRRCase
      | _ => .error "malformed RR fence metadata"
  | _ => .error "bad RRFixture root or version"

def validateJsonString : Json → Except String Unit
  | .str _ => pure ()
  | _ => .error "expected JSON string"

def validateParseCase (value : Json) : Except String Unit := do
  let index ← value.getObjVal? "index"
  match index with
  | .num _ => pure ()
  | _ => .error "parse case index is not numeric"
  let command ← value.getObjVal? "command"
  match command with
  | .arr items => items.forM validateJsonString
  | _ => .error "parse case command is not an array"
  let surface ← value.getObjVal? "surface"
  match surface with
  | .str _ | .bool false => pure ()
  | _ => .error "parse case surface is neither string nor false"
  let parse ← value.getObjVal? "parse"
  match parse with
  | .obj _ | .bool false => pure ()
  | _ => .error "parse case parse payload is neither object nor false"

def validateParseFixture (value : Json) : Except String Unit := do
  let cases ← value.getObjVal? "cases"
  match cases with
  | .arr items => items.forM validateParseCase
  | _ => .error "ParseFixture cases is not an array"

def validateTypedRecord (root : String) (record : S1TypedRecord) : IO Unit := do
  let actualDigest ← sha256File root record.path
  if actualDigest != record.sha256 then
    throw <| IO.userError s!"digest mismatch for {record.path}"
  let source ← IO.FS.readFile (root ++ "/" ++ record.path)
  match record.schema with
  | "RRFixture" =>
      let parsed ← IO.ofExcept <| (SExpr.parse source).mapError fun error =>
        s!"{record.path}: {error}"
      IO.ofExcept <| (validateRRFixture parsed).mapError fun error =>
        s!"{record.path}: {error}"
  | "ParseFixture" =>
      let parsed ← IO.ofExcept (Json.parse source)
      IO.ofExcept <| (validateParseFixture parsed).mapError fun error =>
        s!"{record.path}: {error}"
  | schema => throw <| IO.userError s!"unknown typed record schema {schema}"

structure S1Run where
  total : Nat := 0
  primitive : Nat := 0
  pendingM2 : Nat := 0
  outOfSlice : Nat := 0
  decodedCore : Nat := 0
  surfaceRoundTrips : Nat := 0
  textRoundTrips : Nat := 0
  deriving Repr, Inhabited

def S1Run.addTag (run : S1Run) (tag : String) : S1Run :=
  { run with
    total := run.total + 1
    primitive := run.primitive + if tag == "primitive-core" then 1 else 0
    pendingM2 := run.pendingM2 +
      if tag == "pending-milestone-2" then 1 else 0
    outOfSlice := run.outOfSlice + if tag == "out-of-slice" then 1 else 0 }

def probeSurface (source : String) : Except String SurfaceTerm :=
  return SurfaceTerm.ofSExprWithLexicon [] (← SExpr.parse source)

def runClassifierProbes : IO Unit := do
  let boundApplication ← IO.ofExcept <|
    probeSurface "(λ ($f :: Entity) ($f 1))"
  if expectedTag [] [] boundApplication != "primitive-core" then
    throw <| IO.userError "bound-application probe was not primitive-core"
  let boundBundle ← IO.ofExcept <|
    Interchange.Bundle.ofSurfaceWith "probe-bound" [] [] none boundApplication
  match boundBundle.term with
  | .lambda _ (.apply (.bound _) (.natural 1)) => pure ()
  | _ => throw <| IO.userError "bound application decoded as lexical/free"

  let definedAtom ← IO.ofExcept <| probeSurface "(Refer This)"
  if expectedTag [] [] definedAtom != "pending-milestone-2" then
    throw <| IO.userError "defined atom probe did not stay pending M2"

  let unknown ← IO.ofExcept <| probeSurface "(Zzz 1)"
  if expectedTag [] [] unknown != "out-of-slice" then
    throw <| IO.userError "unknown-head probe failed open"

  let stringPayload ← IO.ofExcept <| probeSurface "(OpaqueQuote \"mi klama\")"
  if expectedTag [] [] stringPayload != "primitive-core" then
    throw <| IO.userError "string payload probe was not primitive-core"
  let stringBundle ← IO.ofExcept <|
    Interchange.Bundle.ofSurfaceWith "probe-string" [] [] none stringPayload
  match stringBundle.term with
  | .primitive .opaqueQuote (.cons (.string "mi klama") .nil) => pure ()
  | _ => throw <| IO.userError "string payload decoded as lexical"

  let ghost ← IO.ofExcept <| probeSurface "(Refer $ghost)"
  if expectedTag [] [] ghost != "out-of-slice" then
    throw <| IO.userError "undeclared-free probe failed open"
  if (Interchange.Bundle.ofSurfaceWith "probe-ghost" [] [] none ghost).isOk then
    throw <| IO.userError "undeclared free identity was synthesized"

  let schematic ← IO.ofExcept <| probeSurface "(C H deps…)"
  if expectedTag [] [] schematic != "out-of-slice" then
    throw <| IO.userError "schematic-head probe failed open"

def validateCorpusCase (lexicalHeads : List String) (manifest : S1Manifest)
    (run : S1Run) (record : CorpusCase) : IO S1Run := do
  let some expected := findManifestCase manifest record.id
    | throw <| IO.userError s!"case absent from S1 manifest: {record.id}"
  let surface := SurfaceTerm.ofSExprWithLexicon lexicalHeads record.term
  let freeNames := freeNamesFromEnvironment record.environment
  let actualTag :=
    if provenanceHasFenceKind "declaration" record.provenance then
      "out-of-slice"
    else expectedTag lexicalHeads freeNames surface
  if actualTag != expected.tag then
    throw <| IO.userError <|
      s!"case {record.id}: tag {actualTag}, expected {expected.tag}; " ++
      s!"heads={repr (surface.offendingHeadsWith lexicalHeads)} " ++
      s!"free={repr (undeclaredVariables freeNames [] surface)}"
  let canonical := surface.toSExpr
  let reparsedSurface := SurfaceTerm.ofSExprWithLexicon lexicalHeads canonical
  if !(reparsedSurface == surface) then
    throw <| IO.userError s!"case {record.id}: SurfaceTerm round trip failed"
  let text ← IO.ofExcept (SExpr.parse canonical.render)
  if !(text == canonical) then
    throw <| IO.userError s!"case {record.id}: text S-expression round trip failed"
  let mut updated := (run.addTag actualTag)
  updated := { updated with
    surfaceRoundTrips := updated.surfaceRoundTrips + 1
    textRoundTrips := updated.textRoundTrips + 1 }
  if record.inventory.toArray != manifest.sources.inventory_hashes then
    throw <| IO.userError s!"case {record.id}: inventory hash mismatch"
  if actualTag == "primitive-core" then
    let rrLink := (rrLinkFromProvenance record.provenance).bind fun candidate =>
      if manifest.typed_records.any fun typed => typed.path == candidate
      then some candidate else none
    let bundle ← IO.ofExcept <|
      Interchange.Bundle.ofSurfaceWith record.id lexicalHeads freeNames
        rrLink surface
    if bundle.sites.any fun site => site.rrLink != rrLink then
      throw <| IO.userError s!"case {record.id}: site RR linkage mismatch"
    let encoded := Interchange.Bundle.encode bundle
    let decoded ← IO.ofExcept (Interchange.Bundle.decode 0 encoded)
    if !(Interchange.Bundle.encode decoded == encoded) then
      throw <| IO.userError s!"case {record.id}: bundle round trip failed"
    updated := { updated with decodedCore := updated.decodedCore + 1 }
  pure updated

def runS1 (root : String) : IO S1Run := do
  runClassifierProbes
  let manifestSource ← IO.FS.readFile (root ++ "/pilot/shared/M1_S1_MANIFEST.json")
  let manifest : S1Manifest ←
    IO.ofExcept (Json.parse manifestSource >>= fromJson?)
  if manifest.schema != "smusni-pilot-s1" || manifest.version != 1 then
    throw <| IO.userError "unsupported S1 manifest"
  if manifest.base_head != pinnedM1BaseHead then
    throw <| IO.userError "S1 manifest base head drift"
  let corpusDigest ← sha256File root manifest.sources.port_corpus
  if corpusDigest != manifest.sources.port_corpus_sha256 then
    throw <| IO.userError "port corpus source digest mismatch"
  let fixtureDigest ← sha256File root manifest.sources.fixtures
  if fixtureDigest != manifest.sources.fixtures_sha256 then
    throw <| IO.userError "lexical fixture source digest mismatch"
  let matrixDigest ← sha256File root
    "pilot/shared/M1_CONSTRUCTOR_DISPOSITION.tsv"
  if matrixDigest != manifest.sources.constructor_matrix_sha256 then
    throw <| IO.userError "constructor matrix digest mismatch"
  let corpusSource ← IO.FS.readFile (root ++ "/" ++ manifest.sources.port_corpus)
  let corpus ← IO.ofExcept (SExpr.parse corpusSource >>= decodeCorpus)
  let fixtureSource ← IO.FS.readFile
    (root ++ "/" ++ manifest.sources.fixtures)
  let lexicalHeads ← IO.ofExcept
    (SExpr.parse fixtureSource >>= decodeLexicalHeads)
  let run ← corpus.foldlM (validateCorpusCase lexicalHeads manifest) {}
  if run.total != manifest.counts.total_cases ||
      run.primitive != manifest.counts.primitive_core ||
      run.pendingM2 != manifest.counts.pending_milestone_2 ||
      run.outOfSlice != manifest.counts.out_of_slice then
    throw <| IO.userError s!"S1 count mismatch: {repr run}"
  for record in manifest.typed_records do
    validateTypedRecord root record
  pure run

end SmusniPilot
