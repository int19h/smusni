import Lean
import SmusniPilot.Decode
import SmusniPilot.Interchange

namespace SmusniPilot

open Lean

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

structure S1Manifest where
  schema : String
  version : Nat
  base_head : String
  sources : Json
  counts : S1Counts
  cases : Array S1CaseRecord
  typed_records : Array S1TypedRecord
  deriving FromJson

structure CorpusCase where
  id : String
  provenance : SExpr
  term : SExpr
  environment : SExpr
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
      pure { id, provenance, term, environment }
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

def expectedTag (surface : SurfaceTerm) : String :=
  if !surface.offendingHeads.isEmpty then "out-of-slice"
  else if !surface.definedHeads.isEmpty then "pending-milestone-2"
  else "primitive-core"

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

def validateCorpusCase (lexicalHeads : List String) (manifest : S1Manifest)
    (run : S1Run) (record : CorpusCase) : IO S1Run := do
  let some expected := findManifestCase manifest record.id
    | throw <| IO.userError s!"case absent from S1 manifest: {record.id}"
  let surface := SurfaceTerm.ofSExprWithLexicon lexicalHeads record.term
  let actualTag := expectedTag surface
  if actualTag != expected.tag then
    throw <| IO.userError s!"case {record.id}: tag {actualTag}, expected {expected.tag}"
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
  if actualTag == "primitive-core" then
    let bundle ← IO.ofExcept (Interchange.Bundle.ofSurface record.id surface)
    let encoded := Interchange.Bundle.encode bundle
    let decoded ← IO.ofExcept (Interchange.Bundle.decode 0 encoded)
    if !(Interchange.Bundle.encode decoded == encoded) then
      throw <| IO.userError s!"case {record.id}: bundle round trip failed"
    updated := { updated with decodedCore := updated.decodedCore + 1 }
  pure updated

def runS1 (root : String) : IO S1Run := do
  let manifestSource ← IO.FS.readFile (root ++ "/pilot/shared/M1_S1_MANIFEST.json")
  let manifest : S1Manifest ←
    IO.ofExcept (Json.parse manifestSource >>= fromJson?)
  if manifest.schema != "smusni-pilot-s1" || manifest.version != 1 then
    throw <| IO.userError "unsupported S1 manifest"
  let corpusSource ← IO.FS.readFile
    (root ++ "/tools/smusni-redex/inventory/port-corpus.sexp")
  let corpus ← IO.ofExcept (SExpr.parse corpusSource >>= decodeCorpus)
  let fixtureSource ← IO.FS.readFile
    (root ++ "/tools/smusni-redex/inventory/fixtures.sexp")
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
