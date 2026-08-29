# Lean milestone 1 report — term, interchange, binders

## Outcome

M1 is implemented on the pinned Lean 4.33.1 / Lake 5.0.0 toolchain. It builds
one primitive-only, well-scoped `CoreTerm` representation; a distinct
non-denoting `SurfaceTerm`; generic and typed S-expression transport; semantic
site tables plus nonsemantic source maps; and complete runtime ingestion of the
pinned S1 inputs. No `sorry`, axiom, corpus literal table, `Lean.Expr`
whitelist, intrinsic type/effect index, or §12 constructor is present.

This is derived pilot evidence. It neither selects Lean nor transfers semantic
authority, and it implements no M2 elaboration or typing.

## Constructor disposition and representation

The pre-constructor commit `d900e16` recorded 282 rows: 119 primitive, 84
defined, 68 type/index data, 6 gap, and 5 tool rows. Review of the first
implementation then exposed four missing syntax/data categories, so the
current matrix has 286 namespace-qualified rows: the original rows plus
`term:$index`, `term:$string`, `type:$index`, and `type:$variable`. Both points
in that history are recorded here rather than retroactively describing all 286
as pre-code.

| disposition | count | Lean representation |
|---|---:|---|
| `primitive-core` | 121 | full inventory; 111 generated first-order operators plus 10 structural forms |
| `defined-surface` | 84 | one constructor in generated `SurfaceHead` |
| `type-index-data` | 70 | one constructor in generated `TypeName`, or a special scoped/index case |
| `gap-prose-only` | 6 | generated `GapHead`; never decodes to core |
| `tool-only` | 5 | generated `ToolHead`; never decodes to core |

The complete list, sources, and evidence are in
`pilot/shared/M1_CONSTRUCTOR_DISPOSITION.tsv`; its fail-closed builders also
pin the source digests. The special scoped `Term` constructors are bound/free
variables, naturals, strings, index labels, λ, `Bind`, application, lexical predication,
site-bearing `Context`/`Vague`, and generic primitive application.

The full generated `Primitive` inventory has 121 names, while the argument to
the generic core constructor is the generated 111-member
`FirstOrderPrimitive`. The other ten inventory entries (`$application`,
`$index`, `$lexical-predication`, `$natural`, `$string`, `$variable`, `Bind`,
`Context`, `Vague`, and `λ`) are excluded by type and can only use their
dedicated structural representation.
This is a deliberate factorization of first-order syntax: without M2 typing,
the remaining operators all have the same binding behavior, so 111 direct
`Term` clauses would duplicate renaming/substitution logic without semantic
content. λ, `Bind`, variables, application, lexical heads, and sites are direct
constructors because their binding or identity behavior differs. M2 supplies
operator-specific arity, formation, and typing; M1 does not accept a generic
operator merely because it parses.

The appendix-only names absent from the old core inventory are not lost:
`NewTopic`, `Resume`, `ActContent`, `InterpretAct`, the realized projections,
`QuestionOf`, `During`, `EnumerationOrdinal`, context operations, arithmetic
crossings, and related names are explicit matrix/Lean constructors. The
appendix's non-term `bind` operation and `Select` family label are recorded as
metatheory/family rows rather than invented terms. The `klama` ledger row is a
mapping-schema example; actual fixture-declared lexical heads route through
generic lexical predication.

## Scoped core and binding infrastructure

`Term n` uses `Fin n` for bound variables, so an ill-scoped bound variable is
unrepresentable. Free/RR identities are explicit `FreeId`s. A `SiteId` is the
structural triple `(document identity, occurrence ordinal, expansion role)`;
`Term` stores only that identity at a site occurrence. The authoritative
sidecar entry carries role, serialized scoped dependency profile, and RR
linkage; `Site n` remains the scoped algebraic form used to state and prove
dependency transformations. The decoder assigns written sites and sidecar
entries together in deterministic traversal/source order, never from byte
offsets.

Binding infrastructure is 786 lines including scoped data/core, or 588 lines
for operations and proofs alone:

- renaming, lifted renaming, weakening;
- capture-avoiding substitution and lifted substitution;
- capture-avoiding lowering of dependency-profile references across binders;
- identity renaming/substitution;
- renaming composition;
- renaming followed by substitution;
- substitution followed by renaming commutes with renaming every replacement;
- substitution composition;
- dependency-list and site transformation compatibility;
- renaming preserves the complete site-ID list;
- substitution preserves every pre-existing site ID;
- site-profile renaming/substitution never changes the site identity;
- source binder spellings erase to equal core terms.

All are kernel theorems in `BindingLaws.lean`/`Examples.lean`; none is assumed.
The examples additionally prove bound dependency substitution changes
`bound 0` into the replacement's free identity, while retaining the site ID.

Site discriminators pass:

- one shared λ value used twice retains the same site identity at both uses;
- two copied occurrences carry distinct identities;
- α-renamed source binders produce byte-for-byte equal encoded `CoreTerm`,
  while their display spellings remain distinct in the source map.

## Interchange and trust boundary

The generic reader handles parentheses, braces, square brackets, comments,
symbols, quoted strings, and escapes. Its writer emits one canonical spelling.
`SurfaceTerm` classifies heads through the generated matrix and retains bracket
shape. Defined forms have no denotation and cannot decode as core.

The versioned bundle contains:

- the term datum;
- a semantic site table (identity, role, scoped dependencies serialized by
  de Bruijn number, and RR linkage to the actual typed fixture path or `none`);
  and
- a nonsemantic source map (binder spellings, structural position/source
  ordinal, and source order; optional physical line/column fields).

The kernel theorem `BundleDatum.toBundle_ofBundle` proves exact round trip for
every internal bundle through an independent typed structured transport AST.
The textual S-expression reader is the untrusted byte boundary; runtime gates
check `encode(decode(encode(b))) = encode(b)` for the example bundle, every 50
already-primitive S1 payloads, and 303 programmatically generated core terms.
The core term encoding contains only site-ID references. Bundle validation
requires exactly one sidecar entry for every referenced identity, rejects
missing, extra, duplicate, role-conflicting, and out-of-scope entries, and is
run after both source decoding and text decoding. Each primitive S1 case also
passes a term-only source-to-core-to-canonical round trip.
Source maps do not enter `Term` or `TermDatum` equality. The generic
S-expression canonical round trip is checked on all 337 S1 terms.

## S1 ingestion

The S1 manifest pins all 337 frozen corpus cases, both ruleset/inventory hashes,
and every RR/parse record digest:

| tag | count | result |
|---|---:|---|
| `primitive-core` | 50 | decoded to `Bundle` and text-round-tripped |
| `pending-milestone-2` | 256 | decoded/round-tripped as `SurfaceTerm` |
| `out-of-slice` | 31 | declaration/schema/placeholders/malformed structure named with offending heads |

Both verified L5.30 fence cases are present and pending M2. All 29 RR and 31
gentufa parse fixtures are read from disk and validated as typed records; both
structural/skeleton probe files are included. RR fixtures validate exact
version/root/fence metadata, all eight named fields, no duplicates/unknowns,
and natural case indices. Parse fixtures require one of the three recorded
schema names, `jbotci_version`, a nonempty case array, ordinary-fixture source,
ordinal, and fence metadata, plus schema-appropriate per-case fields and
types. The port corpus validates its version, count, digests/source tables,
case field set, nonempty inventory hashes, and environments; environments are
list-shaped, contain only `$`-identity/type pairs, and reject duplicate
identities. Negative mutations cover corpus version/count/environment errors,
missing and unknown parse schemas, empty cases, missing parse fields, and each
invalid sidecar class. No fixture term appears as a Lean literal.
Lean verifies the recorded base commit, matrix/corpus/fixture SHA-256 values,
every typed-record digest, and both per-case inventory hashes before counting a
gate. The base commit is a fixed constant, never recomputed from moving
`origin/main`.

Classification is fail-closed: only fixture-declared lexical heads are
lexical; `$` applications resolve through binder/free environments; undeclared
free IDs, unknown atoms/operators, schematic placeholders, and declaration
fences are out-of-slice. Defined constants in atom position stay pending M2.
Unknown structure inside a defined form is still scanned and makes the case
out-of-slice; the outer defined head does not hide it. There are 232 cases with
one or more `$` spellings under a defined payload. Their binder/free status is
explicitly undetermined in M1 because it depends on M2 definition-specific
binder signatures; they are not silently diagnosed as undeclared.
Strings and index atoms have explicit literal constructors; argument labels
have explicit label/value list nodes. Direct probes cover
bound function application, `(Refer This)`, unknown `Zzz`, opaque string
payloads, undeclared `$ghost`, schematic `C/H/deps…`, unknown `Zzz` nested
under defined `Let`, malformed structural
forms, rejection of structural operators through the first-order constructor,
variadic/labelled applications, and empty/multiple/nested `Fn`/`EFn`
parameter lists.

The strict reader exposed 28 RR files with an extra trailing `)`. The existing
Racket loader read only one datum and ignored trailing bytes. This branch
removes those extra delimiters, makes `load-rr-fixture` require exactly one
datum, and adds positive/trailing-datum/trailing-read-error regressions. The
full Racket gate passes 1,830 tests after the correction.

Literal M1 runner result:

```text
S1 total=337 primitive=50 pending-m2=256 out-of-slice=31
core-decoded=50 core-canonical-roundtrips=50
surface-roundtrips=337 text-roundtrips=337
defined-payload-variable-cases=232 generated-roundtrips=303
```

## Timing

- clean M1 build after `lake clean`: 9.57 s wall, 28.18 s user, 3.98 s system,
  1,704,300 KiB maximum RSS;
- warm S1 + local/generated gate run: 0.34 s wall, 0.10 s user, 0.15 s system,
  133,432 KiB maximum RSS.

Build time is not reported as runtime.

## Explicit limits / not yet general

- M1 performs no surface-to-core elaboration for the 256 defined-form cases;
  they are `pending-milestone-2`, not successes or gaps.
- `Ty` records named formers, variables, index data, and explicit `Fn`/`EFn`
  parameter lists/results but does not validate arity/subsorting; that is
  extrinsic M2 typing.
- First-order primitive nodes do not validate operator arity or result category
  in M1; structural form shapes are validated before core decoding.
- The source map records stable structural ordinals/source order and binder
  spellings. Physical line/column fields exist but are absent when the frozen
  inventory does not preserve them.
- The surface decoder normalizes multi-parameter λ telescopes and multi-binding
  `Bind` forms to source-ordered nesting. Variadic ordinary application is one
  application node with an ordered list of positional/labelled fills, so no
  source arity or label structure is lost before M2 typing.
- Expansion-introduced sites, including L5.29 scale/cutoff sites, are M2 work.
- Text parsing and file hashing remain outside the Lean kernel; the typed
  structured round-trip theorem and runtime corpus gates make that boundary
  explicit rather than pretending bytes are proved.
