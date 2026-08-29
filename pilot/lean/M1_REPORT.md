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

The matrix was committed before constructors at base main
`892a7040d4f3786be42635089b6aac7743ba6b74`. Its current 284 namespace-qualified
rows are:

| disposition | count | Lean representation |
|---|---:|---|
| `primitive-core` | 119 | one constructor in generated `Primitive` |
| `defined-surface` | 84 | one constructor in generated `SurfaceHead` |
| `type-index-data` | 70 | one constructor in generated `TypeName`, or a special scoped/index case |
| `gap-prose-only` | 6 | generated `GapHead`; never decodes to core |
| `tool-only` | 5 | generated `ToolHead`; never decodes to core |

The complete list, sources, and evidence are in
`pilot/shared/M1_CONSTRUCTOR_DISPOSITION.tsv`; its fail-closed builders also
pin the source digests. The special scoped `Term` constructors are bound/free
variables, naturals, λ, `Bind`, application, lexical predication,
site-bearing `Context`/`Vague`, and generic primitive application.

The `Primitive` argument to the last constructor has 119 named constructors.
This is a deliberate factorization of first-order syntax: without M2 typing,
the remaining operators all have the same binding behavior, so 119 direct
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
`Site n` also carries role, scoped dependency profile, and RR linkage. The
decoder assigns written sites in deterministic traversal/source order, never
from byte offsets.

Binding infrastructure is 619 lines including scoped data/core, or 492 lines
for operations and proofs alone:

- renaming, lifted renaming, weakening;
- capture-avoiding substitution and lifted substitution;
- capture-avoiding lowering of dependency-profile references across binders;
- identity renaming/substitution;
- renaming composition;
- substitution followed by renaming commutes with renaming every replacement;
- dependency-list and site transformation compatibility;
- renaming preserves the complete site-ID list;
- substitution preserves every pre-existing site ID;
- site renaming/substitution never changes the site identity;
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
  de Bruijn number, and RR linkage); and
- a nonsemantic source map (binder spellings, structural position/source
  ordinal, and source order; optional physical line/column fields).

The kernel theorem `BundleDatum.toBundle_ofBundle` proves exact round trip for
every internal bundle through an independent typed structured transport AST.
The textual S-expression reader is the untrusted byte boundary; runtime gates
check `encode(decode(encode(b))) = encode(b)` for the example bundle, every 68
already-primitive S1 payloads, and 311 programmatically generated core terms.
Source maps do not enter `Term` or `TermDatum` equality. The generic
S-expression canonical round trip is checked on all 337 S1 terms.

## S1 ingestion

The S1 manifest pins all 337 frozen corpus cases, both ruleset/inventory hashes,
and every RR/parse record digest:

| tag | count | result |
|---|---:|---|
| `primitive-core` | 68 | decoded to `Bundle` and text-round-tripped |
| `pending-milestone-2` | 269 | decoded/round-tripped as `SurfaceTerm` |
| `out-of-slice` | 0 | none |

Both verified L5.30 fence cases are present and pending M2. All 29 RR and 31
gentufa parse fixtures are read from disk and validated as typed records; both
structural/skeleton probe files are included. RR fixtures validate exact
version/root/fence metadata, all eight named fields, no duplicates/unknowns,
and natural case indices. Parse fixtures validate the per-case index, command,
surface, and parse payload shapes. No fixture term appears as a Lean literal.

The strict reader exposed 28 RR files with an extra trailing `)`. The existing
Racket loader read only one datum and ignored trailing bytes. This branch
removes those extra delimiters, makes `load-rr-fixture` require exactly one
datum, and adds positive/trailing-datum/trailing-read-error regressions. The
full Racket gate passes 1,830 tests after the correction.

Literal M1 runner result:

```text
S1 total=337 primitive=68 pending-m2=269 out-of-slice=0
core-decoded=68 surface-roundtrips=337 text-roundtrips=337
generated-roundtrips=311
```

## Timing

- clean M1 build after `lake clean`: 7.67 s wall, 21.91 s user, 3.85 s system,
  1,653,652 KiB maximum RSS;
- warm S1 + local/generated gate run: 0.34 s wall, 0.10 s user, 0.17 s system,
  133,304 KiB maximum RSS.

Build time is not reported as runtime.

## Explicit limits / not yet general

- M1 performs no surface-to-core elaboration for the 269 defined-form cases;
  they are `pending-milestone-2`, not successes or gaps.
- `Ty` records named formers, variables, and index data but does not validate
  arity/subsorting; that is extrinsic M2 typing.
- Generic primitive nodes do not validate operator arity or result category in
  M1.
- The source map records stable structural ordinals/source order and binder
  spellings. Physical line/column fields exist but are absent when the frozen
  inventory does not preserve them.
- The current surface decoder normalizes multi-parameter λ telescopes to nested
  single binders. Multi-binding `Bind` is not accepted directly; the live S1
  uses explicit nesting and M2 must preserve the same source order.
- Expansion-introduced sites, including L5.29 scale/cutoff sites, are M2 work.
- Text parsing and file hashing remain outside the Lean kernel; the typed
  structured round-trip theorem and runtime corpus gates make that boundary
  explicit rather than pretending bytes are proved.
