# Smusni Redex checker

This directory contains a derived checker for the notation and selected
static laws in `spec.md`. It is not a semantic authority: when the checker and
the documents disagree, the discrepancy must be diagnosed against the live
normative text.

Milestone 1 covers the declaration mirror, exhaustive classification of the
Markdown `lisp` fences in `spec.md` and `samples.md`, the concrete reader,
elaboration, extrinsic typing, and the static regression ledger. Fences in
derivative documents are outside this bounded corpus until a synchronization
milestone explicitly adds them. Dynamic execution, Lojban lowering, finite
model search, and Lean certificates are later milestones.

Run the milestone checks from the repository root:

```sh
tools/check-smusni
```

The fence classifier uses the tracked sidecar
`inventory/fences.sexp`. Every fence is keyed by source file, ordinal, and
content hash; insertion, deletion, or editing therefore makes the check fail
until the classification is reviewed. This avoids changing normative
documents merely to attach checker metadata.

All Racket list delimiters are semantically identical. Special forms are
recognized by their reserved head atoms and positional operands; the reader
does not preserve or validate brace shape. Its sole pre-read lexical step
protects identifier-internal Lojban apostrophes such as `te'a` outside
comments and strings.

`unchecked` is a manifest vocabulary item only for a durably explained gap;
the runner treats every such entry as a failure. It cannot make an in-scope
specimen green by exemption.

The lexical rows in `inventory/fixtures.sexp` are non-normative scaffolding
pending issue #12. The report lists the forms whose first milestone rules are
bounded pass-throughs rather than full signature checks. A normal run permits
only exact hash-bound findings in `expected-findings.sexp`; use
`tools/check-smusni --strict` to fail while any such document debt remains.

`Refer` admits an `EFn` restrictor at the *reference* level (spec §5.3): a
description property may sequence retrieval sites, and the returned referent
is still introduced by `Refer` itself. A *member-level* restrictor
(`Fn (T) Content`) is the §5.3 `CoveredBy` lift and must be pure; an
effectful member-level restrictor is rejected. Both halves are pinned by
static tests and must not be generalized to the pure positions (`SetOf`,
quantifier/Generic restrictors, and the `Select*` family).

Gate 3b enforces those pure positions directly. `SetOf`, all four
`Select*` members, `Generic`, and the §12 GQ family reject an effectful
restrictor with an `L0.1` pure-position diagnostic. The concrete GQs have their
normative signatures rather than pass-through typing: witness forms take a
pure member restrictor and a reference-level nuclear scope, `Every` takes a
member-level nuclear scope, and `GlobalExactly`/`Most` require both operands
to be pure because both run inside `SetOf` comprehensions. Exporting GQs keep
their witness-introduction effect (with the literal-zero `AtLeast`/`Exactly`
exceptions); `AtLeast 0` is effect-free `⊤` and does not evaluate its nuclear
scope, whereas `Exactly 0 = No` still does. `Card` and its
`GlobalExactly`/`Most` consumers carry the projective finite-set definedness
obligation.

## Checker fidelity follow-ups (#13)

- `Mention` constructs `Act<Expressive>` and is rejected where an assertion
  act is required; displaying a value never supplies assertion force.
- Sign constructors return their §7.5 kind (`Opaque`, `Structured`, `Name`,
  `Sentence`, `Letteral`, or `Word`) instead of collapsing quotation and word
  signs to `Sign<Sentence>`.
- `components_κ` accepts exactly one `Group<T>` object and records the
  complete-cover definedness obligation; plural group references require an
  explicit sole-group projection before crossing.
- `Fn`/`EFn` parameters are contravariant and results covariant. The §7.4/§7.5
  `Utterance`/`Sign` entry spellings keep their token-sort binder annotations,
  but their dedicated rules bind and return the singleton-lifted token-reference
  properties. The implemented `Assert`, `Express`, `Ask`, and `Mention`
  constructors suspend their payload effects, so described acts remain inert
  while a direct effect in an entry fact is still rejected; no general
  parameter-position lift is used for that notation. `SentenceSign` likewise
  stages its Content operand inertly.

The `le` description form `SpeakerDescribes` (#41 item 1) is typed by its §12
signature — described reference (member or plural) and a unary description
property — and is pure; `LocutionOf` and the `CurrentToken` constant carry the
sorts its definition needs; `SpeakerDescribesUnaddressed` (`voi`, #49) shares the
rule with the audience place deleted. `type-compatible?` places the §3.1 collection and
sign object sorts (`Set`, `Group`, `List`, `Sign`, `SignToken`) under `Entity`.

## Model-bank profiles

The model bank prints decision status before every verdict:

- `live-baseline` tests laws already present in the tracked specification;
- `human-adopted-pending-sync` tests an adopted decision not yet fully
  synchronized;
- `reviewer-consensus` tests a peer-settled proposal still awaiting the
  human/adoption or baseline edit recorded by its issue;
- `comparative` tests a still-live alternative profile without treating it
  as either baseline or rejected;
- `rejected-alternative` is expected to reject its discriminating model.

A green result in any non-baseline profile is evidence about that encoding,
never ratification. Named regressions are deterministic. Bounded searches
print the exact signature size and structure count. The divisible-bread
compatibility case uses a symbolic dyadic-interval splitter because a finite
atomless semilattice cannot exist; finite searches are never described as
atomless.

Generated files under `corpus/` are checked in for review. Regenerate them
with:

```sh
racket tools/smusni-redex/extract.rkt --write
```

Do not hand-edit generated corpus files.


## Lowering-rule citations (#9 M1)

`spec.md` §11 numbers every schema `Ln.m` and marks the kind of each: an
unmarked rule is a lowering judgment (the F₀ population); *(gap)*, *(note)*,
and *(reading)* rules are documented no-mappings, explanatory consequences,
and resolved-reading decisions, never citable and never ledgered. The checker
reads ids and kinds from the normative text, never from a copy. Specimens
carry an `(origin "surface"|"core")` clause: a surface specimen lowers
Lojban and must cite the judgments it instantiates as its focal claims (not
every rule its sub-terms touch); a core fixture is a typed term authored
directly in the core and cites nothing. Each specimen entry in
`inventory/fences.sexp` carries a `(rules …)` clause naming the rules it
instantiates, and `inventory/rule-coverage.sexp` ledgers every rule no
specimen cites yet, each with the issue that owns the gap. The run fails on a
specimen without citations, a citation of an unknown id, a rule that is
neither cited nor ledgered, or a ledger entry for a rule that a specimen does
cite. The ledger also carries a **ratchet** `(cited-floor N)`: the number of
rules cited by specimens may never fall below it, and a commit that raises
coverage must raise the floor, so ledgering a rule instead of writing its
specimen is a failing move and any lowered floor is a visible diff. Citing a
rule is a claim about the specimen; it is not checked semantically until #9
M3.

## Executable lowering (#9 M3)

M3 adds a derived lowering gate for live L1, L3, and L5 plus the L0.1 premise
(46 lowering judgments; fixtures are explicitly not exhaustive).
`inventory/lowering.sexp` identifies candidate fence keys, while one tracked
`gentufa` JSON fixture and one eight-field `RR` S-expression fixture per fence
preserve ordered cases. Refresh parser fixtures deliberately with:

```sh
racket tools/smusni-redex/lower.rkt --refresh-parses
```

The ordinary check never invokes jbotci. It attempts each candidate case as a
whole term, type-checks every produced core term, symmetrically normalizes only
the documented Close, omitted-place, force-boundary, and L0.1 display
conventions, and compares modulo α-renaming. Reports distinguish matched,
mismatch, unresolved, out-of-fragment, and in-fragment `no-lowering` results.
Missing RR fields and implementation failures fail the gate; missing rows are
report-only unless the manifest promises them; under-specified rules remain
visible #9 findings. Per-case dispositions are authoritative, and a documented
precedence produces the stable fence summary. Formed-rule coverage is printed
separately from M1's focal-citation ratchet.

The parse-to-source adapter recursively inspects tagged gentufa constructs
(`BridiStatement`, bridi/selbri/term nodes, descriptors, quantifiers,
connections, termsets, and LAhE) and treats terminal lexemes as data. It never
dispatches on a whole surface-token sentence. RR force, readings, selected
rows, and sites are consumed on that path; mutation regressions require tree
structure changes to block lowering and RR changes to alter or reject output.

The executable rules are the `(I I O)` Redex judgment `m3-lower`; its named
clauses are live §11 ids, and formed attribution is read from
`build-derivations`, never a manual counter. The display normalizer is a Redex
metafunction applied to both sides, and `SmusniCore` declares canonical
binding forms for λ, `Let`, and sequential `Bind` so comparison uses Redex
`alpha-equivalent?`. The manifest driver deterministically enumerates and
type-checks every fixture derivation; it is not labelled `redex-check`.
`redex-check` is reserved for the bounded `#:satisfying` generator. This Redex
version rejects generation for the judgment's ellipsis patterns, so the report
records seed/attempts/size as unavailable and labels coverage fixture-only
rather than describing it as randomized testing.
