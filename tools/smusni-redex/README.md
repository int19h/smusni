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

`Refer` deliberately admits an `EFn` restrictor. Unlike the pure positions
(`SetOf`, quantifier/Generic restrictors, and the `Select*` family), a
description property may sequence retrieval sites; the returned referent is
still introduced by `Refer` itself. This choice is pinned by a positive static
test and must not be generalized to the pure positions.

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

`spec.md` §11 numbers every lowering schema `Ln.m`; the checker reads those
ids from the normative text, never from a copy. Each specimen entry in
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
