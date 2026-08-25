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

Generated files under `corpus/` are checked in for review. Regenerate them
with:

```sh
racket tools/smusni-redex/extract.rkt --write
```

Do not hand-edit generated corpus files.
