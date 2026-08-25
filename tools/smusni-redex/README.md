# Smusni Redex checker

This directory contains a derived checker for the notation and selected
static laws in `spec.md`. It is not a semantic authority: when the checker and
the documents disagree, the discrepancy must be diagnosed against the live
normative text.

Milestone 1 covers the declaration mirror, exhaustive classification of the
Markdown `lisp` fences, the concrete reader, elaboration, extrinsic typing,
and the static regression ledger. Dynamic execution, Lojban lowering, finite
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

Generated files under `corpus/` are checked in for review. Regenerate them
with:

```sh
racket tools/smusni-redex/extract.rkt --write
```

Do not hand-edit generated corpus files.

