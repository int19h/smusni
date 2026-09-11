# Lean milestone 1 pinned inputs

These artifacts fix the Lean M1 constructor and S1 inputs before any
`CoreTerm` constructor is written. They are derived pilot data, not semantic
authority.

## Constructor disposition

`M1_CONSTRUCTOR_DISPOSITION.tsv` joins four live sources at main
`892a7040d4f3786be42635089b6aac7743ba6b74`:

- `tools/smusni-redex/inventory/core.sexp`;
- `tools/smusni-redex/inventory/definitions.sexp`;
- the `SmusniA0` grammar in `tools/smusni-redex/port-a0.rkt`; and
- `spec.md` §3.4–§3.5 and Appendix “the kernel.”

Namespaces are explicit (`sort:`, `type-form:`, `type:`, `term:`), so a type
former and a term constructor with the same printed head are not collapsed.
Every row has exactly one of the five brief-prescribed dispositions:

| disposition | count |
|---|---:|
| `primitive-core` | 121 |
| `defined-surface` | 84 |
| `type-index-data` | 70 |
| `gap-prose-only` | 6 |
| `tool-only` | 5 |

The generator hard-fails on an unknown A0 term head, an unclassified structural
core form, or a primitive/defined/data conflict. Source SHA-256 values are in
the matrix header. Run:

```sh
python3 pilot/shared/build_m1_constructor_matrix.py
```

## S1 partition

`M1_S1_MANIFEST.json` partitions all 337 frozen `port-corpus.sexp` cases by
their recursively observed constructor heads:

| tag | count | M1 disposition |
|---|---:|---|
| `primitive-core` | 51 | decode and round-trip as `CoreTerm` in M1 |
| `pending-milestone-2` | 264 | decode as `SurfaceTerm`; typed elaboration waits for M2 |
| `out-of-slice` | 22 | schematic/placeholder/declaration cases with every offending head named |

Both verified L5.30 fence cases are present and tagged
`pending-milestone-2`. The manifest also pins 29 RR fixtures and 31 parse
fixtures (60 typed records total), including both structural/skeleton probe
files, with per-file SHA-256 values. It records the port-corpus digest and both
inventory hashes carried by every frozen case. Run:

```sh
python3 pilot/shared/build_m1_s1_manifest.py
```

`SurfaceTerm` is transport/elaboration input and has no denotation. RR,
gentufa parse, corpus, and manifest records remain typed records; they are not
misrepresented as terms. No corpus term is embedded as a Lean literal by
these input builders.

The manifest's `base_head` is the semantic selection snapshot. Its per-file
digests include the M1 syntax-only normalization that removes one previously
ignored trailing `)` from 28 RR fixtures; the manifest records that delta
explicitly. The parsed RR datum in every corrected file is unchanged.
