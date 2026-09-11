# E02: one outer Assert context bridge

Current P45 fidelity result: [`E02_NEGATION_FIDELITY.md`](E02_NEGATION_FIDELITY.md).
The later generic negation correction resolves the four failures exposed by
the strengthened consumer; all consumer gates remain in force.

Correction: [`E02_CONSUMER_BATCH01.md`](E02_CONSUMER_BATCH01.md) supersedes
the original successful typed-parity claim below. Four retained rejection ASTs
had been counted; checkpoint eb72540 reported them and failed M2.
The 74 independent A0-typed oracle targets themselves remain unchanged.

Implementation follows PM's obligation-preserving release
`msg_20260911T015146004382Z_9b7abac205cc4cb29fc9097b64fba3c9`, recorded on #74.
Base checkpoint: `3a7edfc`; semantic input remains `18cd626`.
Independent review is pending. No frozen E01 engine or semantic documents
were changed. F01, E03, wider contexts and checking-only source admission
remain outside this tranche.

## Mechanism and evidence

`pilot/shared/export_m2_redex_oracle.rkt` admits literally one root
`(Assert C)` with one operand. It independently obtains a unique frozen A0
synthesis of C whose type is **literally Content**, completely expands C,
then requires a unique A0 check of C′ at Content. It publishes `(Assert C′)`,
not a local payload comparison. No Lean result, case ID, permissive legacy
inference, or fictitious Fn declaration for Assert determines admission.

The actual port environment and lexical fixture arity/event mode supply
declarations before payload typing. Unknown/inconsistent CloseWith rows,
conflicting declarations and missing free-variable declarations fail closed;
no row is filled with an invented default. Unsupported contextual vocabulary
is distinguished from actual A0 grammar failure and from unclassified zero
derivations. The bridge is not recursive: nested Assert is not Content;
Express/Mention/Ask/Polar/sign/Do and root bindings containing Assert are not
silently admitted. Reify can fit generic application syntax without having
an admitted rule, so it is not labelled a grammar or semantic type error.

Every selected definition redex passes a frozen A0 guard, including redexes
introduced during expansion. Checking-only definition guards use their
declared result types from actual operands (SelectSome/MaxRefer/Massify);
this does not add checking-only **source payload** admission. Known
metafunction limitations for symbolic AtLeast, nonliteral Exactly and
nonconcrete/unequal ZipWith are explicit expansion-domain failures.
The CoveredBy dependency path now traverses the same guarded expansion
function rather than bypassing it in a helper. A final residual-definition
check prevents an unexpanded selected redex from becoming an available target.
The member-Refer overload is detected using its actual property typing and
binding environment, not merely a lambda or symbol spelling.

## Assert certificate and consumer

Oracle format version 2 records `context = whole-a0 | assert-bridge` and
source/target typing witnesses. Bridge records additionally carry both
payload witnesses. The two Act witnesses have type Act Assertion, empty
immediate effects, and **the corresponding payload's obligation metadata**.
Payload effects and obligations need not be empty. No obligations are
executed, discharged or erased at act construction. This is exactly the
existing §7.1 / frozen `suspend-results` interface, not a new projection rule.

The exporter checks its context certificate against the independently
obtained source and target A0 records. The Lean consumer rejects wrapper
stripping, changed type/effect/obligation records, missing evidence, duplicate
fields/cases, unknown context markers, and unavailable records carrying a
usable target. A bridge record must also join to an actual outer Assert in
the original corpus. Non-admission categories are parsed explicitly and
never treated as available; an all-unavailable oracle fails the empty guard.

The new theorem `assertOracleWitness_preserves_metadata` proves that every
successful witness construction empties immediate effects and preserves the
payload obligation list. It is a context-metadata theorem, not a Lean replay
proof of Redex derivations. The oracle producer remains trusted to obtain
those actual A0 judgments; it does not depend on the candidate Lean result.
Existing bidirectional typing/certificate soundness and their declared
domains are unchanged.

## Current populations

The source-derived **192-case selection is unchanged**. Current whole-term
typed parity is 74: 54 ordinary whole-A0 targets plus 20 Assert-bridge targets.
All 74 term comparisons and all 74 site-signature comparisons match; zero
differences. There are no local-only comparisons masquerading as whole terms.

The remaining 118 candidates are explicitly nonavailable:

| Category | Count |
| --- | ---: |
| context-unsupported | 71 |
| grammar-unsupported | 25 |
| unclassified-non-admission | 22 |
| type/domain-rejected | 0 |
| expansion-domain-unavailable | 0 |
| malformed-input | 0 |

The zero categories are exercised by required synthetic controls, not omitted
from the protocol. Zero A0 derivations are not semantic ill-typing evidence.
The number 118 here is coincidental, not restoration of the old untyped oracle
or a population acceptance target. Broader contextual and expected-mode
typing require their own scoped work; this is not all-S1 exact parity.

All-S1 Lean results remain 370 cases, 31 unchanged and 157 successful
expansions, with 188/188 successful output typings inside the independent
59-rule soundness domain and 51 explicit rule exclusions. Other case and
proof limits are unchanged from `M2_REPORT.md`'s migration checkpoint.

## Required controls and validation

The exporter has 111 passing assertions. Controls include non-Content payloads,
unclosed ClauseContent, malformed/nested Assert, all required unsupported
contexts, declared EFn and unseen equivalent, effectful member lambda and
function-returning construction, member/reference mismatch, a valid Some
equation inside pure-invalid SetOf, wrapper stripping, obligation dropping,
residual definitions, injected expansion-chain guard failure, unexpected
exceptions, missing/conflicting lexical input, and explicit count/list
metafunction boundaries. Pure member, Assert CloseWith, and projective
Assert Presuppose controls remain positive. These are mechanism tests;
no production branch selects an output or admission by a fixture ID.

Lean additionally runs independent certificate/empty-oracle mutations and
proves the metadata law (axioms: propext only). Existing public synthesis and
checking soundness still report only propext/Classical.choice/Quot.sound.

Completed validation commands:

- `./pilot/lean/check-m2.sh`: PASS; 111 exporter assertions, all Lean controls,
  74 term/site matches and 188/188 output typing coverage; 24.74 s wall,
  345,732 KiB maximum RSS in the final incremental run.
- `./pilot/lean/check-m1.sh`: PASS; 370 surface/text round trips, 51 primitive
  core round trips and 303 generated round trips; 2.68 s wall,
  1,665,228 KiB maximum RSS.
- `tools/check-smusni`: PASS; 3,464 Racket tests, 8 Python tests,
  370-case identity differential with no differences, 114-case A0/B1
  differential with no differences and 32 existing field-scoped waivers;
  148.97 s wall, 376,872 KiB maximum RSS.
- Tracked document checker and `git diff --check`: PASS.

Final root inventory/fence and complete M1/M2 regeneration was byte-identical.
The exact commit is recorded in the durable handoff.

No push, merge, self-solicited review, subagent, semantic-authority transfer,
or broader oracle-context implementation is included.
