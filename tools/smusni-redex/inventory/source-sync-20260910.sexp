(smusni-document-sync 1
  (source "PM input snapshot 62347a5; adopted v3/P2/P43/P44, F01 excluded")
  (issue "#20")
  (historical-snapshots
    "history/pre-e01-port-corpus.sexp" "history/pre-e01-port-baseline.sexp"
    "Exact pre-E01 snapshots from 7ec9f80 are retained for migration and pilot provenance; the live corpus is independently regenerated from current source and tests.")
  (retired-specimen "spec.md" 9
    "The old witness-set bare numeral is superseded by standard individual global exactness; old spec fence10 is the predecessor of current fence9.")
  (retired-specimen "spec.md" 13
    "The cross-sentence quantified-family artifact was removed by P43. Historical source remains in git at 97a5b44; samples fence42 retains its typed core comparison.")
  (core-comparisons (samples 41 42 48 49) (spec 11)
    "These remain typed corpus specimens. Their live text explicitly disclaims a standard surface lowering; no syntax/type failure motivated reclassification.")
  (unresolved-case "samples.md" 64 2 "#9"
    "The source labels the du'e term a reference-level comparison; L5.28 is now an explicit gap. The term remains checked with the whole fence; no current surface term target is claimed.")
  (retired-lowering "L5.28" "#9"
    "The adopted source reclassified ordinary threshold-count adaptation as a gap. Library threshold helpers remain implemented, but are no longer emitted as L5.28 surface lowerings.")
  (coverage-transition (old-cited 70) (new-cited 69)
    "Exactly one formerly cited judgment, L5.28, left the lowering population. The live source also reclassified L12.5 from an uncovered judgment to a gap. This is a documentary population change, not a lowered test bar.")
  (retired-definition "D12.Additive" "#20"
    "Spec §12 reserves the name for unfinished lexical/target adaptation; the old equation is no longer a live definition. No implementation or fallback is supplied.")
  (changed-definition "D12.Massify"
    "The current equation uses reference-level Refer with existential co-reference to a canonical group. Old SelectExactly 1 is not asserted equivalent.")
  (fixture "batci" "officialdata via jbotci vlacku 2026-09-10"
    "Four ordinary places: biter, bitten, locus, tool. Full lexical adjudication remains #12."))
