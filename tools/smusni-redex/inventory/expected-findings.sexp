(smusni-expected-findings 1
  (finding "samples.md" 52
           "c6fd505895bb18b032697c8e269899709f0c923b"
           type-error
           "legacy angle/comma type spelling"
           "#13"
           "The bare-jai sample still uses the superseded Fn<...> notation instead of §2's flat type spine.")
  (finding "spec.md" 10
           "9401002142f90505a3b1b1d7517603747c96081e"
           type-error
           "expected 'Content, got '(PredTerm bajra 1)"
           "#9,#12,#13"
           "The GlobalExactly display puts event-open bajra $x in a pure SetOf property without defining a pure unary runner projection."))

