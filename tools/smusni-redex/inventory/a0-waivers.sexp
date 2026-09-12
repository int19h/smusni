(smusni-port-waivers
 1
 (waiver
  (case "a0-zipwith-empty-effectful")
  (fields status type failure-class source-rule derivations)
  (finding "#13:issuecomment-5458243084")
  (reason
   "A0 types the literal empty lists without executing the effectful function; the legacy pass-through crashes while unequal-length meaning remains blocked by issue 41."))
 (waiver
  (case "b1-every")
  (fields effects obligations)
  (finding "#13:issuecomment-5459255275")
  (reason
   "B1 restores MaxRefer projective emission and its structured inhabitedness obligation."))
 (waiver
  (case "b1-fewer-zero")
  (fields effects)
  (finding "#13:issuecomment-5459255275")
  (reason
   "The literal-zero expansion is negated truth and never executes the nuclear property."))
 (waiver
  (case "b1-distrib")
  (fields effects)
  (finding "#13:issuecomment-5459255275")
  (reason
   "The executable universal distribution calls its effectful member property."))
 (waiver
  (case "b1-overlap")
  (fields status type gaps)
  (finding "#13:issuecomment-5459255275")
  (reason
   "B1 replaces the legacy missing-rule gap with the executable existential overlap definition."))
 (waiver
  (case "b1-max-refer")
  (fields
   status
   type
   effects
   obligations
   failure-class
   source-rule
   derivations)
  (finding "#13:issuecomment-5459255275")
  (reason
   "B1 supplies the formerly missing maximal-reference computation and its structured import."))
 (waiver
  (case "b1-presuppose")
  (fields status obligations gaps)
  (finding "#13:issuecomment-5459255275")
  (reason
   "B1 replaces the bounded legacy gap with structured alpha-compared presupposition obligations."))
 (waiver
  (case "b1-negation")
  (fields effects)
  (finding "#13:issuecomment-5459255275")
  (reason
   "Generic B1 negation masks escaping refer while retaining all other effects and obligations."))
 (waiver
  (case "b1-addition")
  (fields type)
  (finding "#13:issuecomment-5459255275")
  (reason
   "B1 preserves the Natural join sort for Natural addition instead of widening it to Number."))
 (waiver
  (case "a0-close")
  (fields effects)
  (finding "#81")
  (reason
   "The corrected direct-event Close template keeps omitted-place retrieval inside the event property and exposes it as an effectful call."))
 (waiver
  (case "a0-close-explicit-event")
  (fields effects)
  (finding "#81")
  (reason
   "The corrected explicit-event Close template keeps omitted-place retrieval inside the lexical event property and exposes it as an effectful call."))
 (waiver
  (case "2d088f8d691dcc1adf31b20f0c9bb570601ced32")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "B1 preserves the no-diagnostics judgment boundary for this Every domain-mismatch mutation."))
 (waiver
  (case "a68369220eb4bbe39b3cbb37c47bec9b92c90505")
  (fields effects)
  (finding "#13:issuecomment-5458243084")
  (reason
   "The A0 equation executes its effectful function at each paired step; the legacy pass-through omits that application effect."))
 (waiver
  (case "278b32f45d29d4e8d5fed713c411a6f38189d0d5")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "B1 preserves the no-diagnostics judgment boundary for this newly eligible negative pure-position case."))
 (waiver
  (case "a7ca422686b006064a8f88b18ab5d3b0b4096653")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
 (waiver
  (case "ddfc00e6e2ae96b94a3feeafcff526ffc2b843fa")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "B1 preserves the no-diagnostics judgment boundary for this CoveredBy domain-mismatch mutation."))
 (waiver
  (case "065a3d039ea0846c5397d1eae7579772e32995d2")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
 (waiver
  (case "97c577c75a80447f3e3e564e0681b9b8c58577b8")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
 (waiver
  (case "6ef69cef9f9571b0ced4e7a84d44841a1e2307bd")
  (fields type)
  (finding "#81")
  (reason
   "CloseClause now exposes the EFn refinement of an effectful event property; the legacy checker incorrectly classified the enclosing lambda as pure."))
 (waiver
  (case "c20b6fa30bbd410632e7861b0ed06ac7eecdceec")
  (fields effects)
  (finding "#13:issuecomment-5458243084")
  (reason
   "The A0 equation executes its effectful function at each paired step; the legacy pass-through omits that application effect."))
 (waiver
  (case "e8d8c6f4db003a0d4acec21b95d5ce387007ca05")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "B1 preserves the no-diagnostics judgment boundary for this newly eligible negative pure-position case."))
 (waiver
  (case "a6aff88d96c8efbf4065d5012ddf25a7ed4a52ea")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "B1 preserves the no-diagnostics judgment boundary for this newly eligible negative pure-position case."))
 (waiver
  (case "6c2254c6498b1b5f51135572617077056761c3ba")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "B1 preserves the no-diagnostics judgment boundary for this newly eligible CoveredBy purity rejection."))
 (waiver
  (case "0b789589437436561ad8b9caf066aead525ef817")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
 (waiver
  (case "713afb4443ade46e64c47f3a952f993daf4603b0")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "B1 preserves the no-diagnostics judgment boundary for this invalid quantifier-domain mutation."))
 (waiver
  (case "65def4c44fa49728749081bb493458c91c6a31c1")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "B1 preserves the no-diagnostics judgment boundary for this newly eligible negative pure-position case."))
 (waiver
  (case "3c72601f5d9e78fbd5fedb746aa7e1c77017b4d3")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
 (waiver
  (case "890ee3d26b930a00cad64274799fa9df65693931")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
 (waiver
  (case "fbd0a28c2d108321bd60bbb032163b6a87d600f5")
  (fields effects)
  (finding "#81")
  (reason
   "DirectClause defaults now remain inside the event property, so Close reports the conservative effectful-call rather than the stale outer context effect."))
 (waiver
  (case "4bb09f0a9dc7ffb0058871b5dbbe0880a7f580c9")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
 (waiver
   (case "b1-lowering-49efe161ccee6531")
  (fields effects)
  (finding "#81")
  (reason
   "The lowering-derived ClauseContent now preserves the latent EFn call from its corrected inner DirectClause defaults."))
 (waiver
   (case "b1-lowering-070f5fba29ef5fc0")
  (fields effects)
  (finding "#81")
  (reason
   "The lowering-derived ClauseContent now preserves the latent EFn call from its corrected inner DirectClause defaults.")))
