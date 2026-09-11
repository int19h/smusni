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
  (case "0361b7fdaa1fd90b87b97a7934892d93cf982dcd")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "B1 preserves the no-diagnostics judgment boundary for this Every domain-mismatch mutation."))
 (waiver
  (case "068cb85ec8ecb3ccc509a1792f79f631c2f91654")
  (fields effects)
  (finding "#13:issuecomment-5458243084")
  (reason
   "The A0 equation executes its effectful function at each paired step; the legacy pass-through omits that application effect."))
 (waiver
  (case "17e08cbac8f779bc4f04b2b480bce8f5a7774d46")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "B1 preserves the no-diagnostics judgment boundary for this newly eligible negative pure-position case."))
 (waiver
  (case "1ae8d66b81c220f5f975851d5f78bfa701a2156a")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
 (waiver
  (case "228ea135aca439f8a9037357f905d482636fa1c2")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "B1 preserves the no-diagnostics judgment boundary for this CoveredBy domain-mismatch mutation."))
 (waiver
  (case "37db005424979d116e258427722bcee539b3f4e4")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
 (waiver
  (case "41639ddaaa12f66e8b6030f81fedc3c3f957080a")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
 (waiver
  (case "41661471fc45cb1b6566ad38c641091bc7bf9e96")
  (fields type)
  (finding "#81")
  (reason
   "CloseClause now exposes the EFn refinement of an effectful event property; the legacy checker incorrectly classified the enclosing lambda as pure."))
 (waiver
  (case "569ded40de1611196c7100eaf0a94b84d2a5324d")
  (fields effects)
  (finding "#13:issuecomment-5458243084")
  (reason
   "The A0 equation executes its effectful function at each paired step; the legacy pass-through omits that application effect."))
 (waiver
  (case "6db1c4b791f0854fe7956e9eaa47adf625c5027d")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "B1 preserves the no-diagnostics judgment boundary for this newly eligible negative pure-position case."))
 (waiver
  (case "79f753ce71d86adc8a504da89297f9a3bf973028")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "B1 preserves the no-diagnostics judgment boundary for this newly eligible negative pure-position case."))
 (waiver
  (case "9179373ca8c2e48ede6fe47086cebd79b7f61352")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "B1 preserves the no-diagnostics judgment boundary for this newly eligible CoveredBy purity rejection."))
 (waiver
  (case "bdd3d191b2cdc13f93625cd4ad2b8bfdcbc997f0")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
 (waiver
  (case "bf9cba2101fca4330c7878635e3eade3cd1d6894")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "B1 preserves the no-diagnostics judgment boundary for this invalid quantifier-domain mutation."))
 (waiver
  (case "ca3ded71dd1e695cfba61b2e74339866dbf5b8a7")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "B1 preserves the no-diagnostics judgment boundary for this newly eligible negative pure-position case."))
 (waiver
  (case "dca2591716f1bddade1e6b1d76605a84e2b5157f")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
 (waiver
  (case "e2ac359a95a348da47b2f9e9763c8f8739435ea8")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
 (waiver
  (case "f7526f02968c2d0f940554bf7559692e5e9de6ea")
  (fields effects)
  (finding "#81")
  (reason
   "DirectClause defaults now remain inside the event property, so Close reports the conservative effectful-call rather than the stale outer context effect."))
 (waiver
  (case "fecc256bfaacdc51a22517ddaf899499179207f8")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
 (waiver
  (case "b1-lowering-668ac22896455289")
  (fields effects)
  (finding "#81")
  (reason
   "The lowering-derived ClauseContent now preserves the latent EFn call from its corrected inner DirectClause defaults."))
 (waiver
  (case "b1-lowering-9a4b45a97730a6c7")
  (fields effects)
  (finding "#81")
  (reason
   "The lowering-derived ClauseContent now preserves the latent EFn call from its corrected inner DirectClause defaults.")))
