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
  (case "7bcd8dc2f4961a8b551b2d2258b1c8e26d59a3bc")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "B1 preserves the no-diagnostics judgment boundary for this Every domain-mismatch mutation."))
 (waiver
  (case "62ef9d2abb3071b0cc188c169d027c46b0ce41fd")
  (fields effects)
  (finding "#13:issuecomment-5458243084")
  (reason
   "The A0 equation executes its effectful function at each paired step; the legacy pass-through omits that application effect."))
 (waiver
  (case "b9fc9816e545772460d20961c1932bbf3e7ae53c")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "B1 preserves the no-diagnostics judgment boundary for this newly eligible negative pure-position case."))
 (waiver
  (case "09f0948ce98ba5c5c10172f02e84d769c77fc947")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
 (waiver
  (case "74d0212bae121f9f6f818fd874766bf175e0fc4b")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "B1 preserves the no-diagnostics judgment boundary for this CoveredBy domain-mismatch mutation."))
 (waiver
  (case "c7c22c1e196d02ebc70afdc94b4dae9476772913")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
 (waiver
  (case "2b338049c10e9453426315140e2d00875af639d9")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
 (waiver
  (case "4981a00f42ced6494624933b2573328a83445aed")
  (fields type)
  (finding "#81")
  (reason
   "CloseClause now exposes the EFn refinement of an effectful event property; the legacy checker incorrectly classified the enclosing lambda as pure."))
 (waiver
  (case "05bb8ad1ae173cc81f1f84b69b295fff82b9c9f2")
  (fields effects)
  (finding "#13:issuecomment-5458243084")
  (reason
   "The A0 equation executes its effectful function at each paired step; the legacy pass-through omits that application effect."))
 (waiver
  (case "059ad6f2adf9d4a2cf81693ee14b6f3b5ea49562")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "B1 preserves the no-diagnostics judgment boundary for this newly eligible negative pure-position case."))
 (waiver
  (case "dea28886c2b9a331b99bd06cbdbf0f84f8a18d7a")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "B1 preserves the no-diagnostics judgment boundary for this newly eligible negative pure-position case."))
 (waiver
  (case "2a00f8ca5df0ba140dbe29fa18c0acda9b274913")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "B1 preserves the no-diagnostics judgment boundary for this newly eligible CoveredBy purity rejection."))
 (waiver
  (case "a7dc745e8ebce5f8e1e04767521823f6cdbdbc7c")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
 (waiver
  (case "2272d4a81ceb6bc5583cc03cc024895db0d0ac62")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "B1 preserves the no-diagnostics judgment boundary for this invalid quantifier-domain mutation."))
 (waiver
  (case "010a22f419f0e4714289ac20673998b765002c77")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "B1 preserves the no-diagnostics judgment boundary for this newly eligible negative pure-position case."))
 (waiver
  (case "84dfb76d571acff8ff6909c051c6b8221a347eb3")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
 (waiver
  (case "d3636a7baf7c40fc35eb5863a56c40cc33b5e59a")
  (fields failure-class)
  (finding "#52:issuecomment-5458132092")
  (reason
   "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
 (waiver
  (case "42171935390224ab5042ee63543b3d03e33f6009")
  (fields effects)
  (finding "#81")
  (reason
   "DirectClause defaults now remain inside the event property, so Close reports the conservative effectful-call rather than the stale outer context effect."))
 (waiver
  (case "2350ec46a860b191ed7dfc8805106543d00813c7")
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
