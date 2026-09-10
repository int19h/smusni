(smusni-waiver-transition
 1
 (source-commit "7ec9f80")
 (reason
  "Inventory digests are part of case identities. Exact/alpha-identical terms and environments transport their existing field-scoped findings. Two adopted individual-closure consumers retain the independently recorded CloseClause effect refinement #81. No additional field is waived.")
 (previous-waivers
  (waiver
   (case "04cdfd2f45e14a4ad9d525b9aa39518337dfe160")
   (fields effects)
   (finding "#13:issuecomment-5458243084")
   (reason
    "The A0 equation executes its effectful function at each paired step; the legacy pass-through omits that application effect."))
  (waiver
   (case "5f5b053a4dcccf2858daa126fd3d854e0e78d516")
   (fields effects)
   (finding "#13:issuecomment-5458243084")
   (reason
    "The A0 equation executes its effectful function at each paired step; the legacy pass-through omits that application effect."))
  (waiver
   (case "a0-zipwith-empty-effectful")
   (fields status type failure-class source-rule derivations)
   (finding "#13:issuecomment-5458243084")
   (reason
    "A0 types the literal empty lists without executing the effectful function; the legacy pass-through crashes while unequal-length meaning remains blocked by issue 41."))
  (waiver
   (case "27f27c1038df83b40e16a919fdaf24b405d04b04")
   (fields failure-class)
   (finding "#52:issuecomment-5458132092")
   (reason
    "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
  (waiver
   (case "4955a8c68f8935068ee2677cd187fc98421260f7")
   (fields failure-class)
   (finding "#52:issuecomment-5458132092")
   (reason
    "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
  (waiver
   (case "58c6ffc749c2646868481de082505374ffabf2df")
   (fields failure-class)
   (finding "#52:issuecomment-5458132092")
   (reason
    "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
  (waiver
   (case "7482cccbaa630047b71bb8f648818fa1359ddf68")
   (fields failure-class)
   (finding "#52:issuecomment-5458132092")
   (reason
    "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
  (waiver
   (case "84d3f3f5db6d9bb097e9df301673052e73e0649a")
   (fields failure-class)
   (finding "#52:issuecomment-5458132092")
   (reason
    "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
  (waiver
   (case "8e29fcd7ea73a0b92af918404558667876eff43a")
   (fields failure-class)
   (finding "#52:issuecomment-5458132092")
   (reason
    "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
  (waiver
   (case "fb5015ae6fdfa682c9b7f70814a49daf00df1d91")
   (fields failure-class)
   (finding "#52:issuecomment-5458132092")
   (reason
    "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
  (waiver
   (case "24a8f6ee7b1b963841362803c17af2271ae6a6d9")
   (fields failure-class)
   (finding "#52:issuecomment-5458132092")
   (reason
    "B1 preserves the no-diagnostics judgment boundary for this newly eligible negative pure-position case."))
  (waiver
   (case "6f7179b2bc813a079360002fde1531d22f13075a")
   (fields failure-class)
   (finding "#52:issuecomment-5458132092")
   (reason
    "B1 preserves the no-diagnostics judgment boundary for this newly eligible negative pure-position case."))
  (waiver
   (case "7318097d39a3fd427b8496b52e0a9c8c908bd088")
   (fields failure-class)
   (finding "#52:issuecomment-5458132092")
   (reason
    "B1 preserves the no-diagnostics judgment boundary for this newly eligible CoveredBy purity rejection."))
  (waiver
   (case "8c9b8391ccb99eb35ea47ede0725496776f25689")
   (fields failure-class)
   (finding "#52:issuecomment-5458132092")
   (reason
    "B1 preserves the no-diagnostics judgment boundary for this newly eligible negative pure-position case."))
  (waiver
   (case "98f77d55dfa9fd511bb856c6dd96598f1a9809c9")
   (fields failure-class)
   (finding "#52:issuecomment-5458132092")
   (reason
    "B1 preserves the no-diagnostics judgment boundary for this invalid quantifier-domain mutation."))
  (waiver
   (case "9950bcb96b07982d231b52cb8af364c40cb79561")
   (fields failure-class)
   (finding "#52:issuecomment-5458132092")
   (reason
    "B1 preserves the no-diagnostics judgment boundary for this Every domain-mismatch mutation."))
  (waiver
   (case "cb8093665b4b7ed893a755ddf7595d703673c951")
   (fields failure-class)
   (finding "#52:issuecomment-5458132092")
   (reason
    "B1 preserves the no-diagnostics judgment boundary for this newly eligible negative pure-position case."))
  (waiver
   (case "d8e9f58244e983851351b588de235d4375f926f0")
   (fields failure-class)
   (finding "#52:issuecomment-5458132092")
   (reason
    "B1 preserves the no-diagnostics judgment boundary for this CoveredBy domain-mismatch mutation."))
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
   (case "b1-lowering-58446186c6fa7dbc")
   (fields effects obligations)
   (finding "#13:issuecomment-5459255275")
   (reason
    "The lowering-derived Every subterm inherits MaxRefer projective import in B1."))
  (waiver
   (case "b1-lowering-7c491742d3d8fff2")
   (fields effects obligations)
   (finding "#13:issuecomment-5459255275")
   (reason
    "The lowering-derived Every subterm inherits MaxRefer projective import in B1."))
  (waiver
   (case "b1-lowering-4268934806d322ae")
   (fields effects obligations)
   (finding "#13:issuecomment-5459255275")
   (reason
    "The lowering-derived nested Every subterm inherits MaxRefer projective import in B1."))
  (waiver
   (case "06465575093b9abc8b8c2d7cbeed038ba08c7707")
   (fields type)
   (finding "#81")
   (reason
    "CloseClause now exposes the EFn refinement of an effectful event property; the legacy checker incorrectly classified the enclosing lambda as pure."))
  (waiver
   (case "4cc6a45509151b5a0827ca4741f05c3e9e3afb8c")
   (fields effects)
   (finding "#81")
   (reason
    "DirectClause defaults now remain inside the event property, so Close reports the conservative effectful-call rather than the stale outer context effect."))
  (waiver
   (case "c27acb49649a24ec94cecaf88567f2d8e9165026")
   (fields effects)
   (finding "#81")
   (reason
    "DirectClause defaults now remain inside the event property, so Close reports the conservative effectful-call rather than the stale outer context effect."))
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
   (case "b1-lowering-c28906129a38b214")
   (fields effects)
   (finding "#81")
   (reason
    "The lowering-derived ClauseContent now preserves the latent EFn call from its corrected inner DirectClause defaults."))
  (waiver
   (case "b1-lowering-5490abdf57992a66")
   (fields effects)
   (finding "#81")
   (reason
    "The lowering-derived ClauseContent now preserves the latent EFn call from its corrected inner DirectClause defaults.")))
 (transports
  (transport
   (waiver
    (case "9950bcb96b07982d231b52cb8af364c40cb79561")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason
     "B1 preserves the no-diagnostics judgment boundary for this Every domain-mismatch mutation."))
   (waiver
    (case "0361b7fdaa1fd90b87b97a7934892d93cf982dcd")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason
     "B1 preserves the no-diagnostics judgment boundary for this Every domain-mismatch mutation."))
   (current-term
    (Every
     (λ ($x :: Entity) (gerku $x))
     (λ ($w :: Referents Entity) (Close (jmaji $w)))))
   (old-record
    "#(struct:port-record rejection #f () () () typing-failure Every \"0361b7fdaa1fd90b87b97a7934892d93cf982dcd:?:?: Every restrictor/nuclear domain mismatch: 'Entity versus '(Referents Entity)\" 0)")
   (new-record
    "#(struct:port-record rejection #f () () () no-derivation Every \"A0 derivations: 0\" 0)"))
  (transport
   (waiver
    (case "04cdfd2f45e14a4ad9d525b9aa39518337dfe160")
    (fields effects)
    (finding "#13:issuecomment-5458243084")
    (reason
     "The A0 equation executes its effectful function at each paired step; the legacy pass-through omits that application effect."))
   (waiver
    (case "068cb85ec8ecb3ccc509a1792f79f631c2f91654")
    (fields effects)
    (finding "#13:issuecomment-5458243084")
    (reason
     "The A0 equation executes its effectful function at each paired step; the legacy pass-through omits that application effect."))
   (current-term
    (ZipWith
     (λ ($left $right :: Referents Entity) (Close (tavla $left $right)))
     (List Speaker Audience)
     (List Audience Speaker)))
   (old-record "#(struct:port-record success Content () () () #f #f #f 1)")
   (new-record
    "#(struct:port-record success Content (effectful-call) () () #f #f #f 1)"))
  (transport
   (waiver
    (case "8c9b8391ccb99eb35ea47ede0725496776f25689")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason
     "B1 preserves the no-diagnostics judgment boundary for this newly eligible negative pure-position case."))
   (waiver
    (case "17e08cbac8f779bc4f04b2b480bce8f5a7774d46")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason
     "B1 preserves the no-diagnostics judgment boundary for this newly eligible negative pure-position case."))
   (current-term (SetOf (λ ($x :: Entity) (Presuppose (gerku $x) (gerku $x)))))
   (old-record
    "#(struct:port-record rejection #f () () () typing-failure SetOf \"17e08cbac8f779bc4f04b2b480bce8f5a7774d46:?:?: SetOf property must be a pure Fn under L0.1\" 0)")
   (new-record
    "#(struct:port-record rejection #f () () () no-derivation SetOf \"A0 derivations: 0\" 0)"))
  (transport
   (waiver
    (case "fb5015ae6fdfa682c9b7f70814a49daf00df1d91")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason
     "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
   (waiver
    (case "1ae8d66b81c220f5f975851d5f78bfa701a2156a")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason
     "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
   (current-term
    (SetOf
     (λ ($z :: Entity)
       (Exactly
        1
        (λ ($x :: Entity) (gerku $x))
        (λ ($w :: Referents Entity) (Close (jmaji $w)))))))
   (old-record
    "#(struct:port-record rejection #f () () () typing-failure SetOf \"1ae8d66b81c220f5f975851d5f78bfa701a2156a:?:?: SetOf property must be a pure Fn under L0.1\" 0)")
   (new-record
    "#(struct:port-record rejection #f () () () no-derivation SetOf \"A0 derivations: 0\" 0)"))
  (transport
   (waiver
    (case "d8e9f58244e983851351b588de235d4375f926f0")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason
     "B1 preserves the no-diagnostics judgment boundary for this CoveredBy domain-mismatch mutation."))
   (waiver
    (case "228ea135aca439f8a9037357f905d482636fa1c2")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason
     "B1 preserves the no-diagnostics judgment boundary for this CoveredBy domain-mismatch mutation."))
   (current-term
    (λ (($p :: Fn (Eventuality) Content) ($r :: Referents Entity))
      (CoveredBy $p $r)))
   (old-record
    "#(struct:port-record rejection #f () () () typing-failure λ \"228ea135aca439f8a9037357f905d482636fa1c2:?:?: CoveredBy property/reference type mismatch\" 0)")
   (new-record
    "#(struct:port-record rejection #f () () () no-derivation λ \"A0 derivations: 0\" 0)"))
  (transport
   (waiver
    (case "8e29fcd7ea73a0b92af918404558667876eff43a")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason
     "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
   (waiver
    (case "37db005424979d116e258427722bcee539b3f4e4")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason
     "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
   (current-term
    (λ ($f :: EFn ((Referents Entity)) Content)
      (SetOf (λ ($x :: Entity) ($f $x)))))
   (old-record
    "#(struct:port-record rejection #f () () () typing-failure λ \"37db005424979d116e258427722bcee539b3f4e4:?:?: SetOf property must be a pure Fn under L0.1\" 0)")
   (new-record
    "#(struct:port-record rejection #f () () () no-derivation λ \"A0 derivations: 0\" 0)"))
  (transport
   (waiver
    (case "27f27c1038df83b40e16a919fdaf24b405d04b04")
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
   (current-term
    (SetOf
     (λ ($z :: Entity)
       (MoreThan
        0
        (λ ($x :: Entity) (gerku $x))
        (λ ($w :: Referents Entity) (Close (jmaji $w)))))))
   (old-record
    "#(struct:port-record rejection #f () () () typing-failure SetOf \"41639ddaaa12f66e8b6030f81fedc3c3f957080a:?:?: SetOf property must be a pure Fn under L0.1\" 0)")
   (new-record
    "#(struct:port-record rejection #f () () () no-derivation SetOf \"A0 derivations: 0\" 0)"))
  (transport
   (waiver
    (case "06465575093b9abc8b8c2d7cbeed038ba08c7707")
    (fields type)
    (finding "#81")
    (reason
     "CloseClause now exposes the EFn refinement of an effectful event property; the legacy checker incorrectly classified the enclosing lambda as pure."))
   (waiver
    (case "41661471fc45cb1b6566ad38c641091bc7bf9e96")
    (fields type)
    (finding "#81")
    (reason
     "CloseClause now exposes the EFn refinement of an effectful event property; the legacy checker incorrectly classified the enclosing lambda as pure."))
   (current-term
    (λ ($c :: EFn ((Referents Eventuality)) Content) (CloseClause $c)))
   (old-record
    "#(struct:port-record success (Fn ((EFn ((Referents Eventuality)) Content)) Content) () () () #f #f #f 1)")
   (new-record
    "#(struct:port-record success (EFn ((EFn ((Referents Eventuality)) Content)) Content) () () () #f #f #f 1)"))
  (transport
   (waiver
    (case "04cdfd2f45e14a4ad9d525b9aa39518337dfe160")
    (fields effects)
    (finding "#13:issuecomment-5458243084")
    (reason
     "The A0 equation executes its effectful function at each paired step; the legacy pass-through omits that application effect."))
   (waiver
    (case "569ded40de1611196c7100eaf0a94b84d2a5324d")
    (fields effects)
    (finding "#13:issuecomment-5458243084")
    (reason
     "The A0 equation executes its effectful function at each paired step; the legacy pass-through omits that application effect."))
   (current-term
    (ZipWith
     (λ ($s $l :: Referents Entity) (Close (tavla $s $l)))
     (List Speaker Audience)
     (List Audience Speaker)))
   (old-record "#(struct:port-record success Content () () () #f #f #f 1)")
   (new-record
    "#(struct:port-record success Content (effectful-call) () () #f #f #f 1)"))
  (transport
   (waiver
    (case "cb8093665b4b7ed893a755ddf7595d703673c951")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason
     "B1 preserves the no-diagnostics judgment boundary for this newly eligible negative pure-position case."))
   (waiver
    (case "6db1c4b791f0854fe7956e9eaa47adf625c5027d")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason
     "B1 preserves the no-diagnostics judgment boundary for this newly eligible negative pure-position case."))
   (current-term
    (SetOf
     (λ ($z :: Entity)
       (Some
        (λ ($x :: Entity) (gerku $x))
        (λ ($w :: Referents Entity) (Close (jmaji $w)))))))
   (old-record
    "#(struct:port-record rejection #f () () () typing-failure SetOf \"6db1c4b791f0854fe7956e9eaa47adf625c5027d:?:?: SetOf property must be a pure Fn under L0.1\" 0)")
   (new-record
    "#(struct:port-record rejection #f () () () no-derivation SetOf \"A0 derivations: 0\" 0)"))
  (transport
   (waiver
    (case "24a8f6ee7b1b963841362803c17af2271ae6a6d9")
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
   (current-term
    (SetOf
     (λ ($z :: Entity)
       (AtLeast
        1
        (λ ($x :: Entity) (gerku $x))
        (λ ($w :: Referents Entity) (Close (jmaji $w)))))))
   (old-record
    "#(struct:port-record rejection #f () () () typing-failure SetOf \"79f753ce71d86adc8a504da89297f9a3bf973028:?:?: SetOf property must be a pure Fn under L0.1\" 0)")
   (new-record
    "#(struct:port-record rejection #f () () () no-derivation SetOf \"A0 derivations: 0\" 0)"))
  (transport
   (waiver
    (case "7318097d39a3fd427b8496b52e0a9c8c908bd088")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason
     "B1 preserves the no-diagnostics judgment boundary for this newly eligible CoveredBy purity rejection."))
   (waiver
    (case "9179373ca8c2e48ede6fe47086cebd79b7f61352")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason
     "B1 preserves the no-diagnostics judgment boundary for this newly eligible CoveredBy purity rejection."))
   (current-term
    (λ (($p :: EFn (Entity) Content) ($r :: Referents Entity))
      (CoveredBy $p $r)))
   (old-record
    "#(struct:port-record rejection #f () () () typing-failure λ \"9179373ca8c2e48ede6fe47086cebd79b7f61352:?:?: CoveredBy types are incompatible: '(EFn (Entity) Content), '(Referents Entity)\" 0)")
   (new-record
    "#(struct:port-record rejection #f () () () no-derivation λ \"A0 derivations: 0\" 0)"))
  (transport
   (waiver
    (case "4955a8c68f8935068ee2677cd187fc98421260f7")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason
     "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
   (waiver
    (case "bdd3d191b2cdc13f93625cd4ad2b8bfdcbc997f0")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason
     "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
   (current-term
    (SetOf
     (λ ($z :: Entity)
       (GlobalExactly
        1
        (λ ($x :: Entity) (gerku $x))
        (λ ($x :: Entity) (Close (jmaji $x)))))))
   (old-record
    "#(struct:port-record rejection #f () () () typing-failure SetOf \"bdd3d191b2cdc13f93625cd4ad2b8bfdcbc997f0:?:?: SetOf property must be a pure Fn under L0.1\" 0)")
   (new-record
    "#(struct:port-record rejection #f () () () no-derivation SetOf \"A0 derivations: 0\" 0)"))
  (transport
   (waiver
    (case "98f77d55dfa9fd511bb856c6dd96598f1a9809c9")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason
     "B1 preserves the no-diagnostics judgment boundary for this invalid quantifier-domain mutation."))
   (waiver
    (case "bf9cba2101fca4330c7878635e3eade3cd1d6894")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason
     "B1 preserves the no-diagnostics judgment boundary for this invalid quantifier-domain mutation."))
   (current-term (∃ (λ ($c :: Content) $c)))
   (old-record
    "#(struct:port-record rejection #f () () () typing-failure ∃ \"bf9cba2101fca4330c7878635e3eade3cd1d6894:?:?: quantifier domains must be first-order/referential, got '(Content)\" 0)")
   (new-record
    "#(struct:port-record rejection #f () () () no-derivation ∃ \"A0 derivations: 0\" 0)"))
  (transport
   (waiver
    (case "6f7179b2bc813a079360002fde1531d22f13075a")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason
     "B1 preserves the no-diagnostics judgment boundary for this newly eligible negative pure-position case."))
   (waiver
    (case "ca3ded71dd1e695cfba61b2e74339866dbf5b8a7")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason
     "B1 preserves the no-diagnostics judgment boundary for this newly eligible negative pure-position case."))
   (current-term
    (SetOf
     (λ ($z :: Entity)
       (Every
        (λ ($x :: Entity) (gerku $x))
        (λ ($x :: Entity) (Close (jmaji $x)))))))
   (old-record
    "#(struct:port-record rejection #f () () () typing-failure SetOf \"ca3ded71dd1e695cfba61b2e74339866dbf5b8a7:?:?: SetOf property must be a pure Fn under L0.1\" 0)")
   (new-record
    "#(struct:port-record rejection #f () () () no-derivation SetOf \"A0 derivations: 0\" 0)"))
  (transport
   (waiver
    (case "58c6ffc749c2646868481de082505374ffabf2df")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason
     "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
   (waiver
    (case "dca2591716f1bddade1e6b1d76605a84e2b5157f")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason
     "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
   (current-term
    (SetOf
     (λ ($x :: Entity)
       (Bind
        ($r :: Referents Entity)
        (Refer (λ ($y :: Entity) (gerku $y)))
        (gerku $x)))))
   (old-record
    "#(struct:port-record rejection #f () () () typing-failure SetOf \"dca2591716f1bddade1e6b1d76605a84e2b5157f:?:?: SetOf property must be a pure Fn under L0.1\" 0)")
   (new-record
    "#(struct:port-record rejection #f () () () no-derivation SetOf \"A0 derivations: 0\" 0)"))
  (transport
   (waiver
    (case "7482cccbaa630047b71bb8f648818fa1359ddf68")
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
   (current-term (SetOf (λ ($x :: Entity) (Context))))
   (old-record
    "#(struct:port-record rejection #f () () () typing-failure SetOf \"e2ac359a95a348da47b2f9e9763c8f8739435ea8:?:?: Context is a retrieval/reference computation; bind it with an expected type and do not place it directly in a pure position\" 0)")
   (new-record
    "#(struct:port-record rejection #f () () () no-derivation SetOf \"A0 derivations: 0\" 0)"))
  (transport
   (waiver
    (case "4cc6a45509151b5a0827ca4741f05c3e9e3afb8c")
    (fields effects)
    (finding "#81")
    (reason
     "DirectClause defaults now remain inside the event property, so Close reports the conservative effectful-call rather than the stale outer context effect."))
   (waiver
    (case "f7526f02968c2d0f940554bf7559692e5e9de6ea")
    (fields effects)
    (finding "#81")
    (reason
     "DirectClause defaults now remain inside the event property, so Close reports the conservative effectful-call rather than the stale outer context effect."))
   (current-term
    (Bind
     ($r :: Referents Entity)
     (Refer (λ ($unit :: Referents Entity) (gerku $unit)))
     (Close (tavla Speaker $r))))
   (old-record
    "#(struct:port-record success Content (context refer) () () #f #f #f 1)")
   (new-record
    "#(struct:port-record success Content (effectful-call refer) () () #f #f #f 1)"))
  (transport
   (waiver
    (case "84d3f3f5db6d9bb097e9df301673052e73e0649a")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason
     "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
   (waiver
    (case "fecc256bfaacdc51a22517ddaf899499179207f8")
    (fields failure-class)
    (finding "#52:issuecomment-5458132092")
    (reason
     "A0 keeps diagnostics outside its Redex judgment, so this rejected in-bank mutation has no Phase B failure classification yet."))
   (current-term
    (SetOf
     (λ ($x :: Entity)
       (Bind
        ($r :: Referents Entity)
        (SelectSome (λ ($y :: Entity) (gerku $y)))
        (gerku $x)))))
   (old-record
    "#(struct:port-record rejection #f () () () typing-failure SetOf \"fecc256bfaacdc51a22517ddaf899499179207f8:?:?: SetOf property must be a pure Fn under L0.1\" 0)")
   (new-record
    "#(struct:port-record rejection #f () () () no-derivation SetOf \"A0 derivations: 0\" 0)"))
  (transport
   (waiver
    (case "b1-lowering-c28906129a38b214")
    (fields effects)
    (finding "#81")
    (reason
     "The lowering-derived ClauseContent now preserves the latent EFn call from its corrected inner DirectClause defaults."))
   (waiver
    (case "b1-lowering-668ac22896455289")
    (fields effects)
    (finding "#81")
    (reason
     "The lowering-derived ClauseContent now preserves the latent EFn call from its corrected inner DirectClause defaults."))
   (current-term
    (CloseClause
     (ActualClause
      (StateClause
       (IndividualEvery
        (λ ($x :: Entity) (gerku $x))
        (λ ($x :: Entity)
          (CloseClause
           (ActualClause
            (λ ($event :: Referents Eventuality)
              (Bind
               ($ctx3 :: Referents Entity)
               (Context)
               (tavla :1 $x :2 $r :3 $ctx3 :Eventuality $event)))))))))))
   (old-record "#(struct:port-record success Content () () () #f #f #f 1)")
   (new-record
    "#(struct:port-record success Content (effectful-call) () () #f #f #f 1)"))
  (transport
   (waiver
    (case "b1-lowering-c28906129a38b214")
    (fields effects)
    (finding "#81")
    (reason
     "The lowering-derived ClauseContent now preserves the latent EFn call from its corrected inner DirectClause defaults."))
   (waiver
    (case "b1-lowering-9a4b45a97730a6c7")
    (fields effects)
    (finding "#81")
    (reason
     "The lowering-derived ClauseContent now preserves the latent EFn call from its corrected inner DirectClause defaults."))
   (current-term
    (CloseClause
     (ActualClause
      (StateClause
       (IndividualEvery
        (λ ($x :: Entity) (gerku $x))
        (λ ($x :: Entity)
          (IndividualSome
           (λ ($x :: Entity) (mlatu $x))
           (λ ($w :: Entity)
             (CloseClause
              (ActualClause
               (λ ($event :: Referents Eventuality)
                 (Bind
                  ($ctx3 :: Referents Entity)
                  (Context)
                  (tavla :1 $x :2 $w :3 $ctx3 :Eventuality $event)))))))))))))
   (old-record "#(struct:port-record success Content () () () #f #f #f 1)")
   (new-record
    "#(struct:port-record success Content (effectful-call) () () #f #f #f 1)")))
 (retired-stale
  (waiver
   (case "5f5b053a4dcccf2858daa126fd3d854e0e78d516")
   (fields effects)
   (finding "#13:issuecomment-5458243084")
   (reason
    "The A0 equation executes its effectful function at each paired step; the legacy pass-through omits that application effect."))
  (waiver
   (case "b1-lowering-58446186c6fa7dbc")
   (fields effects obligations)
   (finding "#13:issuecomment-5459255275")
   (reason
    "The lowering-derived Every subterm inherits MaxRefer projective import in B1."))
  (waiver
   (case "b1-lowering-7c491742d3d8fff2")
   (fields effects obligations)
   (finding "#13:issuecomment-5459255275")
   (reason
    "The lowering-derived Every subterm inherits MaxRefer projective import in B1."))
  (waiver
   (case "b1-lowering-4268934806d322ae")
   (fields effects obligations)
   (finding "#13:issuecomment-5459255275")
   (reason
    "The lowering-derived nested Every subterm inherits MaxRefer projective import in B1."))
  (waiver
   (case "c27acb49649a24ec94cecaf88567f2d8e9165026")
   (fields effects)
   (finding "#81")
   (reason
    "DirectClause defaults now remain inside the event property, so Close reports the conservative effectful-call rather than the stale outer context effect."))
  (waiver
   (case "b1-lowering-5490abdf57992a66")
   (fields effects)
   (finding "#81")
   (reason
    "The lowering-derived ClauseContent now preserves the latent EFn call from its corrected inner DirectClause defaults."))))
