import SmusniPilot.M2TypingBridge

namespace SmusniPilot
namespace M2

structure TypingManifestSupported (trace : List M2TypingRuleId) : Prop where
  supported : trace.all typingRuleImplemented = true

structure TypingResultsManifestSupported (results : List TypingResult) : Prop where
  traces : results.all (fun result => result.trace.all typingRuleImplemented) = true

@[simp] theorem except_error_bind_sound {error first second : Type}
    (failureValue : error) (next : first → Except error second) :
    ((Except.error failureValue : Except error first) >>= next) =
      .error failureValue := rfl

theorem typing_manifest_prefix {rules suffix : List M2TypingRuleId}
    (supported : (rules ++ suffix).all typingRuleImplemented = true) :
    rules.all typingRuleImplemented = true := by
  rw [List.all_eq_true] at supported ⊢
  intro rule member
  exact supported rule (List.mem_append_left suffix member)

theorem typing_manifest_prefix_witness {rules suffix : List M2TypingRuleId}
    (supported : TypingManifestSupported (rules ++ suffix)) :
    TypingManifestSupported rules :=
  ⟨typing_manifest_prefix supported.supported⟩

theorem typing_manifest_middle_prefix
    {initial kept dropped : List M2TypingRuleId}
    (supported : TypingManifestSupported (initial ++ (kept ++ dropped))) :
    TypingManifestSupported (initial ++ kept) := by
  apply typing_manifest_prefix_witness (suffix := dropped)
  simpa [List.append_assoc] using supported

theorem typing_manifest_drop_one {rules : List M2TypingRuleId}
    {last : M2TypingRuleId}
    (supported : TypingManifestSupported (rules ++ [last])) :
    TypingManifestSupported rules :=
  typing_manifest_prefix_witness supported

theorem typing_manifest_drop_two {rules : List M2TypingRuleId}
    {penultimate last : M2TypingRuleId}
    (supported : TypingManifestSupported (rules ++ [penultimate, last])) :
    TypingManifestSupported rules :=
  typing_manifest_prefix_witness supported

theorem typing_manifest_keep_first_two {rules : List M2TypingRuleId}
    {first second third fourth : M2TypingRuleId}
    (supported : TypingManifestSupported
      (rules ++ [first, second, third, fourth])) :
    TypingManifestSupported (rules ++ [first, second]) := by
  apply typing_manifest_middle_prefix (dropped := [third, fourth])
  simpa using supported

theorem typing_results_manifest_of_flattened
    {results : List TypingResult} {suffix : List M2TypingRuleId}
    (supported : TypingManifestSupported
      (results.flatMap (fun result => result.trace) ++ suffix)) :
    TypingResultsManifestSupported results := by
  constructor
  rw [List.all_eq_true]
  intro result member
  rw [List.all_eq_true]
  intro rule ruleMember
  have flattenedMember : rule ∈ results.flatMap (fun item => item.trace) := by
    rw [List.mem_flatMap]
    exact ⟨result, member, ruleMember⟩
  have flatSupported := typing_manifest_prefix supported.supported
  rw [List.all_eq_true] at flatSupported
  exact flatSupported rule flattenedMember

theorem typing_manifest_sublist {whole part : List M2TypingRuleId}
    (supported : TypingManifestSupported whole)
    (included : ∀ rule, rule ∈ part → rule ∈ whole) :
    TypingManifestSupported part := by
  constructor
  have wholeSupported := supported.supported
  rw [List.all_eq_true] at wholeSupported ⊢
  intro rule member
  exact wholeSupported rule (included rule member)

theorem typing_manifest_excludes {rules : List M2TypingRuleId}
    {rule : M2TypingRuleId}
    (supported : TypingManifestSupported rules)
    (member : rule ∈ rules)
    (excluded : typingRuleImplemented rule = false) : False := by
  have allSupported := supported.supported
  rw [List.all_eq_true] at allSupported
  have implemented := allSupported rule member
  rw [excluded] at implemented
  contradiction

theorem typing_results_manifest_cons {head : TypingResult}
    {tail : List TypingResult}
    (supported : TypingResultsManifestSupported (head :: tail)) :
    TypingManifestSupported head.trace ∧
      TypingResultsManifestSupported tail := by
  rcases supported with ⟨supported⟩
  simp only [List.all_cons, Bool.and_eq_true] at supported
  exact ⟨⟨supported.1⟩, ⟨supported.2⟩⟩

theorem asUnary_eq_some {type : Ty} {name : TypeName} {inner : Ty}
    (found : Ty.asUnary type name = some inner) :
    type = .named name [inner] := by
  cases type with
  | named actual arguments =>
      cases arguments with
      | nil => simp [Ty.asUnary] at found
      | cons head tail =>
          cases tail with
          | nil =>
              simp [Ty.asUnary] at found
              rcases found with ⟨rfl, rfl⟩
              rfl
          | cons second rest => simp [Ty.asUnary] at found
  | «variable» _ | index _ | function _ _ _ => simp [Ty.asUnary] at found

theorem typeName_eq_of_beq_true {first second : TypeName}
    (equal : (first == second) = true) : first = second := by
  cases first <;> cases second <;>
    first | rfl | (change false = true at equal; contradiction)

theorem asBinary_eq_some {type : Ty} {name : TypeName} {first second : Ty}
    (found : Ty.asBinary type name = some (first, second)) :
    type = .named name [first, second] := by
  cases type with
  | named actual arguments =>
      cases arguments with
      | nil => simp [Ty.asBinary] at found
      | cons head tail =>
          cases tail with
          | nil => simp [Ty.asBinary] at found
          | cons next rest =>
              cases rest with
              | cons third more => simp [Ty.asBinary] at found
              | nil =>
                  simp [Ty.asBinary] at found
                  rcases found with ⟨nameBeq, headEq, nextEq⟩
                  have nameEq : actual = name := typeName_eq_of_beq_true nameBeq
                  cases nameEq
                  cases headEq
                  cases nextEq
                  rfl
  | «variable» _ | index _ | function _ _ _ => simp [Ty.asBinary] at found

theorem compatible_self_sound (type : Ty) : Ty.compatible type type = true := by
  unfold Ty.compatible
  have self : (type == type) = true := by
    change Ty.beq type type = true
    exact Ty.beq_self type
  rw [self]
  rfl

theorem oneArgumentFunction_sound {result : TypingResult}
    {effectful : Bool} {inner : Ty}
    (found : oneArgumentFunction result = some (effectful, inner)) :
    result.type = Ty.function effectful [inner] Ty.content := by
  cases typeEq : result.type with
  | named name arguments => simp [oneArgumentFunction, typeEq] at found
  | «variable» name => simp [oneArgumentFunction, typeEq] at found
  | index value => simp [oneArgumentFunction, typeEq] at found
  | function actualEffectful parameters output =>
      cases parameters with
      | nil => simp [oneArgumentFunction, typeEq] at found
      | cons parameter tail =>
          cases tail with
          | cons second rest => simp [oneArgumentFunction, typeEq] at found
          | nil =>
              cases outputEq : output == Ty.content with
              | false =>
                  simp [oneArgumentFunction, typeEq, outputEq] at found
              | true =>
                  simp [oneArgumentFunction, typeEq, outputEq] at found
                  rcases found with ⟨rfl, rfl⟩
                  have outputType : output = Ty.content :=
                    Ty.eq_of_beq_true outputEq
                  subst output
                  rfl

theorem expected_context_refComp {scope : Nat} (site : SiteId)
    (arguments : TermList scope) (expected : Ty)
    (selected : expectedCheckClause (.context site arguments) expected =
      some .context) :
    ∃ inner, expected = Ty.refComp inner := by
  cases found : Ty.asUnary expected .typeFormRefComp with
  | none => simp [expectedCheckClause, found] at selected
  | some inner =>
      exact ⟨inner, by
        simpa [Ty.refComp] using asUnary_eq_some found⟩

theorem expected_context_term_shape {scope : Nat} (term : Term scope)
    (expected : Ty)
    (selected : expectedCheckClause term expected = some .context) :
    ∃ site arguments, term = .context site arguments := by
  cases term <;> simp [expectedCheckClause] at selected ⊢
  all_goals
    cases found : Ty.asUnary expected .typeFormRefComp <;>
      simp [expectedCheckClause, found] at selected
  all_goals
    cases ‹FirstOrderPrimitive› <;>
      try simp [expectedCheckClause, found] at selected
  all_goals
    cases expected <;> try simp [expectedCheckClause, found] at selected
  all_goals
    cases ‹List Ty› with
    | nil => simp [expectedCheckClause] at selected
    | cons head tail =>
        cases tail with
        | nil =>
            cases ‹TypeName› <;> simp [expectedCheckClause] at selected
        | cons second rest => simp [expectedCheckClause] at selected

theorem expected_context_shape_contradiction {scope : Nat}
    (term : Term scope) (expected : Ty)
    (selected : expectedCheckClause term expected = some .context)
    (notContext : ∀ site arguments, term ≠ .context site arguments) : False := by
  rcases expected_context_term_shape term expected selected with
    ⟨site, arguments, shape⟩
  exact notContext site arguments shape

theorem expected_vague_term_shape {scope : Nat} (term : Term scope)
    (expected : Ty)
    (selected : expectedCheckClause term expected = some .vague) :
    ∃ site constraint inner,
      term = .vague site constraint ∧
        Ty.asUnary expected .typeFormRefComp = some inner := by
  cases term <;> simp [expectedCheckClause] at selected ⊢
  all_goals
    cases found : Ty.asUnary expected .typeFormRefComp <;>
      simp [expectedCheckClause, found] at selected ⊢
  all_goals
    cases ‹FirstOrderPrimitive› <;>
      try simp [expectedCheckClause, found] at selected
  all_goals
    cases expected <;> try simp [expectedCheckClause, found] at selected
  all_goals
    cases ‹List Ty› with
    | nil => simp [expectedCheckClause] at selected
    | cons head tail =>
        cases tail with
        | nil =>
            cases ‹TypeName› <;> simp [expectedCheckClause] at selected
        | cons second rest => simp [expectedCheckClause] at selected

theorem expected_vague_shape_contradiction {scope : Nat}
    (term : Term scope) (expected : Ty)
    (selected : expectedCheckClause term expected = some .vague)
    (notVague : ∀ site constraint inner,
      term = .vague site constraint →
        Ty.asUnary expected .typeFormRefComp ≠ some inner) : False := by
  rcases expected_vague_term_shape term expected selected with
    ⟨site, constraint, inner, shape, expectedShape⟩
  exact notVague site constraint inner shape expectedShape

theorem expected_local_refComp {scope : Nat} (arguments : TermList scope)
    (expected : Ty)
    (selected : expectedCheckClause (.primitive .local arguments) expected =
      some .local) :
    ∃ inner, expected = Ty.refComp inner := by
  cases found : Ty.asUnary expected .typeFormRefComp with
  | none => simp [expectedCheckClause, found] at selected
  | some inner =>
      exact ⟨inner, by simpa [Ty.refComp] using asUnary_eq_some found⟩

theorem expected_refer_term_shape {scope : Nat} (term : Term scope)
    (expected : Ty)
    (selected : expectedCheckClause term expected = some .refer) :
    ∃ arguments reference,
      term = .primitive .refer arguments ∧
        Ty.asUnary expected .typeFormRefComp = some reference := by
  cases term <;> simp [expectedCheckClause] at selected ⊢
  all_goals
    cases found : Ty.asUnary expected .typeFormRefComp <;>
      simp [expectedCheckClause, found] at selected ⊢
  all_goals
    cases ‹FirstOrderPrimitive› <;>
      try simp [expectedCheckClause, found] at selected ⊢
  all_goals
    cases expected <;> try simp [expectedCheckClause, found] at selected
  all_goals
    cases ‹List Ty› with
    | nil => simp [expectedCheckClause] at selected
    | cons head tail =>
        cases tail with
        | nil => cases ‹TypeName› <;> simp [expectedCheckClause] at selected
        | cons second rest => simp [expectedCheckClause] at selected

theorem expected_presuppose_term_shape {scope : Nat} (term : Term scope)
    (expected : Ty)
    (selected : expectedCheckClause term expected = some .presupposeReference) :
    ∃ arguments, term = .primitive .presuppose arguments := by
  cases term <;> simp [expectedCheckClause] at selected ⊢
  all_goals
    cases found : Ty.asUnary expected .typeFormRefComp <;>
      simp [expectedCheckClause, found] at selected ⊢
  all_goals
    cases ‹FirstOrderPrimitive› <;>
      try simp [expectedCheckClause, found] at selected ⊢
  all_goals
    cases expected <;> try simp [expectedCheckClause, found] at selected
  all_goals
    cases ‹List Ty› with
    | nil => simp [expectedCheckClause] at selected
    | cons head tail =>
        cases tail with
        | nil => cases ‹TypeName› <;> simp [expectedCheckClause] at selected
        | cons second rest => simp [expectedCheckClause] at selected

theorem expected_local_term_shape {scope : Nat} (term : Term scope)
    (expected : Ty)
    (selected : expectedCheckClause term expected = some .local) :
    ∃ arguments, term = .primitive .local arguments := by
  cases term <;> simp [expectedCheckClause] at selected ⊢
  all_goals
    cases found : Ty.asUnary expected .typeFormRefComp <;>
      simp [expectedCheckClause, found] at selected ⊢
  all_goals
    cases ‹FirstOrderPrimitive› <;>
      try simp [expectedCheckClause, found] at selected ⊢
  all_goals
    cases expected <;> try simp [expectedCheckClause, found] at selected
  all_goals
    cases ‹List Ty› with
    | nil => simp [expectedCheckClause] at selected
    | cons head tail =>
        cases tail with
        | nil => cases ‹TypeName› <;> simp [expectedCheckClause] at selected
        | cons second rest => simp [expectedCheckClause] at selected

theorem expected_reference_primitive_shape {scope : Nat} (term : Term scope)
    (expected : Ty)
    (selected : expectedCheckClause term expected = some .referencePrimitive) :
    ∃ operator arguments reference,
      term = .primitive operator arguments ∧
        Ty.asUnary expected .typeFormRefComp = some reference := by
  cases term <;> simp [expectedCheckClause] at selected ⊢
  all_goals
    cases found : Ty.asUnary expected .typeFormRefComp <;>
      simp [expectedCheckClause, found] at selected ⊢
  all_goals
    cases ‹FirstOrderPrimitive› <;>
      try simp [expectedCheckClause, found] at selected ⊢
  all_goals
    cases expected <;> try simp [expectedCheckClause, found] at selected
  all_goals
    cases ‹List Ty› with
    | nil => simp [expectedCheckClause] at selected
    | cons head tail =>
        cases tail with
        | nil => cases ‹TypeName› <;> simp [expectedCheckClause] at selected
        | cons second rest => simp [expectedCheckClause] at selected

theorem expected_list_shape {scope : Nat} (term : Term scope)
    (expected : Ty)
    (selected : expectedCheckClause term expected = some .list) :
    ∃ arguments itemType,
      term = .primitive .list arguments ∧
        expected = Ty.list itemType := by
  cases term <;> simp [expectedCheckClause] at selected ⊢
  all_goals
    cases found : Ty.asUnary expected .typeFormRefComp <;>
      simp [expectedCheckClause, found] at selected ⊢
  all_goals
    cases ‹FirstOrderPrimitive› <;>
      try simp [expectedCheckClause, found] at selected ⊢
  all_goals
    cases expected <;> try simp [expectedCheckClause, found, Ty.list] at selected ⊢
  all_goals
    cases ‹List Ty› with
    | nil => simp [expectedCheckClause, Ty.list] at selected
    | cons head tail =>
        cases tail with
        | nil =>
            cases ‹TypeName› <;> simp [expectedCheckClause, Ty.list] at selected ⊢
        | cons second rest => simp [expectedCheckClause, Ty.list] at selected

private def SignSoundMotive (scope : Nat) (environment : Environment scope)
    (operator : FirstOrderPrimitive) (arguments : TermList scope) (kind : String) : Prop :=
  ((operator = .opaqueQuote ∧ kind = "Opaque") ∨
    (operator = .wordSign ∧ kind = "Word") ∨
    (operator = .nameSign ∧ kind = "Name") ∨
    (operator = .letteralSign ∧ kind = "Letteral")) →
  ∀ result, synthPrimitive.signConstructor environment operator arguments kind = .ok result →
    TypingManifestSupported result.trace →
    PrimitiveJudgment environment operator arguments result.observation

private def CheckSoundMotive (scope : Nat) (environment : Environment scope)
    (term : Term scope) (expected : Ty) : Prop :=
  ∀ result, check environment term expected = .ok result →
    TypingManifestSupported result.trace →
    CheckJudgment environment term expected result.observation

private def CheckExpectedSoundMotive (scope : Nat) (environment : Environment scope)
    (term : Term scope) (expected : Ty) (synthError : TypingError) : Prop :=
  ∀ result, checkExpected environment term expected synthError = .ok result →
    TypingManifestSupported result.trace →
    CheckJudgment environment term expected result.observation

private def CheckArgumentsSoundMotive (scope : Nat) (environment : Environment scope)
    (arguments : TermList scope) (expected : Ty) : Prop :=
  ∀ results, checkPositionalList environment arguments expected = .ok results →
    TypingResultsManifestSupported results →
    CheckArgumentsJudgment environment arguments expected
      (results.map TypingResult.observation)

private def CheckReferenceSoundMotive (scope : Nat) (environment : Environment scope)
    (operator : FirstOrderPrimitive) (arguments : TermList scope)
    (reference expected : Ty) : Prop :=
  Ty.asUnary expected .typeFormRefComp = some reference →
  ∀ result, checkReferencePrimitive environment operator arguments reference expected = .ok result →
    TypingManifestSupported result.trace →
    CheckJudgment environment (.primitive operator arguments) expected result.observation

private def CheckPresupposeSoundMotive (scope : Nat)
    (environment : Environment scope) (arguments : TermList scope) (expected : Ty) : Prop :=
  ∀ inner, Ty.asUnary expected .typeFormRefComp = some inner →
  ∀ result, checkPresupposeReference environment arguments expected = .ok result →
    TypingManifestSupported result.trace →
    CheckJudgment environment (.primitive .presuppose arguments) expected result.observation

private def SynthSoundMotive (scope : Nat) (environment : Environment scope)
    (term : Term scope) : Prop :=
  ∀ result, synth environment term = .ok result →
    TypingManifestSupported result.trace →
    SynthJudgment environment term result.observation

private def PrimitiveSoundMotive (scope : Nat) (environment : Environment scope)
    (operator : FirstOrderPrimitive) (arguments : TermList scope) : Prop :=
  ∀ result, synthPrimitive environment operator arguments = .ok result →
    TypingManifestSupported result.trace →
    PrimitiveJudgment environment operator arguments result.observation

private def PerformSoundMotive (scope : Nat) (environment : Environment scope)
    (arguments : TermList scope) : Prop :=
  ∀ result, synthPerform environment arguments = .ok result →
    TypingManifestSupported result.trace →
    PrimitiveJudgment environment .perform arguments result.observation

private def ThresholdSoundMotive (scope : Nat) (environment : Environment scope)
    (arguments : TermList scope) : Prop :=
  ∀ result, synthAdmissibleThreshold environment arguments = .ok result →
    TypingManifestSupported result.trace →
    PrimitiveJudgment environment .admissibleThreshold arguments result.observation

private def PresupposeSoundMotive (scope : Nat) (environment : Environment scope)
    (arguments : TermList scope) : Prop :=
  ∀ result, synthPresuppose environment arguments = .ok result →
    TypingManifestSupported result.trace →
    PrimitiveJudgment environment .presuppose arguments result.observation

private def ReferenceBinarySoundMotive (scope : Nat)
    (environment : Environment scope) (operator : FirstOrderPrimitive)
    (arguments : TermList scope) (rule : M2TypingRuleId) : Prop :=
  (operator = .among ∧ rule = .b1TAmong) →
  ∀ result, synthPrimitive.referenceBinary environment operator arguments rule = .ok result →
    TypingManifestSupported result.trace →
    PrimitiveJudgment environment operator arguments result.observation

private def QuantifySoundMotive (scope : Nat) (environment : Environment scope)
    (operator : FirstOrderPrimitive) (arguments : TermList scope)
    (rule : M2TypingRuleId) : Prop :=
  (operator = .forall ∨ operator = .exists) →
  ∀ result, synthPrimitive.quantify environment operator arguments rule = .ok result →
    TypingManifestSupported result.trace →
    PrimitiveJudgment environment operator arguments result.observation

private def UnaryCheckSoundMotive (scope : Nat) (environment : Environment scope)
    (operator : FirstOrderPrimitive) (arguments : TermList scope)
    (rule : M2TypingRuleId) (expected resultType : Ty) : Prop :=
  UnaryCheckedPrimitiveRule operator expected resultType → ∀ result,
    synthPrimitive.unaryCheck environment operator arguments rule expected resultType = .ok result →
    TypingManifestSupported result.trace →
    PrimitiveJudgment environment operator arguments result.observation

private def BinaryCheckSoundMotive (scope : Nat) (environment : Environment scope)
    (operator : FirstOrderPrimitive) (arguments : TermList scope)
    (rule : M2TypingRuleId) (expected resultType : Ty) : Prop :=
  BinaryCheckedPrimitiveRule operator expected resultType → ∀ result,
    synthPrimitive.binaryCheck environment operator arguments rule expected resultType = .ok result →
    TypingManifestSupported result.trace →
    PrimitiveJudgment environment operator arguments result.observation

private def BinarySynthSoundMotive (scope : Nat) (environment : Environment scope)
    (operator : FirstOrderPrimitive) (arguments : TermList scope)
    (rule : M2TypingRuleId)
    (resultType : TypingResult → TypingResult → Except TypingError Ty) : Prop :=
  (∀ first second output,
    resultType first second = .ok output →
      BinaryPrimitiveRule operator first.observation second.observation output) →
  ∀ result,
    synthPrimitive.binarySynth environment operator arguments rule resultType = .ok result →
    TypingManifestSupported result.trace →
    PrimitiveJudgment environment operator arguments result.observation

private def JaiRoleSoundMotive (scope : Nat) (environment : Environment scope)
    (arguments : TermList scope) : Prop :=
  ∀ result, synthJaiRoleAdmissible environment arguments = .ok result →
    TypingManifestSupported result.trace →
    PrimitiveJudgment environment .jaiRoleAdmissible arguments result.observation

private def PeerUnitSoundMotive (scope : Nat) (environment : Environment scope)
    (arguments : TermList scope) : Prop :=
  ∀ result, synthPeerUnitAt environment arguments = .ok result →
    TypingManifestSupported result.trace →
    PrimitiveJudgment environment .peerUnitAt arguments result.observation

private def BasisUnitSoundMotive (scope : Nat) (environment : Environment scope)
    (arguments : TermList scope) : Prop :=
  ∀ result, synthBasisUnitAt environment arguments = .ok result →
    TypingManifestSupported result.trace →
    PrimitiveJudgment environment .basisUnitAt arguments result.observation

private def AggregateSoundMotive (scope : Nat) (environment : Environment scope)
    (arguments : TermList scope) : Prop :=
  ∀ result, synthAggregate environment arguments = .ok result →
    TypingManifestSupported result.trace →
    PrimitiveJudgment environment .aggregate arguments result.observation

private def ContentInterfaceSoundMotive (scope : Nat)
    (environment : Environment scope) (operator : FirstOrderPrimitive)
    (arguments : TermList scope) (arity : Option Nat) : Prop :=
  ((operator = .named ∧ arity = some 2) ∨
    ((operator = .happiness ∨ operator = .unhappiness ∨
      operator = .desire ∨ operator = .evidentialBasis ∨
      operator = .contrast ∨ operator = .metalinguisticallyDefective ∨
      operator = .realizes ∨ operator = .speakerOf) ∧ arity = none)) →
  ∀ result, synthPrimitive.contentInterface environment operator arguments arity = .ok result →
    TypingManifestSupported result.trace →
    PrimitiveJudgment environment operator arguments result.observation

theorem constant_rule_manifest {operator : FirstOrderPrimitive}
    {observation : TypingObservation}
    (rule : ConstantPrimitiveRule operator observation) :
    m2CoreConstantRecords.any
      (fun record => record.name == rawTermName operator.name) = true := by
  cases rule <;> decide

private def SynthArgumentsSoundMotive (scope : Nat)
    (environment : Environment scope) (arguments : TermList scope) : Prop :=
  ∀ results, synthPositionalList environment arguments = .ok results →
    TypingResultsManifestSupported results →
    SynthArgumentsJudgment environment arguments
      (results.map TypingResult.observation)

private def LexicalSoundMotive (scope : Nat) (environment : Environment scope)
    (head : String) (arguments : TermList scope) : Prop :=
  ∀ result, synthLexical environment head arguments = .ok result →
    TypingManifestSupported result.trace →
    SynthJudgment environment (.lexical head arguments) result.observation

private def LexicalArgumentsSoundMotive (scope : Nat)
    (environment : Environment scope) (row : M2LexicalRowRecord)
    (arguments : TermList scope) (seen : List String) : Prop :=
  ∀ results ordinary eventFilled,
    lexicalArgumentResults environment row arguments seen =
      .ok (results, ordinary, eventFilled) →
    TypingResultsManifestSupported results →
    LexicalArgumentsJudgment environment row arguments seen
        (results.map TypingResult.observation) ordinary eventFilled ∧
      ordinary ≤ row.ordinaryArity ∧
      (":Eventuality" ∈ seen → eventFilled = false)

private def ApplySoundMotive (scope : Nat) (environment : Environment scope)
    (functionResult : TypingResult) (arguments : TermList scope) : Prop :=
  ∀ result, applyFunction environment functionResult arguments = .ok result →
    TypingManifestSupported result.trace →
    TypingManifestSupported functionResult.trace ∧
      ApplyJudgment environment functionResult.observation arguments result.observation

private def PredArgumentsSoundMotive (scope : Nat)
    (environment : Environment scope) (arguments : TermList scope) : Prop :=
  ∀ results ordinary eventFilled,
    predTermArgumentResults environment arguments = .ok (results, ordinary, eventFilled) →
    TypingResultsManifestSupported results →
    PredArgumentsJudgment environment arguments
      (results.map TypingResult.observation) ordinary eventFilled

private def ValueArgumentsSoundMotive (scope : Nat)
    (environment : Environment scope) (arguments : TermList scope) : Prop :=
  ∀ results, synthValueOperands environment arguments = .ok results →
    TypingResultsManifestSupported results →
    ValueArgumentsJudgment environment arguments
      (results.map TypingResult.observation)

private theorem check_from_synth_manifest {scope : Nat}
    (environment : Environment scope) (term : Term scope) (expected : Ty)
    (actual : TypingResult)
    (compatible : Ty.compatible actual.type expected = true)
    (synthSound : TypingManifestSupported actual.trace →
      SynthJudgment environment term actual.observation)
    (supported : TypingManifestSupported
      (actual.trace ++ [.a0TCheckSynth, .a0Check])) :
    CheckJudgment environment term expected actual.observation :=
  .fromSynth environment term expected actual.observation
    (synthSound (typing_manifest_drop_two supported)) compatible

private theorem check_success_handler {scope : Nat}
    (environment : Environment scope) (term : Term scope) (expected : Ty)
    (actual : TypingResult)
    (synthSuccess : synth environment term = .ok actual)
    (compatible : Ty.compatible actual.type expected = true)
    (synthSound : SynthSoundMotive scope environment term) :
    CheckSoundMotive scope environment term expected := by
  intro result checkSuccess supported
  rw [check.eq_1, synthSuccess] at checkSuccess
  simp [compatible] at checkSuccess
  cases checkSuccess
  exact check_from_synth_manifest environment term expected actual compatible
    (fun manifest => synthSound actual synthSuccess manifest) supported

private theorem context_check_handler {scope : Nat}
    (environment : Environment scope) (expected : Ty)
    (synthError : TypingError) (site : SiteId) (arguments : TermList scope)
    (selected : expectedCheckClause (.context site arguments) expected =
      some .context)
    (argumentsSound : ValueArgumentsSoundMotive scope environment arguments) :
    CheckExpectedSoundMotive scope environment (.context site arguments)
      expected synthError := by
  rcases expected_context_refComp site arguments expected selected with
    ⟨inner, rfl⟩
  intro result success supported
  cases resultsEq : synthValueOperands environment arguments with
  | error error =>
      simp [checkExpected, expectedCheckClause_context, resultsEq] at success
  | ok results =>
      have resultEq : result =
          (mergeResults (Ty.refComp inner) results [.context] [] .a0TContext).withRule
            .a0Check := by
        simpa [checkExpected, expectedCheckClause_context, resultsEq] using
          success.symm
      subst result
      have resultsSupported : TypingResultsManifestSupported results := by
        apply typing_results_manifest_of_flattened (suffix := [.a0TContext, .a0Check])
        simpa [mergeResults, TypingResult.withRule] using supported
      simpa only [observation_withRule, observation_mergeResults] using
        CheckJudgment.context environment site arguments inner
          (results.map TypingResult.observation)
          (argumentsSound results resultsEq resultsSupported)

private theorem context_impossible_handler {scope : Nat}
    (environment : Environment scope) (term : Term scope) (expected : Ty)
    (synthError : TypingError)
    (selected : expectedCheckClause term expected = some .context)
    (notContext : ∀ site arguments, term ≠ .context site arguments) :
    CheckExpectedSoundMotive scope environment term expected synthError :=
  (expected_context_shape_contradiction term expected selected notContext).elim

private theorem vague_check_handler {scope : Nat}
    (environment : Environment scope) (expected : Ty)
    (synthError : TypingError) (site : SiteId) (constraint : Term scope)
    (inner : Ty) (expectedShape : Ty.asUnary expected .typeFormRefComp = some inner)
    (_selected : expectedCheckClause (.vague site constraint) expected = some .vague)
    (constraintSound : SynthSoundMotive scope environment constraint) :
    CheckExpectedSoundMotive scope environment (.vague site constraint)
      expected synthError := by
  have expectedEq : expected = Ty.refComp inner := by
    simpa [Ty.refComp] using asUnary_eq_some expectedShape
  subst expected
  intro result success supported
  cases constraintEq : synth environment constraint with
  | error error =>
      simp [checkExpected, expectedCheckClause_vague, constraintEq] at success
  | ok property =>
      cases typeEq : property.type == Ty.pureFn [inner] Ty.content with
      | false =>
          simp [checkExpected, expectedCheckClause_vague, constraintEq, typeEq] at success
          simp [failure, except_error_bind_sound] at success
      | true =>
          cases pureEq : isPure property with
          | false =>
              simp [checkExpected, expectedCheckClause_vague, constraintEq,
                typeEq, pureEq] at success
              simp [failure, except_error_bind_sound] at success
          | true =>
              have resultEq : result =
                  (mergeResults (Ty.refComp inner) [property] [.context] []
                    .a0TVague).withRule .a0Check := by
                simpa [checkExpected, expectedCheckClause_vague, constraintEq,
                  typeEq, pureEq] using success.symm
              subst result
              have propertySupported : TypingManifestSupported property.trace := by
                apply typing_manifest_drop_two
                simpa [mergeResults, TypingResult.withRule] using supported
              have propertyTyping := constraintSound property constraintEq
                propertySupported
              have propertyType : property.type = Ty.pureFn [inner] Ty.content :=
                Ty.eq_of_beq_true typeEq
              have pure : property.effects = [] :=
                (purity_classifier_sound_complete property).mp pureEq
              simpa only [observation_withRule, observation_mergeResults,
                List.map] using
                CheckJudgment.vague environment site constraint inner
                  property.observation propertyTyping propertyType pure

private theorem vague_impossible_handler {scope : Nat}
    (environment : Environment scope) (term : Term scope) (expected : Ty)
    (synthError : TypingError)
    (selected : expectedCheckClause term expected = some .vague)
    (notVague : ∀ site constraint inner,
      term = .vague site constraint →
        Ty.asUnary expected .typeFormRefComp ≠ some inner) :
    CheckExpectedSoundMotive scope environment term expected synthError :=
  (expected_vague_shape_contradiction term expected selected notVague).elim

private theorem local_check_handler {scope : Nat}
    (environment : Environment scope) (expected : Ty)
    (synthError : TypingError) (body : Term scope)
    (selected : expectedCheckClause
      (.primitive .local (.positional body .nil)) expected = some .local)
    (bodySound : CheckSoundMotive scope environment body expected) :
    CheckExpectedSoundMotive scope environment
      (.primitive .local (.positional body .nil)) expected synthError := by
  rcases expected_local_refComp (.positional body .nil) expected selected with
    ⟨inner, rfl⟩
  intro result success supported
  cases bodyEq : check environment body (Ty.refComp inner) with
  | error error =>
      simp [checkExpected, expectedCheckClause_local, bodyEq] at success
  | ok bodyResult =>
      have resultEq : result =
          (mergeResults (Ty.refComp inner) [bodyResult] [] [] .m2TLocal).withRule
            .a0Check := by
        simpa [checkExpected, expectedCheckClause_local, bodyEq] using success.symm
      subst result
      have bodySupported : TypingManifestSupported bodyResult.trace := by
        apply typing_manifest_drop_two
        simpa [mergeResults, TypingResult.withRule] using supported
      simpa only [observation_withRule, observation_mergeResults, List.map,
        judgmentTermList] using
        CheckJudgment.local environment body inner bodyResult.observation
          (bodySound bodyResult bodyEq bodySupported)

private theorem refer_check_handler {scope : Nat}
    (environment : Environment scope) (expected : Ty)
    (synthError : TypingError) (reference : Ty)
    (expectedShape : Ty.asUnary expected .typeFormRefComp = some reference)
    (inner : Ty)
    (referenceShape : Ty.asUnary reference .typeFormReferents = some inner)
    (property : Term scope)
    (_selected : expectedCheckClause
      (.primitive .refer (.positional property .nil)) expected = some .refer)
    (propertySound : SynthSoundMotive scope environment property) :
    CheckExpectedSoundMotive scope environment
      (.primitive .refer (.positional property .nil)) expected synthError := by
  have expectedEq : expected = Ty.refComp (Ty.referents inner) := by
    have outer : expected = Ty.refComp reference := by
      simpa [Ty.refComp] using asUnary_eq_some expectedShape
    have referenceEq : reference = Ty.referents inner := by
      simpa [Ty.referents] using asUnary_eq_some referenceShape
    simpa [referenceEq] using outer
  subst expected
  intro result success supported
  cases propertyEq : synth environment property with
  | error error =>
      simp [checkExpected, expectedCheckClause_refer, propertyEq] at success
  | ok propertyResult =>
      cases propertyTypeEq : propertyResult.type with
      | named name arguments =>
          simp [checkExpected, expectedCheckClause_refer, propertyEq,
            propertyTypeEq] at success
          simp [failure, except_error_bind_sound] at success
      | «variable» name =>
          simp [checkExpected, expectedCheckClause_refer, propertyEq,
            propertyTypeEq] at success
          simp [failure, except_error_bind_sound] at success
      | index value =>
          simp [checkExpected, expectedCheckClause_refer, propertyEq,
            propertyTypeEq] at success
          simp [failure, except_error_bind_sound] at success
      | function effectful parameters output =>
          cases parameters with
          | nil =>
              simp [checkExpected, expectedCheckClause_refer, propertyEq,
                propertyTypeEq] at success
              simp [failure, except_error_bind_sound] at success
          | cons parameter tail =>
              cases tail with
              | cons second rest =>
                  simp [checkExpected, expectedCheckClause_refer, propertyEq,
                    propertyTypeEq] at success
                  simp [failure, except_error_bind_sound] at success
              | nil =>
                  cases outputEq : output == Ty.content with
                  | false =>
                      simp [checkExpected, expectedCheckClause_refer, propertyEq,
                        propertyTypeEq, outputEq] at success
                      simp [failure, except_error_bind_sound] at success
                  | true =>
                      have outputType : output = Ty.content :=
                        Ty.eq_of_beq_true outputEq
                      subst output
                      cases referenceDomainEq :
                          parameter == Ty.referents inner with
                      | true =>
                          have parameterType : parameter = Ty.referents inner :=
                            Ty.eq_of_beq_true referenceDomainEq
                          subst parameter
                          have resultEq : result =
                              (mergeResults (Ty.refComp (Ty.referents inner))
                                [propertyResult]
                                ((if effectful then [.effectfulCall] else []) ++
                                  [.refer]) [] .a0TReferReference).withRule
                                .a0Check := by
                            simpa [checkExpected, expectedCheckClause_refer,
                              propertyEq, propertyTypeEq, outputEq,
                              referenceDomainEq] using success.symm
                          subst result
                          have propertySupported :
                              TypingManifestSupported propertyResult.trace := by
                            apply typing_manifest_drop_two
                            simpa [mergeResults, TypingResult.withRule] using supported
                          have propertyTyping := propertySound propertyResult
                            propertyEq propertySupported
                          have propertyType :
                              propertyResult.type =
                                Ty.effectfulFn [Ty.referents inner] Ty.content ∨
                              propertyResult.type =
                                Ty.pureFn [Ty.referents inner] Ty.content := by
                            cases effectful <;> simp [propertyTypeEq,
                              Ty.effectfulFn, Ty.pureFn]
                          have effectFlag :
                              (propertyResult.observation.type ==
                                Ty.effectfulFn [Ty.referents inner] Ty.content) =
                                effectful := by
                            change (propertyResult.type ==
                              Ty.effectfulFn [Ty.referents inner] Ty.content) =
                                effectful
                            rw [propertyTypeEq]
                            cases effectful with
                            | false => rfl
                            | true =>
                                change Ty.beq
                                  (Ty.function true [Ty.referents inner] Ty.content)
                                  (Ty.function true [Ty.referents inner] Ty.content) =
                                    true
                                exact Ty.beq_self _
                          simpa only [observation_withRule,
                            observation_mergeResults, List.map,
                            judgmentTermList, effectFlag] using
                            CheckJudgment.referReference environment property inner
                              propertyResult.observation propertyTyping propertyType
                      | false =>
                          cases memberEq : (!effectful && parameter == inner &&
                              propertyResult.effects.isEmpty) with
                          | false =>
                              have notMember : ¬((effectful = false ∧
                                  (parameter == inner) = true) ∧
                                  propertyResult.effects = []) := by
                                intro member
                                have memberTrue : (!effectful && parameter == inner &&
                                    propertyResult.effects.isEmpty) = true := by
                                  rcases member with ⟨⟨rfl, parameterMember⟩,
                                    effectsEmpty⟩
                                  simp [parameterMember, effectsEmpty]
                                rw [memberEq] at memberTrue
                                contradiction
                              simp [checkExpected, expectedCheckClause_refer,
                                propertyEq, propertyTypeEq, outputEq,
                                referenceDomainEq, notMember, failure] at success
                          | true =>
                              have memberParts :
                                  (!effectful = true ∧ (parameter == inner) = true) ∧
                                    propertyResult.effects.isEmpty = true := by
                                simpa [Bool.and_eq_true] using memberEq
                              have effectfulFalse : effectful = false := by
                                cases effectful <;> simp_all
                              subst effectful
                              have parameterType : parameter = inner :=
                                Ty.eq_of_beq_true memberParts.1.2
                              subst parameter
                              have pure : propertyResult.effects = [] := by
                                simpa using memberParts.2
                              have resultEq : result =
                                  (mergeResults (Ty.refComp (Ty.referents inner))
                                    [propertyResult] [.refer] []
                                    .a0TReferMember).withRule .a0Check := by
                                simpa [checkExpected, expectedCheckClause_refer,
                                  propertyEq, propertyTypeEq, outputEq,
                                  referenceDomainEq, memberEq, pure] using
                                  success.symm
                              subst result
                              have propertySupported :
                                  TypingManifestSupported propertyResult.trace := by
                                apply typing_manifest_drop_two
                                simpa [mergeResults, TypingResult.withRule] using
                                  supported
                              have propertyTyping := propertySound propertyResult
                                propertyEq propertySupported
                              simpa only [observation_withRule,
                                observation_mergeResults, List.map,
                                judgmentTermList] using
                                CheckJudgment.referMember environment property inner
                                  propertyResult.observation propertyTyping
                                  (by simpa [TypingResult.observation, Ty.pureFn]
                                    using propertyTypeEq) pure
                                  referenceDomainEq (compatible_self_sound inner)

private theorem refer_impossible_handler {scope : Nat}
    (environment : Environment scope) (term : Term scope) (expected : Ty)
    (synthError : TypingError)
    (selected : expectedCheckClause term expected = some .refer)
    (notRefer : ∀ arguments reference,
      term = .primitive .refer arguments →
        Ty.asUnary expected .typeFormRefComp ≠ some reference) :
    CheckExpectedSoundMotive scope environment term expected synthError := by
  rcases expected_refer_term_shape term expected selected with
    ⟨arguments, reference, shape, expectedShape⟩
  exact (notRefer arguments reference shape expectedShape).elim

private theorem presuppose_impossible_handler {scope : Nat}
    (environment : Environment scope) (term : Term scope) (expected : Ty)
    (synthError : TypingError)
    (selected : expectedCheckClause term expected = some .presupposeReference)
    (notPresuppose : ∀ arguments,
      term ≠ .primitive .presuppose arguments) :
    CheckExpectedSoundMotive scope environment term expected synthError := by
  rcases expected_presuppose_term_shape term expected selected with
    ⟨arguments, shape⟩
  exact (notPresuppose arguments shape).elim

private theorem local_impossible_handler {scope : Nat}
    (environment : Environment scope) (term : Term scope) (expected : Ty)
    (synthError : TypingError)
    (selected : expectedCheckClause term expected = some .local)
    (notLocalBody : ∀ body,
      term ≠ .primitive .local (.positional body .nil))
    (notLocal : ∀ arguments, term ≠ .primitive .local arguments) :
    CheckExpectedSoundMotive scope environment term expected synthError := by
  rcases expected_local_term_shape term expected selected with ⟨arguments, shape⟩
  exact (notLocal arguments shape).elim

private theorem reference_primitive_impossible_handler {scope : Nat}
    (environment : Environment scope) (term : Term scope) (expected : Ty)
    (synthError : TypingError)
    (selected : expectedCheckClause term expected = some .referencePrimitive)
    (notPrimitive : ∀ operator arguments reference,
      term = .primitive operator arguments →
        Ty.asUnary expected .typeFormRefComp ≠ some reference) :
    CheckExpectedSoundMotive scope environment term expected synthError := by
  rcases expected_reference_primitive_shape term expected selected with
    ⟨operator, arguments, reference, shape, expectedShape⟩
  exact (notPrimitive operator arguments reference shape expectedShape).elim

private theorem list_check_handler {scope : Nat}
    (environment : Environment scope) (synthError : TypingError)
    (arguments : TermList scope) (itemType : Ty)
    (_selected : expectedCheckClause (.primitive .list arguments)
      (Ty.list itemType) = some .list)
    (argumentsSound : CheckArgumentsSoundMotive scope environment arguments
      itemType) :
    CheckExpectedSoundMotive scope environment (.primitive .list arguments)
      (Ty.list itemType) synthError := by
  intro result success supported
  cases resultsEq : checkPositionalList environment arguments itemType with
  | error error =>
      simp [Ty.list, checkExpected.eq_9, expectedCheckClause_list_raw,
        resultsEq] at success
  | ok results =>
      have resultEq : result =
          (mergeResults (Ty.list itemType) results [] [] .a0TListCheck).withRule
            .a0Check := by
        simpa [Ty.list, checkExpected.eq_9, expectedCheckClause_list_raw,
          resultsEq] using
          success.symm
      subst result
      have resultsSupported : TypingResultsManifestSupported results := by
        apply typing_results_manifest_of_flattened
          (suffix := [.a0TListCheck, .a0Check])
        simpa [mergeResults, TypingResult.withRule] using supported
      simpa only [observation_withRule, observation_mergeResults] using
        CheckJudgment.list environment arguments itemType
          (results.map TypingResult.observation)
          (argumentsSound results resultsEq resultsSupported)

private theorem list_impossible_handler {scope : Nat}
    (environment : Environment scope) (term : Term scope) (expected : Ty)
    (synthError : TypingError)
    (selected : expectedCheckClause term expected = some .list)
    (notList : ∀ arguments itemType,
      term = .primitive .list arguments → expected ≠ Ty.list itemType) :
    CheckExpectedSoundMotive scope environment term expected synthError := by
  rcases expected_list_shape term expected selected with
    ⟨arguments, itemType, termShape, expectedShape⟩
  exact (notList arguments itemType termShape expectedShape).elim

private theorem no_expected_clause_handler {scope : Nat}
    (environment : Environment scope) (term : Term scope) (expected : Ty)
    (synthError : TypingError)
    (selected : expectedCheckClause term expected = none) :
    CheckExpectedSoundMotive scope environment term expected synthError := by
  intro result success _supported
  unfold checkExpected at success
  rw [selected] at success
  contradiction

private theorem check_arguments_nil_handler {scope : Nat}
    (environment : Environment scope) (expected : Ty) :
    CheckArgumentsSoundMotive scope environment .nil expected := by
  intro results success _supported
  have resultsEq : results = [] := by
    simpa [checkPositionalList] using success.symm
  subst results
  exact .nil environment expected

private theorem selection_check_handler {scope : Nat}
    (environment : Environment scope) (operator : FirstOrderPrimitive)
    (reference expected inner : Ty)
    (referenceShape : Ty.asUnary reference .typeFormReferents = some inner)
    (count property : Term scope)
    (selected : operator = .selectExactly ∨ operator = .selectAtLeast ∨
      operator = .selectAllBut)
    (countSound : CheckSoundMotive scope environment count Ty.natural)
    (propertySound : CheckSoundMotive scope environment property
      (Ty.pureFn [inner] Ty.content)) :
    CheckReferenceSoundMotive scope environment operator
      (.positional count (.positional property .nil)) reference expected := by
  intro expectedShape result success supported
  have referenceEq : reference = Ty.referents inner := by
    simpa [Ty.referents] using asUnary_eq_some referenceShape
  have expectedEq : expected = Ty.refComp (Ty.referents inner) := by
    have outer : expected = Ty.refComp reference := by
      simpa [Ty.refComp] using asUnary_eq_some expectedShape
    simpa [referenceEq] using outer
  subst reference
  subst expected
  cases countEq : check environment count Ty.natural with
  | error error =>
      rcases selected with rfl | rfl | rfl <;>
        simp [checkReferencePrimitive, countEq] at success
  | ok countResult =>
      cases guardEq : (operator != .selectAllBut && !provablyPositive count) with
      | true =>
          rcases selected with rfl | rfl | rfl <;>
            simp_all [checkReferencePrimitive, countEq, guardEq, failure]
      | false =>
          have floor : operator = .selectAllBut ∨ provablyPositive count = true := by
            rcases selected with rfl | rfl | rfl
            · right
              cases positive : provablyPositive count with
              | false =>
                  have different :
                      (FirstOrderPrimitive.selectExactly != .selectAllBut) = true :=
                    rfl
                  rw [different, positive] at guardEq
                  contradiction
              | true => rfl
            · right
              cases positive : provablyPositive count with
              | false =>
                  have different :
                      (FirstOrderPrimitive.selectAtLeast != .selectAllBut) = true :=
                    rfl
                  rw [different, positive] at guardEq
                  contradiction
              | true => rfl
            · exact Or.inl rfl
          cases propertyEq : check environment property
              (Ty.pureFn [inner] Ty.content) with
          | error error =>
              rcases selected with rfl | rfl | rfl <;>
                simp [checkReferencePrimitive, countEq, guardEq,
                  propertyEq] at success
          | ok propertyResult =>
              let rule : M2TypingRuleId :=
                if operator == .selectExactly then .a0TSelectExactly
                else if operator == .selectAtLeast then .b1TSelectAtLeast
                else .b1TSelectAllBut
              have executionEq : checkReferencePrimitive environment operator
                  (.positional count (.positional property .nil))
                  (Ty.referents inner) (Ty.refComp (Ty.referents inner)) =
                  .ok ((mergeResults (Ty.refComp (Ty.referents inner))
                    [countResult, propertyResult] [.refer] [] rule).withRule
                    .a0Check) := by
                rcases selected with rfl | rfl | rfl <;>
                  simp [checkReferencePrimitive, countEq, guardEq,
                    propertyEq, rule]
              have resultEq : result =
                  (mergeResults (Ty.refComp (Ty.referents inner))
                    [countResult, propertyResult] [.refer] [] rule).withRule
                    .a0Check := by
                rw [executionEq] at success
                exact Except.ok.inj success.symm
              subst result
              have supportedRaw : TypingManifestSupported
                  (countResult.trace ++ propertyResult.trace ++ [rule, .a0Check]) := by
                simpa [mergeResults, TypingResult.withRule] using supported
              have countSupported : TypingManifestSupported countResult.trace :=
                typing_manifest_sublist supportedRaw (by
                  intro item member
                  simp [member])
              have propertySupported :
                  TypingManifestSupported propertyResult.trace :=
                typing_manifest_sublist supportedRaw (by
                  intro item member
                  simp [member])
              simpa only [observation_withRule, observation_mergeResults,
                List.map, judgmentTermList] using
                CheckJudgment.select environment operator count property inner
                  countResult.observation propertyResult.observation selected
                  (countSound countResult countEq countSupported) floor
                  (propertySound propertyResult propertyEq propertySupported)

private theorem reference_primitive_checkExpected_handler {scope : Nat}
    (environment : Environment scope) (expected : Ty)
    (synthError : TypingError) (operator : FirstOrderPrimitive)
    (arguments : TermList scope) (reference : Ty)
    (expectedShape : Ty.asUnary expected .typeFormRefComp = some reference)
    (selected : expectedCheckClause (.primitive operator arguments) expected =
      some .referencePrimitive)
    (referenceSound : CheckReferenceSoundMotive scope environment operator
      arguments reference expected) :
    CheckExpectedSoundMotive scope environment (.primitive operator arguments)
      expected synthError := by
  intro result success supported
  unfold checkExpected at success
  rw [selected] at success
  simp [expectedShape] at success
  exact referenceSound expectedShape result success supported

private theorem check_arguments_cons_handler {scope : Nat}
    (environment : Environment scope) (expected : Ty)
    (head : Term scope) (tail : TermList scope)
    (headSound : CheckSoundMotive scope environment head expected)
    (tailSound : CheckArgumentsSoundMotive scope environment tail expected) :
    CheckArgumentsSoundMotive scope environment (.positional head tail) expected := by
  intro results success supported
  cases headEq : check environment head expected with
  | error error =>
      simp [checkPositionalList, headEq] at success
  | ok headResult =>
      cases tailEq : checkPositionalList environment tail expected with
      | error error =>
          simp [checkPositionalList, headEq, tailEq] at success
      | ok tailResults =>
          have resultsEq : results = headResult :: tailResults := by
            simpa [checkPositionalList, headEq, tailEq] using success.symm
          subst results
          rcases typing_results_manifest_cons supported with
            ⟨headSupported, tailSupported⟩
          exact CheckArgumentsJudgment.positional environment head tail expected
            headResult.observation (tailResults.map TypingResult.observation)
            (headSound headResult headEq headSupported)
            (tailSound tailResults tailEq tailSupported)

private theorem presuppose_check_handler {scope : Nat}
    (environment : Environment scope) (expected : Ty)
    (condition body : Term scope)
    (conditionSound : CheckSoundMotive scope environment condition Ty.content)
    (bodySound : CheckSoundMotive scope environment body expected) :
    CheckPresupposeSoundMotive scope environment
      (.positional condition (.positional body .nil)) expected := by
  intro inner expectedShape result success supported
  have expectedEq : expected = Ty.refComp inner := by
    simpa [Ty.refComp] using asUnary_eq_some expectedShape
  subst expected
  cases classifiedEq : expectedOnlySynthesisForm body with
  | false =>
      simp [checkPresupposeReference, classifiedEq, failure] at success
  | true =>
      cases conditionEq : check environment condition Ty.content with
      | error error =>
          simp [checkPresupposeReference, classifiedEq, conditionEq] at success
      | ok conditionResult =>
          cases bodyEq : check environment body (Ty.refComp inner) with
          | error error =>
              simp [checkPresupposeReference, classifiedEq, conditionEq,
                bodyEq] at success
          | ok bodyResult =>
              have resultEq : result =
                  (mergeResults (Ty.refComp inner) [conditionResult, bodyResult]
                    [.projective] [.presuppose "condition" (Ty.refComp inner)]
                    .b1TPresupposeReference).withRule .a0Check := by
                simpa [checkPresupposeReference, classifiedEq, conditionEq,
                  bodyEq] using success.symm
              subst result
              have supportedRaw : TypingManifestSupported
                  (conditionResult.trace ++ bodyResult.trace ++
                    [.b1TPresupposeReference, .a0Check]) := by
                simpa [mergeResults, TypingResult.withRule] using supported
              have conditionSupported :
                  TypingManifestSupported conditionResult.trace :=
                typing_manifest_sublist supportedRaw (by
                  intro item member
                  simp [member])
              have bodySupported : TypingManifestSupported bodyResult.trace :=
                typing_manifest_sublist supportedRaw (by
                  intro item member
                  simp [member])
              simpa only [observation_withRule, observation_mergeResults,
                List.map, judgmentTermList] using
                CheckJudgment.presupposeReference environment condition body inner
                  conditionResult.observation bodyResult.observation
                  (conditionSound conditionResult conditionEq conditionSupported)
                  (bodySound bodyResult bodyEq bodySupported)
                  (expected_only_classifier_sound body classifiedEq)

private theorem presuppose_rejected_handler {scope : Nat}
    (environment : Environment scope) (expected : Ty)
    (condition body : Term scope)
    (rejected : (!expectedOnlySynthesisForm body) = true) :
    CheckPresupposeSoundMotive scope environment
      (.positional condition (.positional body .nil)) expected := by
  intro inner expectedShape result success _supported
  simp [checkPresupposeReference, rejected, failure] at success

private theorem presuppose_checkExpected_handler {scope : Nat}
    (environment : Environment scope) (expected : Ty)
    (synthError : TypingError) (arguments : TermList scope)
    (selected : expectedCheckClause (.primitive .presuppose arguments) expected =
      some .presupposeReference)
    (presupposeSound : CheckPresupposeSoundMotive scope environment arguments
      expected) :
    CheckExpectedSoundMotive scope environment (.primitive .presuppose arguments)
      expected synthError := by
  cases expectedShape : Ty.asUnary expected .typeFormRefComp with
  | none => simp [expectedCheckClause, expectedShape] at selected
  | some inner =>
      intro result success supported
      unfold checkExpected at success
      rw [selected] at success
      exact presupposeSound inner expectedShape result success supported

private theorem synth_primitive_manifest {scope : Nat}
    (environment : Environment scope) (operator : FirstOrderPrimitive)
    (arguments : TermList scope) (result : TypingResult)
    (primitiveSound : TypingManifestSupported result.trace →
      PrimitiveJudgment environment operator arguments result.observation)
    (supported : TypingManifestSupported result.trace) :
    SynthJudgment environment (.primitive operator arguments) result.observation :=
  .primitive environment operator arguments result.observation
    (primitiveSound supported)

private theorem synth_bound_handler {scope : Nat}
    (environment : Environment scope) (index : Fin scope) :
    SynthSoundMotive scope environment (.bound index) := by
  intro result success _supported
  have resultEq : result = {
      type := environment.bound index
      trace := [.a0TVariable, .a0Synth] } := by
    simpa [synth] using success.symm
  subst result
  exact .bound environment index

private theorem synth_free_handler {scope : Nat}
    (environment : Environment scope) (identity : FreeId) (type : Ty)
    (found : environment.lookupFree identity = some type) :
    SynthSoundMotive scope environment (.free identity) := by
  intro result success _supported
  have resultEq : result = {
      type
      trace := [.a0TVariable, .a0Synth] } := by
    simpa [synth, found] using success.symm
  subst result
  exact .free environment identity type found

private theorem synth_natural_handler {scope : Nat}
    (environment : Environment scope) (value : Nat) :
    SynthSoundMotive scope environment (.natural value) := by
  intro result success _supported
  have resultEq : result = {
      type := Ty.natural
      trace := [.a0TNatural, .a0Synth] } := by
    simpa [synth] using success.symm
  subst result
  exact .natural environment value

private theorem synth_string_handler {scope : Nat}
    (environment : Environment scope) (value : String) :
    SynthSoundMotive scope environment (.string value) := by
  intro result success _supported
  have resultEq : result = {
      type := Ty.text
      trace := [.m2TString, .a0Synth] } := by
    simpa [synth] using success.symm
  subst result
  exact .string environment value

private theorem synth_lambda_handler {scope : Nat}
    (environment : Environment scope) (binderType : Ty)
    (body : Term (scope + 1))
    (bodySound : SynthSoundMotive (scope + 1)
      (environment.extend binderType) body) :
    SynthSoundMotive scope environment (.lambda binderType body) := by
  intro result success supported
  cases bodyEq : synth (environment.extend binderType) body with
  | error error => simp [synth, bodyEq] at success
  | ok bodyResult =>
      let effectful := !bodyResult.effects.isEmpty
      let rule : M2TypingRuleId :=
        if effectful then .a0TLambdaEffectful else .a0TLambdaPure
      have resultEq : result = {
          type := .function effectful [binderType] bodyResult.type
          obligations := bodyResult.obligations
          trace := bodyResult.trace ++ [rule, .a0Synth] } := by
        simpa [synth, bodyEq, effectful, rule] using success.symm
      subst result
      have bodySupported : TypingManifestSupported bodyResult.trace := by
        apply typing_manifest_drop_two
        simpa [effectful, rule] using supported
      simpa [TypingResult.observation, effectful, rule] using
        SynthJudgment.lambda environment binderType body bodyResult.observation
          (bodySound bodyResult bodyEq bodySupported)

private theorem synth_bind_handler {scope : Nat}
    (environment : Environment scope) (binderType : Ty)
    (computation : Term scope) (body : Term (scope + 1))
    (bodySound : SynthSoundMotive (scope + 1)
      (environment.extend binderType) body)
    (referenceSound : CheckSoundMotive scope environment computation
      (Ty.refComp binderType))
    (performanceSound : CheckSoundMotive scope environment computation
      (Ty.perfComp binderType)) :
    SynthSoundMotive scope environment (.bind binderType computation body) := by
  intro result success supported
  cases bodyEq : synth (environment.extend binderType) body with
  | error error => simp [synth, bodyEq] at success
  | ok bodyResult =>
      cases referenceEq : check environment computation (Ty.refComp binderType) with
      | ok referenceResult =>
          have resultEq : result =
              (mergeResults bodyResult.type [referenceResult, bodyResult] [] []
                .a0TBindReference).withRule .a0Synth := by
            simpa [synth, bodyEq, referenceEq] using success.symm
          subst result
          have supportedRaw : TypingManifestSupported
              (referenceResult.trace ++ bodyResult.trace ++
                [.a0TBindReference, .a0Synth]) := by
            simpa [mergeResults, TypingResult.withRule] using supported
          have referenceSupported :
              TypingManifestSupported referenceResult.trace :=
            typing_manifest_sublist supportedRaw (by
              intro item member
              simp [member])
          have bodySupported : TypingManifestSupported bodyResult.trace :=
            typing_manifest_sublist supportedRaw (by
              intro item member
              simp [member])
          change SynthJudgment environment (.bind binderType computation body)
            (mergeObservations bodyResult.type
              [referenceResult.observation, bodyResult.observation])
          exact SynthJudgment.bindReference environment binderType computation body
            referenceResult.observation bodyResult.observation
            (referenceSound referenceResult referenceEq referenceSupported)
            (bodySound bodyResult bodyEq bodySupported)
      | error referenceError =>
          cases performanceEq : check environment computation
              (Ty.perfComp binderType) with
          | error performanceError =>
              simp [synth, bodyEq, referenceEq, performanceEq] at success
          | ok performanceResult =>
              let resultType := match bodyResult.type with
                | .named .typeFormAct _ => Ty.discourse
                | type => if type == Ty.discourse then Ty.discourse else type
              let rule : M2TypingRuleId := match bodyResult.type with
                | .named .typeFormAct _ => .a0TBindPerformanceAct
                | .named .typeFormPerfComp _ => .a0TBindPerformanceComp
                | _ => .a0TBindPerformanceDiscourse
              simp [synth, bodyEq, referenceEq, performanceEq,
                resultType, rule] at success
              cases success
              have ruleMember : rule ∈
                  ((mergeResults resultType [performanceResult, bodyResult]
                    (if resultType == Ty.discourse then [.performance] else [])
                    [] rule).withRule .a0Synth).trace := by
                simp [mergeResults, TypingResult.withRule]
              have implemented := supported.supported
              rw [List.all_eq_true] at implemented
              have ruleImplemented := implemented rule ruleMember
              have ruleCases : rule = .a0TBindPerformanceAct ∨
                  rule = .a0TBindPerformanceComp ∨
                  rule = .a0TBindPerformanceDiscourse := by
                unfold rule
                cases bodyTypeEq : bodyResult.type with
                | named name arguments =>
                    cases name <;> simp
                | «variable» name | index name => simp
                | function effectful parameters output => simp
              rcases ruleCases with ruleEq | ruleEq | ruleEq
              · have excluded :
                    typingRuleImplemented .a0TBindPerformanceAct = false := by
                  decide
                rw [ruleEq, excluded] at ruleImplemented
                contradiction
              · have excluded :
                    typingRuleImplemented .a0TBindPerformanceComp = false := by
                  decide
                rw [ruleEq, excluded] at ruleImplemented
                contradiction
              · have excluded :
                    typingRuleImplemented .a0TBindPerformanceDiscourse = false := by
                  decide
                rw [ruleEq, excluded] at ruleImplemented
                contradiction

private theorem synth_application_handler {scope : Nat}
    (environment : Environment scope) (function : Term scope)
    (arguments : TermList scope)
    (functionSound : SynthSoundMotive scope environment function)
    (applySound : ∀ functionResult,
      ApplySoundMotive scope environment functionResult arguments) :
    SynthSoundMotive scope environment (.apply function arguments) := by
  intro result success supported
  cases functionEq : synth environment function with
  | error error => simp [synth, functionEq] at success
  | ok functionResult =>
      cases applyEq : applyFunction environment functionResult arguments with
      | error error => simp [synth, functionEq, applyEq] at success
      | ok applied =>
          have resultEq : result = applied := by
            simpa [synth, functionEq, applyEq] using success.symm
          subst result
          rcases applySound functionResult applied applyEq supported with
            ⟨functionSupported, applicationTyping⟩
          exact SynthJudgment.application environment function arguments
            functionResult.observation applied.observation
            (functionSound functionResult functionEq functionSupported)
            applicationTyping

private theorem synthPerform_excluded_handler {scope : Nat}
    (environment : Environment scope) (arguments : TermList scope) :
    PerformSoundMotive scope environment arguments := by
  intro result success supported
  cases arguments with
  | nil => simp [synthPerform, failure] at success
  | labelled label head tail => simp [synthPerform, failure] at success
  | positional first tail =>
      cases tail with
      | nil =>
          cases actEq : synth environment first with
          | error error => simp [synthPerform, actEq] at success
          | ok actResult =>
              cases forceEq : Ty.asUnary actResult.type .typeFormAct with
              | none => simp [synthPerform, actEq, forceEq, failure] at success
              | some force =>
                  have resultEq : result =
                      (mergeResults (Ty.perfComp (Ty.actOccurrence force))
                        [actResult] [.performance] [] .a0TPerform).withRule
                        .a0Synth := by
                    simpa [synthPerform, actEq, forceEq] using success.symm
                  subst result
                  exact (typing_manifest_excludes (rule := .a0TPerform)
                    supported (by
                    simp [mergeResults, TypingResult.withRule]) (by
                    decide)).elim
      | labelled label head rest => simp [synthPerform, failure] at success
      | positional act rest =>
          cases rest with
          | nil =>
              cases roleEq : check environment first Ty.occurrenceRole with
              | error error => simp [synthPerform, roleEq] at success
              | ok roleResult =>
                  cases actEq : synth environment act with
                  | error error => simp [synthPerform, roleEq, actEq] at success
                  | ok actResult =>
                      cases forceEq : Ty.asUnary actResult.type .typeFormAct with
                      | none =>
                          simp [synthPerform, roleEq, actEq, forceEq, failure]
                            at success
                      | some force =>
                          have resultEq : result =
                              (mergeResults (Ty.perfComp (Ty.actOccurrence force))
                                [roleResult, actResult] [.performance] []
                                .m2TPerformRole).withRule .a0Synth := by
                            simpa [synthPerform, roleEq, actEq, forceEq]
                              using success.symm
                          subst result
                          exact (typing_manifest_excludes (rule := .m2TPerformRole)
                            supported (by
                            simp [mergeResults, TypingResult.withRule]) (by
                            decide)).elim
          | positional third more => simp [synthPerform, failure] at success
          | labelled label third more => simp [synthPerform, failure] at success

private theorem threshold_handler {scope : Nat}
    (environment : Environment scope) (kind property purpose : Term scope)
    (kindSound : CheckSoundMotive scope environment kind Ty.thresholdKind)
    (propertySound : SynthSoundMotive scope environment property)
    (purposeSound : CheckSoundMotive scope environment purpose
      (Ty.referents Ty.entity)) :
    ThresholdSoundMotive scope environment
      (.positional kind (.positional property (.positional purpose .nil))) := by
  intro result success supported
  cases kindEq : check environment kind Ty.thresholdKind with
  | error error => simp [synthAdmissibleThreshold, kindEq] at success
  | ok kindResult =>
      cases propertyEq : synth environment property with
      | error error =>
          simp [synthAdmissibleThreshold, kindEq, propertyEq] at success
      | ok propertyResult =>
          cases functionEq : oneArgumentFunction propertyResult with
          | none =>
              simp [synthAdmissibleThreshold, kindEq, propertyEq,
                functionEq, failure] at success
          | some pair =>
              rcases pair with ⟨effectful, inner⟩
              cases effectful with
              | true =>
                  simp [synthAdmissibleThreshold, kindEq, propertyEq,
                    functionEq, failure] at success
              | false =>
                  cases pureEq : isPure propertyResult with
                  | false =>
                      simp [synthAdmissibleThreshold, kindEq, propertyEq,
                        functionEq, pureEq, failure] at success
                  | true =>
                      cases purposeEq : check environment purpose
                          (Ty.referents Ty.entity) with
                      | error error =>
                          simp [synthAdmissibleThreshold, kindEq, propertyEq,
                            functionEq, pureEq, purposeEq] at success
                      | ok purposeResult =>
                          have resultEq : result =
                              (mergeResults (Ty.pureFn [Ty.natural] Ty.content)
                                [kindResult, propertyResult, purposeResult]
                                [] [] .a0TAdmissibleThreshold).withRule
                                .a0Synth := by
                            simpa [synthAdmissibleThreshold, kindEq, propertyEq,
                              functionEq, pureEq, purposeEq] using success.symm
                          subst result
                          have supportedRaw : TypingManifestSupported
                              (kindResult.trace ++ propertyResult.trace ++
                                purposeResult.trace ++
                                [.a0TAdmissibleThreshold, .a0Synth]) := by
                            simpa [mergeResults, TypingResult.withRule,
                              List.append_assoc] using supported
                          have kindSupported : TypingManifestSupported kindResult.trace :=
                            typing_manifest_sublist supportedRaw (by
                              intro item member
                              simp [member])
                          have propertySupported :
                              TypingManifestSupported propertyResult.trace :=
                            typing_manifest_sublist supportedRaw (by
                              intro item member
                              simp [member])
                          have purposeSupported :
                              TypingManifestSupported purposeResult.trace :=
                            typing_manifest_sublist supportedRaw (by
                              intro item member
                              simp [member])
                          have propertyType : propertyResult.observation.type =
                              Ty.pureFn [inner] Ty.content := by
                            simpa [TypingResult.observation, Ty.pureFn] using
                              oneArgumentFunction_sound functionEq
                          have pure : propertyResult.observation.effects = [] :=
                            (purity_classifier_sound_complete propertyResult).mp
                              pureEq
                          simpa only [observation_withRule,
                            observation_mergeResults, List.map,
                            judgmentTermList] using
                            PrimitiveJudgment.admissibleThreshold environment kind
                              property purpose kindResult.observation
                              propertyResult.observation purposeResult.observation
                              inner (kindSound kindResult kindEq kindSupported)
                              (propertySound propertyResult propertyEq
                                propertySupported) propertyType pure
                              (purposeSound purposeResult purposeEq
                                purposeSupported)

private theorem synthPresuppose_excluded_handler {scope : Nat}
    (environment : Environment scope) (condition body : Term scope) :
    PresupposeSoundMotive scope environment
      (.positional condition (.positional body .nil)) := by
  intro result success supported
  cases conditionEq : check environment condition Ty.content with
  | error error => simp [synthPresuppose, conditionEq] at success
  | ok conditionResult =>
      cases bodyEq : synth environment body with
      | error error => simp [synthPresuppose, conditionEq, bodyEq] at success
      | ok bodyResult =>
          cases categoryEq : computationCategoryClassifier bodyResult.type with
          | false =>
              simp [synthPresuppose, conditionEq, bodyEq, categoryEq,
                failure] at success
          | true =>
              have resultEq : result =
                  (mergeResults bodyResult.type [conditionResult, bodyResult]
                    [.projective] [.presuppose "condition" bodyResult.type]
                    .b1TPresupposeSynth).withRule .a0Synth := by
                simpa [synthPresuppose, conditionEq, bodyEq, categoryEq]
                  using success.symm
              subst result
              exact (typing_manifest_excludes (rule := .b1TPresupposeSynth)
                supported (by simp [mergeResults, TypingResult.withRule]) (by
                decide)).elim

private theorem primitive_constant_handler {scope : Nat}
    (environment : Environment scope) (operator : FirstOrderPrimitive)
    (arguments : TermList scope) (type : Ty) (traceRule : M2TypingRuleId)
    (rule : ConstantPrimitiveRule operator { type })
    (execution : synthPrimitive environment operator arguments =
      synthPrimitive.constant operator arguments traceRule type) :
    PrimitiveSoundMotive scope environment operator arguments := by
  intro result success _supported
  rw [execution] at success
  cases arguments with
  | nil =>
      have manifest := constant_rule_manifest rule
      have resultEq : result = { type, trace := [traceRule, .a0Synth] } := by
        simpa [synthPrimitive.constant, positionalTerms, manifest] using
          success.symm
      subst result
      exact PrimitiveJudgment.constant environment operator { type } rule manifest
  | positional head tail =>
      cases tailTerms : positionalTerms tail <;>
        simp [synthPrimitive.constant, positionalTerms, tailTerms, failure] at success
  | labelled label head tail =>
      simp [synthPrimitive.constant, positionalTerms, failure] at success

private theorem primitive_projective_constant_handler {scope : Nat}
    (environment : Environment scope) (operator : FirstOrderPrimitive)
    (arguments : TermList scope)
    (rule : ConstantPrimitiveRule operator {
      type := Ty.referents Ty.entity
      effects := [.projective]
      obligations := [.definedness operator.name (Ty.referents Ty.entity)] })
    (execution : synthPrimitive environment operator arguments = do
      let result ← synthPrimitive.constant operator arguments .m2TCoreConstant
        (Ty.referents Ty.entity)
      pure { result with
        effects := [.projective]
        obligations := [.definedness operator.name (Ty.referents Ty.entity)] }) :
    PrimitiveSoundMotive scope environment operator arguments := by
  intro result success _supported
  rw [execution] at success
  cases arguments with
  | nil =>
      have manifest := constant_rule_manifest rule
      have resultEq : result = {
          type := Ty.referents Ty.entity
          effects := [.projective]
          obligations := [.definedness operator.name (Ty.referents Ty.entity)]
          trace := [.m2TCoreConstant, .a0Synth] } := by
        simpa [synthPrimitive.constant, positionalTerms, manifest] using
          success.symm
      subst result
      exact PrimitiveJudgment.constant environment operator _ rule manifest
  | positional head tail =>
      cases tailTerms : positionalTerms tail <;>
        simp [synthPrimitive.constant, positionalTerms, tailTerms, failure] at success
  | labelled label head tail =>
      simp [synthPrimitive.constant, positionalTerms, failure] at success

private theorem primitive_combine_handler {scope : Nat}
    (environment : Environment scope) (first second : Term scope)
    (firstSound : SynthSoundMotive scope environment first)
    (secondSound : SynthSoundMotive scope environment second) :
    PrimitiveSoundMotive scope environment .combine
      (.positional first (.positional second .nil)) := by
  intro result success supported
  cases firstEq : synth environment first with
  | error error => simp [synthPrimitive, firstEq] at success
  | ok firstResult =>
      cases secondEq : synth environment second with
      | error error => simp [synthPrimitive, firstEq, secondEq] at success
      | ok secondResult =>
          cases firstReferenceEq : Ty.referenceInner firstResult.type with
          | none =>
              simp [synthPrimitive, firstEq, secondEq, firstReferenceEq,
                failure] at success
          | some firstInner =>
              cases secondReferenceEq : Ty.referenceInner secondResult.type with
              | none =>
                  simp [synthPrimitive, firstEq, secondEq, firstReferenceEq,
                    secondReferenceEq, failure] at success
              | some secondInner =>
                  cases firstCompatible : Ty.compatible firstInner secondInner with
                  | true =>
                      have resultEq : result =
                          (mergeResults (Ty.referents secondInner)
                            [firstResult, secondResult] [] [] .m2TCombine).withRule
                            .a0Synth := by
                        simpa [synthPrimitive, firstEq, secondEq,
                          firstReferenceEq, secondReferenceEq,
                          firstCompatible] using success.symm
                      subst result
                      have supportedRaw : TypingManifestSupported
                          (firstResult.trace ++ secondResult.trace ++
                            [.m2TCombine, .a0Synth]) := by
                        simpa [mergeResults, TypingResult.withRule] using supported
                      have firstSupported : TypingManifestSupported firstResult.trace :=
                        typing_manifest_sublist supportedRaw (by
                          intro item member
                          simp [member])
                      have secondSupported :
                          TypingManifestSupported secondResult.trace :=
                        typing_manifest_sublist supportedRaw (by
                          intro item member
                          simp [member])
                      change PrimitiveJudgment environment .combine
                        (.positional first (.positional second .nil))
                        (mergeObservations (Ty.referents secondInner)
                          [firstResult.observation, secondResult.observation])
                      exact PrimitiveJudgment.combine environment first second
                          firstResult.observation secondResult.observation
                          firstInner secondInner secondInner
                          (firstSound firstResult firstEq firstSupported)
                          (secondSound secondResult secondEq secondSupported)
                          firstReferenceEq secondReferenceEq
                          (Or.inl ⟨firstCompatible, rfl⟩)
                  | false =>
                      cases secondCompatible : Ty.compatible secondInner firstInner with
                      | false =>
                          simp [synthPrimitive, firstEq, secondEq,
                            firstReferenceEq, secondReferenceEq, firstCompatible,
                            secondCompatible, failure] at success
                      | true =>
                          have resultEq : result =
                              (mergeResults (Ty.referents firstInner)
                                [firstResult, secondResult] [] [] .m2TCombine).withRule
                                .a0Synth := by
                            simpa [synthPrimitive, firstEq, secondEq,
                              firstReferenceEq, secondReferenceEq,
                              firstCompatible, secondCompatible] using success.symm
                          subst result
                          have supportedRaw : TypingManifestSupported
                              (firstResult.trace ++ secondResult.trace ++
                                [.m2TCombine, .a0Synth]) := by
                            simpa [mergeResults, TypingResult.withRule] using supported
                          have firstSupported :
                              TypingManifestSupported firstResult.trace :=
                            typing_manifest_sublist supportedRaw (by
                              intro item member
                              simp [member])
                          have secondSupported :
                              TypingManifestSupported secondResult.trace :=
                            typing_manifest_sublist supportedRaw (by
                              intro item member
                              simp [member])
                          change PrimitiveJudgment environment .combine
                            (.positional first (.positional second .nil))
                            (mergeObservations (Ty.referents firstInner)
                              [firstResult.observation, secondResult.observation])
                          exact PrimitiveJudgment.combine environment first second
                              firstResult.observation secondResult.observation
                              firstInner secondInner firstInner
                              (firstSound firstResult firstEq firstSupported)
                              (secondSound secondResult secondEq secondSupported)
                              firstReferenceEq secondReferenceEq
                              (Or.inr ⟨firstCompatible, secondCompatible, rfl⟩)

private theorem primitive_memberOf_excluded_handler {scope : Nat}
    (environment : Environment scope) (arguments : TermList scope) :
    PrimitiveSoundMotive scope environment .memberOf arguments := by
  intro result success supported
  cases arityEq : expectArity FirstOrderPrimitive.memberOf arguments 2 with
  | error error =>
      simp [synthPrimitive, arityEq] at success
  | ok operands =>
      cases operands with
      | nil => simp [synthPrimitive, arityEq, failure] at success
      | cons first tail =>
          cases tail with
          | nil => simp [synthPrimitive, arityEq, failure] at success
          | cons second rest =>
              cases rest with
              | cons third rest =>
                  simp [synthPrimitive, arityEq, failure] at success
              | nil =>
                  rcases first with ⟨item, itemSmaller⟩
                  rcases second with ⟨setTerm, setSmaller⟩
                  cases itemEq : synth environment item with
                  | error error =>
                      simp [synthPrimitive, arityEq, itemEq] at success
                  | ok itemResult =>
                      cases setEq : synth environment setTerm with
                      | error error =>
                          simp [synthPrimitive, arityEq, itemEq, setEq] at success
                      | ok setResult =>
                          cases setTypeEq : Ty.asUnary setResult.type .typeFormSet with
                          | none =>
                              simp [synthPrimitive, arityEq, itemEq, setEq,
                                setTypeEq, failure] at success
                          | some inner =>
                              cases compatibleEq :
                                  Ty.compatible itemResult.type inner with
                              | false =>
                                  simp [synthPrimitive, arityEq, itemEq, setEq,
                                    setTypeEq, compatibleEq, failure] at success
                              | true =>
                                  have resultEq : result =
                                      (mergeResults Ty.content [itemResult, setResult]
                                        [] [] .m2TMemberOf).withRule .a0Synth := by
                                    simpa [synthPrimitive, arityEq, itemEq, setEq,
                                      setTypeEq, compatibleEq] using success.symm
                                  subst result
                                  have allSupported := supported.supported
                                  rw [List.all_eq_true] at allSupported
                                  have implemented :
                                      typingRuleImplemented .m2TMemberOf = true :=
                                    allSupported .m2TMemberOf (by
                                      simp [mergeResults, TypingResult.withRule])
                                  have excluded :
                                      typingRuleImplemented .m2TMemberOf = false := by
                                    decide
                                  rw [excluded] at implemented
                                  contradiction

private theorem primitive_force_handler {scope : Nat}
    (environment : Environment scope) (operator : FirstOrderPrimitive)
    (force : Ty) (content : Term scope)
    (selected : (operator = .assert ∧ force = Ty.assertion) ∨
      (operator = .express ∧ force = Ty.expressive))
    (contentSound : CheckSoundMotive scope environment content Ty.content) :
    PrimitiveSoundMotive scope environment operator
      (.positional content .nil) := by
  intro result success supported
  cases contentEq : check environment content Ty.content with
  | error error =>
      rcases selected with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [synthPrimitive, contentEq] at success
  | ok contentResult =>
      have executionEq : synthPrimitive environment operator
          (.positional content .nil) = .ok {
            type := Ty.act force
            obligations := contentResult.obligations
            trace := contentResult.trace ++ [.m2TForce, .a0Synth] } := by
        rcases selected with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp [synthPrimitive, contentEq]
      rw [executionEq] at success
      cases success
      have contentSupported : TypingManifestSupported contentResult.trace :=
        typing_manifest_drop_two supported
      exact PrimitiveJudgment.forceContent environment operator content force
        contentResult.observation selected
        (contentSound contentResult contentEq contentSupported)

private theorem primitive_mention_handler {scope : Nat}
    (environment : Environment scope) (value : Term scope)
    (valueSound : SynthSoundMotive scope environment value) :
    PrimitiveSoundMotive scope environment .mention (.positional value .nil) := by
  intro result success supported
  cases valueEq : synth environment value with
  | error error => simp [synthPrimitive, valueEq] at success
  | ok valueResult =>
      have resultEq : result = {
          type := Ty.act Ty.expressive
          obligations := valueResult.obligations
          trace := valueResult.trace ++ [.m2TForce, .a0Synth] } := by
        simpa [synthPrimitive, valueEq] using success.symm
      subst result
      exact PrimitiveJudgment.mention environment value valueResult.observation
        (valueSound valueResult valueEq (typing_manifest_drop_two supported))

private theorem primitive_discourse_handler {scope : Nat}
    (environment : Environment scope) (arguments : TermList scope)
    (argumentsSound : SynthArgumentsSoundMotive scope environment arguments) :
    PrimitiveSoundMotive scope environment .do arguments := by
  intro result success supported
  cases resultsEq : synthPositionalList environment arguments with
  | error error => simp [synthPrimitive, resultsEq] at success
  | ok results =>
      cases admissibleEq : results.all (fun item => item.type == Ty.discourse ||
          (Ty.asUnary item.type .typeFormAct).isSome ||
          (Ty.asUnary item.type .typeFormPerfComp).isSome) with
      | false =>
          have bad : ∃ item, item ∈ results ∧
              ((item.type == Ty.discourse) = false ∧
                Ty.asUnary item.type .typeFormAct = none) ∧
                Ty.asUnary item.type .typeFormPerfComp = none := by
            rcases (List.all_eq_false.mp admissibleEq) with
              ⟨item, member, itemBad⟩
            refine ⟨item, member, ?_⟩
            simpa using itemBad
          simp [synthPrimitive, resultsEq, bad, failure] at success
      | true =>
          have admissibleEvery : ∀ item ∈ results,
              (item.type == Ty.discourse ||
                (Ty.asUnary item.type .typeFormAct).isSome ||
                (Ty.asUnary item.type .typeFormPerfComp).isSome) = true := by
            simpa [List.all_eq_true] using admissibleEq
          have noBad : ¬∃ item, item ∈ results ∧
              ((item.type == Ty.discourse) = false ∧
                Ty.asUnary item.type .typeFormAct = none) ∧
                Ty.asUnary item.type .typeFormPerfComp = none := by
            rintro ⟨item, member, bad, performanceNone⟩
            have good := admissibleEvery item member
            simp [bad.1, bad.2, performanceNone] at good
          have resultEq : result =
              (mergeResults Ty.discourse results [.performance] []
                .m2TForce).withRule .a0Synth := by
            simpa [synthPrimitive, resultsEq, admissibleEq, noBad] using
              success.symm
          subst result
          have resultsSupported : TypingResultsManifestSupported results := by
            apply typing_results_manifest_of_flattened
              (suffix := [.m2TForce, .a0Synth])
            simpa [mergeResults, TypingResult.withRule] using supported
          have admissible :
              (results.map TypingResult.observation).all (fun item =>
                item.type == Ty.discourse ||
                (Ty.asUnary item.type .typeFormAct).isSome ||
                (Ty.asUnary item.type .typeFormPerfComp).isSome) = true := by
            simpa [List.all_map, TypingResult.observation] using admissibleEq
          simpa only [observation_withRule, observation_mergeResults] using
            PrimitiveJudgment.discourse environment arguments
              (results.map TypingResult.observation)
              (argumentsSound results resultsEq resultsSupported) admissible

private theorem primitive_polar_handler {scope : Nat}
    (environment : Environment scope) (content : Term scope)
    (contentSound : CheckSoundMotive scope environment content Ty.content) :
    PrimitiveSoundMotive scope environment .polar (.positional content .nil) := by
  intro result success supported
  cases contentEq : check environment content Ty.content with
  | error error => simp [synthPrimitive, contentEq] at success
  | ok contentResult =>
      have resultEq : result =
          (mergeResults (Ty.query (.named .sortBool [])) [contentResult]
            [] [] .m2TQuery).withRule .a0Synth := by
        simpa [synthPrimitive, contentEq] using success.symm
      subst result
      have contentTraceSupported : TypingManifestSupported
          (contentResult.trace ++ [.m2TQuery, .a0Synth]) := by
        simpa [mergeResults, TypingResult.withRule] using supported
      simpa only [observation_withRule, observation_mergeResults,
        List.map, judgmentTermList] using
        PrimitiveJudgment.polar environment content contentResult.observation
          (contentSound contentResult contentEq
            (typing_manifest_drop_two contentTraceSupported))

private theorem primitive_openQ_handler {scope : Nat}
    (environment : Environment scope) (property : Term scope)
    (propertySound : SynthSoundMotive scope environment property) :
    PrimitiveSoundMotive scope environment .openQ (.positional property .nil) := by
  intro result success supported
  cases propertyEq : synth environment property with
  | error error => simp [synthPrimitive, propertyEq] at success
  | ok propertyResult =>
      cases typeEq : propertyResult.type with
      | named name arguments => simp [synthPrimitive, propertyEq, typeEq, failure] at success
      | «variable» name => simp [synthPrimitive, propertyEq, typeEq, failure] at success
      | index value => simp [synthPrimitive, propertyEq, typeEq, failure] at success
      | function effectful parameters output =>
          cases parameters with
          | nil => simp [synthPrimitive, propertyEq, typeEq, failure] at success
          | cons answer tail =>
              cases tail with
              | cons second rest =>
                  simp [synthPrimitive, propertyEq, typeEq, failure] at success
              | nil =>
                  cases outputEq : output == Ty.content with
                  | false =>
                      simp [synthPrimitive, propertyEq, typeEq, outputEq,
                        failure] at success
                  | true =>
                      have outputType : output = Ty.content :=
                        Ty.eq_of_beq_true outputEq
                      subst output
                      have resultEq : result =
                          (mergeResults (Ty.query answer) [propertyResult]
                            [] [] .m2TQuery).withRule .a0Synth := by
                        simpa [synthPrimitive, propertyEq, typeEq, outputEq]
                          using success.symm
                      subst result
                      have propertyTraceSupported : TypingManifestSupported
                          (propertyResult.trace ++ [.m2TQuery, .a0Synth]) := by
                        simpa [mergeResults, TypingResult.withRule] using supported
                      simpa only [observation_withRule,
                        observation_mergeResults, List.map,
                        judgmentTermList] using
                        PrimitiveJudgment.openQ environment property
                          propertyResult.observation effectful answer
                          (propertySound propertyResult propertyEq
                            (typing_manifest_drop_two propertyTraceSupported))
                          (by simp [TypingResult.observation, typeEq])

private theorem primitive_ask_handler {scope : Nat}
    (environment : Environment scope) (query : Term scope)
    (querySound : SynthSoundMotive scope environment query) :
    PrimitiveSoundMotive scope environment .ask (.positional query .nil) := by
  intro result success supported
  cases queryEq : synth environment query with
  | error error => simp [synthPrimitive, queryEq] at success
  | ok queryResult =>
      cases answerEq : Ty.asUnary queryResult.type .typeFormQuery with
      | none => simp [synthPrimitive, queryEq, answerEq, failure] at success
      | some answer =>
          have resultEq : result = {
              type := Ty.act Ty.question
              obligations := queryResult.obligations
              trace := queryResult.trace ++ [.m2TQuery, .a0Synth] } := by
            simpa [synthPrimitive, queryEq, answerEq] using success.symm
          subst result
          have queryType : queryResult.observation.type = Ty.query answer := by
            simpa [TypingResult.observation, Ty.query] using asUnary_eq_some answerEq
          exact PrimitiveJudgment.ask environment query queryResult.observation answer
            (querySound queryResult queryEq (typing_manifest_drop_two supported))
            queryType

private theorem primitive_generic_handler {scope : Nat}
    (environment : Environment scope) (mode property nuclear : Term scope)
    (modeSound : CheckSoundMotive scope environment mode Ty.genericMode)
    (propertySound : SynthSoundMotive scope environment property)
    (nuclearSound : ∀ inner,
      CheckSoundMotive scope environment nuclear
        (Ty.effectfulFn [inner] Ty.content)) :
    PrimitiveSoundMotive scope environment .generic
      (.positional mode (.positional property (.positional nuclear .nil))) := by
  intro result success supported
  cases modeEq : check environment mode Ty.genericMode with
  | error error => simp [synthPrimitive, modeEq] at success
  | ok modeResult =>
      cases propertyEq : synth environment property with
      | error error => simp [synthPrimitive, modeEq, propertyEq] at success
      | ok propertyResult =>
          cases functionEq : oneArgumentFunction propertyResult with
          | none =>
              simp [synthPrimitive, modeEq, propertyEq, functionEq,
                failure] at success
          | some functionShape =>
              rcases functionShape with ⟨effectful, inner⟩
              cases effectful with
              | true =>
                  simp [synthPrimitive, modeEq, propertyEq, functionEq,
                    failure] at success
              | false =>
                  cases pureEq : isPure propertyResult with
                  | false =>
                      simp [synthPrimitive, modeEq, propertyEq, functionEq,
                        pureEq, failure] at success
                  | true =>
                      cases nuclearEq : check environment nuclear
                          (Ty.effectfulFn [inner] Ty.content) with
                      | error error =>
                          simp [synthPrimitive, modeEq, propertyEq, functionEq,
                            pureEq, nuclearEq] at success
                      | ok nuclearResult =>
                          have resultEq : result =
                              (mergeResults Ty.content
                                [modeResult, propertyResult, nuclearResult]
                                (if nuclearResult.type ==
                                    Ty.effectfulFn [inner] Ty.content then
                                  [.effectfulCall] else []) []
                                .m2TGeneric).withRule .a0Synth := by
                            simpa [synthPrimitive, modeEq, propertyEq,
                              functionEq, pureEq, nuclearEq] using success.symm
                          subst result
                          have supportedRaw : TypingManifestSupported
                              (modeResult.trace ++ propertyResult.trace ++
                                nuclearResult.trace ++ [.m2TGeneric, .a0Synth]) := by
                            simpa [mergeResults, TypingResult.withRule,
                              List.append_assoc] using supported
                          have modeSupported : TypingManifestSupported modeResult.trace :=
                            typing_manifest_sublist supportedRaw (by
                              intro item member
                              simp [member])
                          have propertySupported :
                              TypingManifestSupported propertyResult.trace :=
                            typing_manifest_sublist supportedRaw (by
                              intro item member
                              simp [member])
                          have nuclearSupported :
                              TypingManifestSupported nuclearResult.trace :=
                            typing_manifest_sublist supportedRaw (by
                              intro item member
                              simp [member])
                          have propertyType : propertyResult.observation.type =
                              Ty.pureFn [inner] Ty.content := by
                            simpa [TypingResult.observation, Ty.pureFn] using
                              oneArgumentFunction_sound functionEq
                          have pure : propertyResult.observation.effects = [] := by
                            exact (purity_classifier_sound_complete propertyResult).mp
                              pureEq
                          change PrimitiveJudgment environment .generic
                            (.positional mode (.positional property
                              (.positional nuclear .nil)))
                            (mergeObservations Ty.content
                              [modeResult.observation, propertyResult.observation,
                                nuclearResult.observation]
                              (if nuclearResult.observation.type ==
                                Ty.effectfulFn [inner] Ty.content then
                                [.effectfulCall] else []))
                          exact PrimitiveJudgment.generic environment mode property
                              nuclear modeResult.observation
                              propertyResult.observation nuclearResult.observation
                              inner (modeSound modeResult modeEq modeSupported)
                              (propertySound propertyResult propertyEq
                                propertySupported) propertyType pure
                              (nuclearSound inner nuclearResult nuclearEq
                                nuclearSupported)

private theorem primitive_locution_handler {scope : Nat}
    (environment : Environment scope) (token locution : Term scope)
    (tokenSound : CheckSoundMotive scope environment token
      (Ty.referents Ty.utteranceToken))
    (locutionSound : CheckSoundMotive scope environment locution
      (Ty.referents Ty.locution)) :
    PrimitiveSoundMotive scope environment .locutionOf
      (.positional token (.positional locution .nil)) := by
  intro result success supported
  cases tokenEq : check environment token (Ty.referents Ty.utteranceToken) with
  | error error => simp [synthPrimitive, tokenEq] at success
  | ok tokenResult =>
      cases locutionEq : check environment locution (Ty.referents Ty.locution) with
      | error error => simp [synthPrimitive, tokenEq, locutionEq] at success
      | ok locutionResult =>
          have resultEq : result =
              (mergeResults Ty.content [tokenResult, locutionResult] [] []
                .m2TLocutionOf).withRule .a0Synth := by
            simpa [synthPrimitive, tokenEq, locutionEq] using success.symm
          subst result
          have supportedRaw : TypingManifestSupported
              (tokenResult.trace ++ locutionResult.trace ++
                [.m2TLocutionOf, .a0Synth]) := by
            simpa [mergeResults, TypingResult.withRule] using supported
          have tokenSupported : TypingManifestSupported tokenResult.trace :=
            typing_manifest_sublist supportedRaw (by
              intro item member
              simp [member])
          have locutionSupported : TypingManifestSupported locutionResult.trace :=
            typing_manifest_sublist supportedRaw (by
              intro item member
              simp [member])
          simpa only [observation_withRule, observation_mergeResults,
            List.map, judgmentTermList] using
            PrimitiveJudgment.locutionOf environment token locution
              tokenResult.observation locutionResult.observation
              (tokenSound tokenResult tokenEq tokenSupported)
              (locutionSound locutionResult locutionEq locutionSupported)

private theorem primitive_holds_handler {scope : Nat}
    (environment : Environment scope) (proposition : Term scope)
    (propositionSound : CheckSoundMotive scope environment proposition Ty.proposition) :
    PrimitiveSoundMotive scope environment .holds
      (.positional proposition .nil) := by
  intro result success supported
  cases propositionEq : check environment proposition Ty.proposition with
  | error error => simp [synthPrimitive, propositionEq] at success
  | ok propositionResult =>
      have resultEq : result =
          (mergeResults Ty.content [propositionResult] [] []
            .m2TContentInterfaces).withRule .a0Synth := by
        simpa [synthPrimitive, propositionEq] using success.symm
      subst result
      have propositionTrace : TypingManifestSupported
          (propositionResult.trace ++ [.m2TContentInterfaces, .a0Synth]) := by
        simpa [mergeResults, TypingResult.withRule] using supported
      simpa only [observation_withRule, observation_mergeResults,
        List.map, judgmentTermList] using
        PrimitiveJudgment.holds environment proposition propositionResult.observation
          (propositionSound propositionResult propositionEq
            (typing_manifest_drop_two propositionTrace))

private theorem primitive_supplement_handler {scope : Nat}
    (environment : Environment scope) (anchor side body : Term scope)
    (anchorSound : SynthSoundMotive scope environment anchor)
    (sideSound : CheckSoundMotive scope environment side Ty.content)
    (bodySound : CheckSoundMotive scope environment body Ty.content) :
    PrimitiveSoundMotive scope environment .supplement
      (.positional anchor (.positional side (.positional body .nil))) := by
  intro result success supported
  cases anchorEq : synth environment anchor with
  | error error => simp [synthPrimitive, anchorEq] at success
  | ok anchorResult =>
      cases sideEq : check environment side Ty.content with
      | error error => simp [synthPrimitive, anchorEq, sideEq] at success
      | ok sideResult =>
          cases bodyEq : check environment body Ty.content with
          | error error => simp [synthPrimitive, anchorEq, sideEq, bodyEq] at success
          | ok bodyResult =>
              have resultEq : result =
                  (mergeResults Ty.content [anchorResult, sideResult, bodyResult]
                    [.projective] [] .m2TContentInterfaces).withRule
                    .a0Synth := by
                simpa [synthPrimitive, anchorEq, sideEq, bodyEq] using
                  success.symm
              subst result
              have supportedRaw : TypingManifestSupported
                  (anchorResult.trace ++ sideResult.trace ++ bodyResult.trace ++
                    [.m2TContentInterfaces, .a0Synth]) := by
                simpa [mergeResults, TypingResult.withRule,
                  List.append_assoc] using supported
              have anchorSupported : TypingManifestSupported anchorResult.trace :=
                typing_manifest_sublist supportedRaw (by
                intro item member
                simp [member])
              have sideSupported : TypingManifestSupported sideResult.trace :=
                typing_manifest_sublist supportedRaw (by
                intro item member
                simp [member])
              have bodySupported : TypingManifestSupported bodyResult.trace :=
                typing_manifest_sublist supportedRaw (by
                intro item member
                simp [member])
              simpa only [observation_withRule, observation_mergeResults,
                List.map, judgmentTermList] using
                PrimitiveJudgment.supplement environment anchor side body
                  anchorResult.observation sideResult.observation
                  bodyResult.observation
                  (anchorSound anchorResult anchorEq anchorSupported)
                  (sideSound sideResult sideEq sideSupported)
                  (bodySound bodyResult bodyEq bodySupported)

private theorem primitive_sentenceSign_handler {scope : Nat}
    (environment : Environment scope) (content : Term scope)
    (contentSound : CheckSoundMotive scope environment content Ty.content) :
    PrimitiveSoundMotive scope environment .sentenceSign
      (.positional content .nil) := by
  intro result success supported
  cases contentEq : check environment content Ty.content with
  | error error => simp [synthPrimitive, contentEq] at success
  | ok contentResult =>
      have resultEq : result = {
          type := Ty.sign "Sentence"
          obligations := contentResult.obligations
          trace := contentResult.trace ++ [.m2TSign, .a0Synth] } := by
        simpa [synthPrimitive, contentEq] using success.symm
      subst result
      exact PrimitiveJudgment.sentenceSign environment content
        contentResult.observation
        (contentSound contentResult contentEq
          (typing_manifest_drop_two supported))

private theorem primitive_reify_handler {scope : Nat}
    (environment : Environment scope) (content : Term scope)
    (contentSound : CheckSoundMotive scope environment content Ty.content) :
    PrimitiveSoundMotive scope environment .reify (.positional content .nil) := by
  intro result success supported
  cases contentEq : check environment content Ty.content with
  | error error => simp [synthPrimitive, contentEq] at success
  | ok contentResult =>
      have resultEq : result = {
          type := Ty.proposition
          obligations := contentResult.obligations
          trace := contentResult.trace ++ [.m2TReify, .a0Synth] } := by
        simpa [synthPrimitive, contentEq] using success.symm
      subst result
      exact PrimitiveJudgment.reify environment content contentResult.observation
        (contentSound contentResult contentEq
          (typing_manifest_drop_two supported))

private theorem primitive_realizedContent_handler {scope : Nat}
    (environment : Environment scope) (token : Term scope)
    (tokenSound : CheckSoundMotive scope environment token
      (Ty.referents Ty.utteranceToken)) :
    PrimitiveSoundMotive scope environment .realizedContent
      (.positional token .nil) := by
  intro result success supported
  cases tokenEq : check environment token (Ty.referents Ty.utteranceToken) with
  | error error => simp [synthPrimitive, tokenEq] at success
  | ok tokenResult =>
      have resultEq : result =
          (mergeResults Ty.content [tokenResult] [.projective]
            [.definedness "RealizedContent" Ty.content] .m2TRealizedContent).withRule
            .a0Synth := by
        simpa [synthPrimitive, tokenEq] using success.symm
      subst result
      have tokenTrace : TypingManifestSupported
          (tokenResult.trace ++ [.m2TRealizedContent, .a0Synth]) := by
        simpa [mergeResults, TypingResult.withRule] using supported
      simpa only [observation_withRule, observation_mergeResults,
        List.map, judgmentTermList] using
        PrimitiveJudgment.realizedContent environment token tokenResult.observation
          (tokenSound tokenResult tokenEq
            (typing_manifest_drop_two tokenTrace))

private theorem primitive_teha_handler {scope : Nat}
    (environment : Environment scope) (base exponent : Term scope)
    (baseSound : CheckSoundMotive scope environment base Ty.number)
    (exponentSound : CheckSoundMotive scope environment exponent Ty.natural) :
    PrimitiveSoundMotive scope environment .teha
      (.positional base (.positional exponent .nil)) := by
  intro result success supported
  cases baseEq : check environment base Ty.number with
  | error error => simp [synthPrimitive, baseEq] at success
  | ok baseResult =>
      cases exponentEq : check environment exponent Ty.natural with
      | error error => simp [synthPrimitive, baseEq, exponentEq] at success
      | ok exponentResult =>
          have resultEq : result =
              (mergeResults Ty.number [baseResult, exponentResult] [] []
                .m2TTeha).withRule .a0Synth := by
            simpa [synthPrimitive, baseEq, exponentEq] using success.symm
          subst result
          have supportedRaw : TypingManifestSupported
              (baseResult.trace ++ exponentResult.trace ++ [.m2TTeha, .a0Synth]) := by
            simpa [mergeResults, TypingResult.withRule] using supported
          have baseSupported : TypingManifestSupported baseResult.trace :=
            typing_manifest_sublist supportedRaw (by
            intro item member
            simp [member])
          have exponentSupported : TypingManifestSupported exponentResult.trace :=
            typing_manifest_sublist supportedRaw (by
            intro item member
            simp [member])
          simpa only [observation_withRule, observation_mergeResults,
            List.map, judgmentTermList] using
            PrimitiveJudgment.teha environment base exponent baseResult.observation
              exponentResult.observation
              (baseSound baseResult baseEq baseSupported)
              (exponentSound exponentResult exponentEq exponentSupported)

private theorem primitive_amountValue_handler {scope : Nat}
    (environment : Environment scope) (arguments : TermList scope)
    (amountSound : ∀ amount, sizeOf amount < sizeOf arguments →
      CheckSoundMotive scope environment amount (Ty.referents Ty.amount))
    (scaleSound : ∀ scale, sizeOf scale < sizeOf arguments →
      CheckSoundMotive scope environment scale (Ty.referents Ty.scale)) :
  PrimitiveSoundMotive scope environment .amountValue arguments := by
  intro result success supported
  cases arguments with
  | nil => simp [synthPrimitive, expectArity, positionalOperands, failure] at success
  | labelled label head tail =>
      simp [synthPrimitive, expectArity, positionalOperands, failure] at success
  | positional amount tail =>
      cases tail with
      | nil => simp [synthPrimitive, expectArity, positionalOperands, failure] at success
      | labelled label head rest =>
          simp [synthPrimitive, expectArity, positionalOperands, failure] at success
      | positional scale rest =>
          cases rest with
          | positional third rest =>
              cases restOperands : positionalOperands rest <;>
                simp [synthPrimitive, expectArity, positionalOperands,
                  restOperands, failure] at success
          | labelled label head rest =>
              simp [synthPrimitive, expectArity, positionalOperands, failure] at success
          | nil =>
              cases amountEq : check environment amount (Ty.referents Ty.amount) with
              | error error =>
                  simp [synthPrimitive, expectArity, positionalOperands,
                    amountEq] at success
              | ok amountResult =>
                  cases scaleEq : check environment scale (Ty.referents Ty.scale) with
                  | error error =>
                      simp [synthPrimitive, expectArity, positionalOperands,
                        amountEq, scaleEq] at success
                  | ok scaleResult =>
                      have resultEq : result =
                          (mergeResults Ty.number [amountResult, scaleResult]
                            [] [] .m2TNumericInterfaces).withRule .a0Synth := by
                        simpa [synthPrimitive, expectArity, positionalOperands,
                          amountEq, scaleEq] using success.symm
                      subst result
                      have supportedRaw : TypingManifestSupported
                          (amountResult.trace ++ scaleResult.trace ++
                            [.m2TNumericInterfaces, .a0Synth]) := by
                        simpa [mergeResults, TypingResult.withRule] using supported
                      have amountSupported : TypingManifestSupported amountResult.trace :=
                        typing_manifest_sublist supportedRaw (by
                          intro item member
                          simp [member])
                      have scaleSupported : TypingManifestSupported scaleResult.trace :=
                        typing_manifest_sublist supportedRaw (by
                          intro item member
                          simp [member])
                      simpa only [observation_withRule, observation_mergeResults,
                        List.map, judgmentTermList] using
                        PrimitiveJudgment.amountValue environment amount scale
                          amountResult.observation scaleResult.observation
                          (amountSound amount (by simp_wf; omega) amountResult
                            amountEq amountSupported)
                          (scaleSound scale (by simp_wf; omega) scaleResult
                            scaleEq scaleSupported)

private theorem primitive_contentRelation_handler {scope : Nat}
    (environment : Environment scope) (operator : FirstOrderPrimitive)
    (arguments : TermList scope)
    (selected : operator = .niRel ∨ operator = .jeiRel ∨ operator = .suhuRel)
    (contentSound : ∀ content, sizeOf content < sizeOf arguments →
      CheckSoundMotive scope environment content Ty.content) :
  PrimitiveSoundMotive scope environment operator arguments := by
  intro result success supported
  cases arguments with
  | nil =>
      rcases selected with rfl | rfl | rfl <;>
        simp [synthPrimitive, expectArity, positionalOperands, failure] at success
  | labelled label head tail =>
      rcases selected with rfl | rfl | rfl <;>
        simp [synthPrimitive, expectArity, positionalOperands, failure] at success
  | positional content tail =>
      cases tail with
      | positional second rest =>
          cases restOperands : positionalOperands rest <;>
            rcases selected with rfl | rfl | rfl <;>
              simp [synthPrimitive, expectArity, positionalOperands,
                restOperands, failure] at success
      | labelled label head rest =>
          rcases selected with rfl | rfl | rfl <;>
            simp [synthPrimitive, expectArity, positionalOperands, failure] at success
      | nil =>
          cases contentEq : check environment content Ty.content with
          | error error =>
              rcases selected with rfl | rfl | rfl <;>
                simp [synthPrimitive, expectArity, positionalOperands,
                  contentEq] at success
          | ok contentResult =>
              have executionEq : synthPrimitive environment operator
                  (.positional content .nil) =
                  .ok ((mergeResults (Ty.predTerm (Ty.arityRow 2))
                    [contentResult] [] [] .m2TNumericInterfaces).withRule
                    .a0Synth) := by
                rcases selected with rfl | rfl | rfl <;>
                  simp [synthPrimitive, expectArity, positionalOperands,
                    contentEq]
              rw [executionEq] at success
              cases success
              have contentTrace : TypingManifestSupported
                  (contentResult.trace ++ [.m2TNumericInterfaces, .a0Synth]) := by
                simpa [mergeResults, TypingResult.withRule] using supported
              simpa only [observation_withRule, observation_mergeResults,
                List.map, judgmentTermList] using
                PrimitiveJudgment.contentRelation environment operator content
                  contentResult.observation selected
                  (contentSound content (by simp_wf; omega) contentResult contentEq
                    (typing_manifest_drop_two contentTrace))

private theorem primitive_dropPlace_handler {scope : Nat}
    (environment : Environment scope) (relation label : Term scope)
    (relationSound : SynthSoundMotive scope environment relation) :
    PrimitiveSoundMotive scope environment .dropPlace
      (.positional relation (.positional label .nil)) := by
  intro result success supported
  cases relationEq : synth environment relation with
  | error error => simp [synthPrimitive, relationEq] at success
  | ok relationResult =>
      cases rowEq : Ty.asUnary relationResult.type .typeFormPredTerm with
      | none => simp [synthPrimitive, relationEq, rowEq, failure] at success
      | some row =>
          have relationType : relationResult.observation.type = Ty.predTerm row := by
            simpa [TypingResult.observation, Ty.predTerm] using asUnary_eq_some rowEq
          cases label with
          | natural value =>
              by_cases positive : value > 0
              · cases shapeEq : rowShape
                    (Ty.rowMinus row (Ty.index value.repr)) with
                | none =>
                    simp [synthPrimitive, relationEq, rowEq, positive,
                      shapeEq, failure] at success
                | some shape =>
                    have resultEq : result =
                        (mergeResults
                          (Ty.predTerm (Ty.rowMinus row (Ty.index value.repr)))
                          [relationResult] [] [] .m2TDropPlace).withRule
                          .a0Synth := by
                      simpa [synthPrimitive, relationEq, rowEq, positive,
                        shapeEq] using success.symm
                    subst result
                    have relationTrace : TypingManifestSupported
                        (relationResult.trace ++ [.m2TDropPlace, .a0Synth]) := by
                      simpa [mergeResults, TypingResult.withRule] using supported
                    simpa only [observation_withRule, observation_mergeResults,
                      List.map, judgmentTermList] using
                      PrimitiveJudgment.dropPlace environment relation
                        (.natural value) relationResult.observation row
                        (Ty.index value.repr)
                        (relationSound relationResult relationEq
                          (typing_manifest_drop_two relationTrace))
                        relationType
                        (Or.inl ⟨value, rfl, positive, rfl⟩)
                        (by simp [shapeEq])
              · simp [synthPrimitive, relationEq, rowEq, positive, failure]
                  at success
          | index literal =>
              by_cases literalEq : literal = "Eventuality"
              · subst literal
                cases shapeEq : rowShape
                    (Ty.rowMinus row (Ty.index "Eventuality")) with
                | none =>
                    simp [synthPrimitive, relationEq, rowEq, shapeEq,
                      failure] at success
                | some shape =>
                    have resultEq : result =
                        (mergeResults
                          (Ty.predTerm (Ty.rowMinus row (Ty.index "Eventuality")))
                          [relationResult] [] [] .m2TDropPlace).withRule
                          .a0Synth := by
                      simpa [synthPrimitive, relationEq, rowEq, shapeEq]
                        using success.symm
                    subst result
                    have relationTrace : TypingManifestSupported
                        (relationResult.trace ++ [.m2TDropPlace, .a0Synth]) := by
                      simpa [mergeResults, TypingResult.withRule] using supported
                    simpa only [observation_withRule, observation_mergeResults,
                      List.map, judgmentTermList] using
                      PrimitiveJudgment.dropPlace environment relation
                        (.index "Eventuality") relationResult.observation row
                        (Ty.index "Eventuality")
                        (relationSound relationResult relationEq
                          (typing_manifest_drop_two relationTrace))
                        relationType (Or.inr ⟨rfl, rfl⟩)
                        (by simp [shapeEq])
              · simp [synthPrimitive, relationEq, rowEq, literalEq, failure]
                  at success
          | bound index => simp [synthPrimitive, relationEq, rowEq, failure] at success
          | free identity => simp [synthPrimitive, relationEq, rowEq, failure] at success
          | string literal => simp [synthPrimitive, relationEq, rowEq, failure] at success
          | lambda binder body => simp [synthPrimitive, relationEq, rowEq, failure] at success
          | bind binder computation body =>
              simp [synthPrimitive, relationEq, rowEq, failure] at success
          | «apply» function arguments =>
              simp [synthPrimitive, relationEq, rowEq, failure] at success
          | lexical predicate arguments =>
              simp [synthPrimitive, relationEq, rowEq, failure] at success
          | context site arguments =>
              simp [synthPrimitive, relationEq, rowEq, failure] at success
          | vague site constraint =>
              simp [synthPrimitive, relationEq, rowEq, failure] at success
          | primitive operator arguments =>
              simp [synthPrimitive, relationEq, rowEq, failure] at success

private theorem primitive_subtract_handler {scope : Nat}
    (environment : Environment scope) (first second : Term scope)
    (firstSound : CheckSoundMotive scope environment first Ty.number)
    (secondSound : CheckSoundMotive scope environment second Ty.number) :
    PrimitiveSoundMotive scope environment .subtract
      (.positional first (.positional second .nil)) := by
  intro result success supported
  cases firstEq : check environment first Ty.number with
  | error error => simp [synthPrimitive, firstEq] at success
  | ok firstResult =>
      cases secondEq : check environment second Ty.number with
      | error error => simp [synthPrimitive, firstEq, secondEq] at success
      | ok secondResult =>
          have resultEq : result =
              (mergeResults Ty.number [firstResult, secondResult] [] []
                .m2TNumericInterfaces).withRule .a0Synth := by
            simpa [synthPrimitive, firstEq, secondEq] using success.symm
          subst result
          have supportedRaw : TypingManifestSupported
              (firstResult.trace ++ secondResult.trace ++
                [.m2TNumericInterfaces, .a0Synth]) := by
            simpa [mergeResults, TypingResult.withRule] using supported
          have firstSupported : TypingManifestSupported firstResult.trace :=
            typing_manifest_sublist supportedRaw (by
              intro item member
              simp [member])
          have secondSupported : TypingManifestSupported secondResult.trace :=
            typing_manifest_sublist supportedRaw (by
              intro item member
              simp [member])
          simpa only [observation_withRule, observation_mergeResults,
            List.map, judgmentTermList] using
            PrimitiveJudgment.binaryCheck environment .subtract first second
              Ty.number Ty.number firstResult.observation secondResult.observation
              (firstSound firstResult firstEq firstSupported)
              (secondSound secondResult secondEq secondSupported)
              .subtract

private theorem primitive_top_handler {scope : Nat}
    (environment : Environment scope) :
    PrimitiveSoundMotive scope environment .and .nil := by
  intro result success _supported
  have resultEq : result = { type := Ty.content, trace := [.a0TTop, .a0Synth] } := by
    simpa [synthPrimitive] using success.symm
  subst result
  exact .top environment

private theorem primitive_and_handler {scope : Nat}
    (environment : Environment scope) (first second : Term scope)
    (firstSound : CheckSoundMotive scope environment first Ty.content)
    (secondSound : CheckSoundMotive scope environment second Ty.content) :
    PrimitiveSoundMotive scope environment .and
      (.positional first (.positional second .nil)) := by
  intro result success supported
  cases firstEq : check environment first Ty.content with
  | error error => simp [synthPrimitive, firstEq] at success
  | ok firstResult =>
      cases secondEq : check environment second Ty.content with
      | error error => simp [synthPrimitive, firstEq, secondEq] at success
      | ok secondResult =>
          have resultEq : result =
              (mergeResults Ty.content [firstResult, secondResult] [] []
                .a0TAnd).withRule .a0Synth := by
            simpa [synthPrimitive, firstEq, secondEq] using success.symm
          subst result
          have supportedRaw : TypingManifestSupported
              (firstResult.trace ++ secondResult.trace ++ [.a0TAnd, .a0Synth]) := by
            simpa [mergeResults, TypingResult.withRule] using supported
          have firstSupported : TypingManifestSupported firstResult.trace :=
            typing_manifest_sublist supportedRaw (by
              intro item member
              simp [member])
          have secondSupported : TypingManifestSupported secondResult.trace :=
            typing_manifest_sublist supportedRaw (by
              intro item member
              simp [member])
          simpa only [observation_withRule, observation_mergeResults,
            List.map, judgmentTermList] using
            PrimitiveJudgment.and environment first second firstResult.observation
              secondResult.observation
              (firstSound firstResult firstEq firstSupported)
              (secondSound secondResult secondEq secondSupported)

private theorem primitive_setOf_handler {scope : Nat}
    (environment : Environment scope) (property : Term scope)
    (propertySound : SynthSoundMotive scope environment property) :
    PrimitiveSoundMotive scope environment .setOf (.positional property .nil) := by
  intro result success supported
  cases propertyEq : synth environment property with
  | error error => simp [synthPrimitive, propertyEq] at success
  | ok propertyResult =>
      cases functionEq : oneArgumentFunction propertyResult with
      | none => simp [synthPrimitive, propertyEq, functionEq, failure] at success
      | some pair =>
          rcases pair with ⟨effectful, inner⟩
          cases effectful with
          | true => simp [synthPrimitive, propertyEq, functionEq, failure] at success
          | false =>
              cases pureEq : isPure propertyResult with
              | false =>
                  simp [synthPrimitive, propertyEq, functionEq, pureEq,
                    failure] at success
              | true =>
                  have resultEq : result =
                      (mergeResults (Ty.set inner) [propertyResult] [] []
                        .a0TSetOf).withRule .a0Synth := by
                    simpa [synthPrimitive, propertyEq, functionEq, pureEq]
                      using success.symm
                  subst result
                  have propertyTrace : TypingManifestSupported
                      (propertyResult.trace ++ [.a0TSetOf, .a0Synth]) := by
                    simpa [mergeResults, TypingResult.withRule] using supported
                  have propertyType : propertyResult.observation.type =
                      Ty.pureFn [inner] Ty.content := by
                    simpa [TypingResult.observation, Ty.pureFn] using
                      oneArgumentFunction_sound functionEq
                  have pure : propertyResult.observation.effects = [] :=
                    (purity_classifier_sound_complete propertyResult).mp pureEq
                  simpa only [observation_withRule, observation_mergeResults,
                    List.map, judgmentTermList] using
                    PrimitiveJudgment.setOf environment property
                      propertyResult.observation inner
                      (propertySound propertyResult propertyEq
                        (typing_manifest_drop_two propertyTrace))
                      propertyType pure

private theorem primitive_card_handler {scope : Nat}
    (environment : Environment scope) (setTerm : Term scope)
    (setSound : SynthSoundMotive scope environment setTerm) :
    PrimitiveSoundMotive scope environment .card (.positional setTerm .nil) := by
  intro result success supported
  cases setEq : synth environment setTerm with
  | error error => simp [synthPrimitive, setEq] at success
  | ok setResult =>
      cases setTypeEq : Ty.asUnary setResult.type .typeFormSet with
      | none => simp [synthPrimitive, setEq, setTypeEq, failure] at success
      | some inner =>
          have resultEq : result =
              (mergeResults Ty.cardinal [setResult] [.projective]
                [.finiteSetCardinalityDefined] .a0TCard).withRule .a0Synth := by
            simpa [synthPrimitive, setEq, setTypeEq] using success.symm
          subst result
          have setTrace : TypingManifestSupported
              (setResult.trace ++ [.a0TCard, .a0Synth]) := by
            simpa [mergeResults, TypingResult.withRule] using supported
          have setType : setResult.observation.type = Ty.set inner := by
            simpa [TypingResult.observation, Ty.set] using asUnary_eq_some setTypeEq
          simpa only [observation_withRule, observation_mergeResults,
            List.map, judgmentTermList] using
            PrimitiveJudgment.card environment setTerm setResult.observation inner
              (setSound setResult setEq (typing_manifest_drop_two setTrace))
              setType

private theorem primitive_stateClause_handler {scope : Nat}
    (environment : Environment scope) (content : Term scope)
    (contentSound : CheckSoundMotive scope environment content Ty.content) :
    PrimitiveSoundMotive scope environment .stateClause
      (.positional content .nil) := by
  intro result success supported
  cases contentEq : check environment content Ty.content with
  | error error => simp [synthPrimitive, contentEq] at success
  | ok contentResult =>
      have resultEq : result =
          (mergeResults Ty.clauseContent [contentResult] [] []
            .a0TStateClause).withRule .a0Synth := by
        simpa [synthPrimitive, contentEq] using success.symm
      subst result
      have contentTrace : TypingManifestSupported
          (contentResult.trace ++ [.a0TStateClause, .a0Synth]) := by
        simpa [mergeResults, TypingResult.withRule] using supported
      simpa only [observation_withRule, observation_mergeResults,
        List.map, judgmentTermList] using
        PrimitiveJudgment.unaryCheck environment .stateClause content Ty.content
          Ty.clauseContent contentResult.observation
          (contentSound contentResult contentEq
            (typing_manifest_drop_two contentTrace)) .stateClause

private theorem primitive_closeClause_handler {scope : Nat}
    (environment : Environment scope) (clause : Term scope)
    (clauseSound : CheckSoundMotive scope environment clause Ty.clauseContent) :
    PrimitiveSoundMotive scope environment .closeClause
      (.positional clause .nil) := by
  intro result success supported
  cases clauseEq : check environment clause Ty.clauseContent with
  | error error => simp [synthPrimitive, clauseEq] at success
  | ok clauseResult =>
      let latentEffect : List Effect := match clauseResult.type with
        | .function true [parameter] output =>
            if parameter == Ty.referents Ty.eventuality && output == Ty.content
            then [.effectfulCall] else []
        | _ => []
      simp [synthPrimitive, clauseEq, latentEffect] at success
      cases success
      have clauseTrace : TypingManifestSupported
          (clauseResult.trace ++ [.a0TCloseClause, .a0Synth]) := by
        simpa [mergeResults, TypingResult.withRule, latentEffect] using supported
      rw [observation_withRule, observation_mergeResults]
      exact PrimitiveJudgment.closeClause environment clause clauseResult.observation
        (clauseSound clauseResult clauseEq
          (typing_manifest_drop_two clauseTrace)) _
        (by simp [TypingResult.observation, latentEffect]; rfl)

private theorem referenceBinary_handler {scope : Nat}
    (environment : Environment scope) (operator : FirstOrderPrimitive)
    (ruleId : M2TypingRuleId) (first second : Term scope)
    (firstSound : SynthSoundMotive scope environment first)
    (secondSound : SynthSoundMotive scope environment second) :
    ReferenceBinarySoundMotive scope environment operator
      (.positional first (.positional second .nil)) ruleId := by
  rintro ⟨rfl, rfl⟩ result success supported
  cases firstEq : synth environment first with
  | error error => simp [synthPrimitive.referenceBinary, firstEq] at success
  | ok firstResult =>
      cases secondEq : synth environment second with
      | error error =>
          simp [synthPrimitive.referenceBinary, firstEq, secondEq] at success
      | ok secondResult =>
          cases compatibleEq : Ty.referenceCompatible firstResult.type
              secondResult.type with
          | false =>
              simp [synthPrimitive.referenceBinary, firstEq, secondEq,
                compatibleEq, failure] at success
          | true =>
              have resultEq : result =
                  (mergeResults Ty.content [firstResult, secondResult] [] []
                    .b1TAmong).withRule .a0Synth := by
                simpa [synthPrimitive.referenceBinary, firstEq, secondEq,
                  compatibleEq] using success.symm
              subst result
              have supportedRaw : TypingManifestSupported
                  (firstResult.trace ++ secondResult.trace ++
                    [.b1TAmong, .a0Synth]) := by
                simpa [mergeResults, TypingResult.withRule] using supported
              have firstSupported : TypingManifestSupported firstResult.trace :=
                typing_manifest_sublist supportedRaw (by
                  intro item member
                  simp [member])
              have secondSupported : TypingManifestSupported secondResult.trace :=
                typing_manifest_sublist supportedRaw (by
                  intro item member
                  simp [member])
              simpa only [observation_withRule, observation_mergeResults,
                List.map, judgmentTermList] using
                PrimitiveJudgment.binarySynth environment .among first second
                  firstResult.observation secondResult.observation Ty.content
                  (firstSound firstResult firstEq firstSupported)
                  (secondSound secondResult secondEq secondSupported)
                  (.among firstResult.observation secondResult.observation
                    compatibleEq)

private theorem quantify_handler {scope : Nat}
    (environment : Environment scope) (operator : FirstOrderPrimitive)
    (ruleId : M2TypingRuleId) (property : Term scope)
    (propertySound : SynthSoundMotive scope environment property) :
    QuantifySoundMotive scope environment operator (.positional property .nil)
      ruleId := by
  intro selected result success supported
  cases propertyEq : synth environment property with
  | error error => simp [synthPrimitive.quantify, propertyEq] at success
  | ok propertyResult =>
      cases typeEq : propertyResult.type with
      | named name arguments =>
          simp [synthPrimitive.quantify, propertyEq, typeEq, failure] at success
      | «variable» name =>
          simp [synthPrimitive.quantify, propertyEq, typeEq, failure] at success
      | index value =>
          simp [synthPrimitive.quantify, propertyEq, typeEq, failure] at success
      | function effectful parameters output =>
          cases outputEq : output == Ty.content with
          | false =>
              simp [synthPrimitive.quantify, propertyEq, typeEq, outputEq,
                failure] at success
          | true =>
              have outputType : output = Ty.content := Ty.eq_of_beq_true outputEq
              subst output
              cases parameters with
              | nil =>
                  simp [synthPrimitive.quantify, propertyEq, typeEq, outputEq,
                    failure] at success
              | cons parameter tail =>
                  cases parameterDomain : Ty.quantifierDomain parameter with
                  | false =>
                      simp [synthPrimitive.quantify, propertyEq, typeEq, outputEq,
                        parameterDomain, failure] at success
                  | true =>
                      cases tailDomains : tail.all Ty.quantifierDomain with
                      | false =>
                          rcases (List.all_eq_false.mp tailDomains) with
                            ⟨bad, member, badDomain⟩
                          have badDomainFalse : Ty.quantifierDomain bad = false := by
                            cases value : Ty.quantifierDomain bad <;> simp_all
                          have badTail : ∃ item, item ∈ tail ∧
                              Ty.quantifierDomain item = false :=
                            ⟨bad, member, badDomainFalse⟩
                          simp [synthPrimitive.quantify, propertyEq, typeEq,
                            outputEq, parameterDomain, badTail, failure] at success
                      | true =>
                       have noBadTail : ¬∃ item, item ∈ tail ∧
                            Ty.quantifierDomain item = false := by
                          intro bad
                          rcases bad with ⟨item, member, itemBad⟩
                          have allGood := List.all_eq_true.mp tailDomains item member
                          rw [itemBad] at allGood
                          contradiction
                       have domainsEq : (parameter :: tail).all
                            Ty.quantifierDomain = true := by
                          simp [parameterDomain, tailDomains]
                       have resultEq : result =
                           (mergeResults Ty.content [propertyResult]
                             (if effectful then [.effectfulCall] else []) []
                             ruleId).withRule .a0Synth := by
                         simpa [synthPrimitive.quantify, propertyEq, typeEq,
                           outputEq, parameterDomain, noBadTail] using success.symm
                       subst result
                       have propertyTrace : TypingManifestSupported
                           (propertyResult.trace ++ [ruleId, .a0Synth]) := by
                         simpa [mergeResults, TypingResult.withRule] using supported
                       simpa only [observation_withRule,
                         observation_mergeResults, List.map,
                         judgmentTermList] using
                         PrimitiveJudgment.quantify environment operator property
                           propertyResult.observation effectful (parameter :: tail)
                           selected
                           (propertySound propertyResult propertyEq
                             (typing_manifest_drop_two propertyTrace))
                           (by simp [TypingResult.observation, typeEq])
                           (by simp) domainsEq

private theorem unaryCheck_handler {scope : Nat}
    (environment : Environment scope) (operator : FirstOrderPrimitive)
    (ruleId : M2TypingRuleId) (term : Term scope) (expected resultType : Ty)
    (termSound : CheckSoundMotive scope environment term expected) :
    UnaryCheckSoundMotive scope environment operator (.positional term .nil)
      ruleId expected resultType := by
  intro schema result success supported
  cases termEq : check environment term expected with
  | error error =>
      simp [synthPrimitive.unaryCheck, termEq] at success
  | ok termResult =>
      have resultEq : result =
          (mergeResults resultType [termResult] [] [] ruleId).withRule
            .a0Synth := by
        simpa [synthPrimitive.unaryCheck, termEq] using success.symm
      subst result
      have termTrace : TypingManifestSupported
          (termResult.trace ++ [ruleId, .a0Synth]) := by
        simpa [mergeResults, TypingResult.withRule] using supported
      simpa only [observation_withRule, observation_mergeResults,
        List.map, judgmentTermList] using
        PrimitiveJudgment.unaryCheck environment operator term expected resultType
          termResult.observation
          (termSound termResult termEq (typing_manifest_drop_two termTrace))
          schema

private theorem binaryCheck_handler {scope : Nat}
    (environment : Environment scope) (operator : FirstOrderPrimitive)
    (ruleId : M2TypingRuleId) (first second : Term scope)
    (expected resultType : Ty)
    (firstSound : CheckSoundMotive scope environment first expected)
    (secondSound : CheckSoundMotive scope environment second expected) :
    BinaryCheckSoundMotive scope environment operator
      (.positional first (.positional second .nil)) ruleId expected resultType := by
  intro schema result success supported
  cases firstEq : check environment first expected with
  | error error => simp [synthPrimitive.binaryCheck, firstEq] at success
  | ok firstResult =>
      cases secondEq : check environment second expected with
      | error error =>
          simp [synthPrimitive.binaryCheck, firstEq, secondEq] at success
      | ok secondResult =>
          have resultEq : result =
              (mergeResults resultType [firstResult, secondResult] [] []
                ruleId).withRule .a0Synth := by
            simpa [synthPrimitive.binaryCheck, firstEq, secondEq] using
              success.symm
          subst result
          have supportedRaw : TypingManifestSupported
              (firstResult.trace ++ secondResult.trace ++ [ruleId, .a0Synth]) := by
            simpa [mergeResults, TypingResult.withRule] using supported
          have firstSupported : TypingManifestSupported firstResult.trace :=
            typing_manifest_sublist supportedRaw (by
              intro item member
              simp [member])
          have secondSupported : TypingManifestSupported secondResult.trace :=
            typing_manifest_sublist supportedRaw (by
              intro item member
              simp [member])
          simpa only [observation_withRule, observation_mergeResults,
            List.map, judgmentTermList] using
            PrimitiveJudgment.binaryCheck environment operator first second
              expected resultType firstResult.observation secondResult.observation
              (firstSound firstResult firstEq firstSupported)
              (secondSound secondResult secondEq secondSupported) schema

private theorem binarySynth_handler {scope : Nat}
    (environment : Environment scope) (operator : FirstOrderPrimitive)
    (ruleId : M2TypingRuleId)
    (resultType : TypingResult → TypingResult → Except TypingError Ty)
    (first second : Term scope)
    (firstSound : SynthSoundMotive scope environment first)
    (secondSound : SynthSoundMotive scope environment second) :
    BinarySynthSoundMotive scope environment operator
      (.positional first (.positional second .nil)) ruleId resultType := by
  intro schema result success supported
  cases firstEq : synth environment first with
  | error error => simp [synthPrimitive.binarySynth, firstEq] at success
  | ok firstResult =>
      cases secondEq : synth environment second with
      | error error =>
          simp [synthPrimitive.binarySynth, firstEq, secondEq] at success
      | ok secondResult =>
          cases typeEq : resultType firstResult secondResult with
          | error error =>
              simp [synthPrimitive.binarySynth, firstEq, secondEq, typeEq]
                at success
          | ok output =>
              have resultEq : result =
                  (mergeResults output [firstResult, secondResult] [] []
                    ruleId).withRule .a0Synth := by
                simpa [synthPrimitive.binarySynth, firstEq, secondEq, typeEq]
                  using success.symm
              subst result
              have supportedRaw : TypingManifestSupported
                  (firstResult.trace ++ secondResult.trace ++ [ruleId, .a0Synth]) := by
                simpa [mergeResults, TypingResult.withRule] using supported
              have firstSupported : TypingManifestSupported firstResult.trace :=
                typing_manifest_sublist supportedRaw (by
                  intro item member
                  simp [member])
              have secondSupported : TypingManifestSupported secondResult.trace :=
                typing_manifest_sublist supportedRaw (by
                  intro item member
                  simp [member])
              simpa only [observation_withRule, observation_mergeResults,
                List.map, judgmentTermList] using
                PrimitiveJudgment.binarySynth environment operator first second
                  firstResult.observation secondResult.observation output
                  (firstSound firstResult firstEq firstSupported)
                  (secondSound secondResult secondEq secondSupported)
                  (schema firstResult secondResult output typeEq)

private theorem jaiRole_excluded_handler {scope : Nat}
    (environment : Environment scope) (relation role : Term scope) :
    JaiRoleSoundMotive scope environment
      (.positional relation (.positional role .nil)) := by
  intro result success supported
  cases relationEq : synth environment relation with
  | error error => simp [synthJaiRoleAdmissible, relationEq] at success
  | ok relationResult =>
      cases predEq : Ty.asUnary relationResult.type .typeFormPredTerm with
      | none =>
          simp [synthJaiRoleAdmissible, relationEq, predEq, failure] at success
      | some row =>
          cases roleEq : synth environment role with
          | error error =>
              simp [synthJaiRoleAdmissible, relationEq, predEq, roleEq]
                at success
          | ok roleResult =>
              cases roleTypeEq : roleResult.type with
              | named name arguments =>
                  simp [synthJaiRoleAdmissible, relationEq, predEq, roleEq,
                    roleTypeEq, failure] at success
              | «variable» name =>
                  simp [synthJaiRoleAdmissible, relationEq, predEq, roleEq,
                    roleTypeEq, failure] at success
              | index value =>
                  simp [synthJaiRoleAdmissible, relationEq, predEq, roleEq,
                    roleTypeEq, failure] at success
              | function effectful parameters output =>
                  cases effectful with
                  | true =>
                      simp [synthJaiRoleAdmissible, relationEq, predEq, roleEq,
                        roleTypeEq, failure] at success
                  | false =>
                      cases parameters with
                      | nil =>
                          simp [synthJaiRoleAdmissible, relationEq, predEq,
                            roleEq, roleTypeEq, failure] at success
                      | cons first tail =>
                          cases tail with
                          | nil =>
                              simp [synthJaiRoleAdmissible, relationEq, predEq,
                                roleEq, roleTypeEq, failure] at success
                          | cons second rest =>
                              cases rest with
                              | cons third more =>
                                  simp [synthJaiRoleAdmissible, relationEq,
                                    predEq, roleEq, roleTypeEq, failure] at success
                              | nil =>
                                  by_cases invalid :
                                      (((output == Ty.content) = false ∨
                                        Ty.asUnary first .typeFormReferents = none) ∨
                                        Ty.asUnary second .typeFormReferents = none) ∨
                                        isPure roleResult = false
                                  · simp [synthJaiRoleAdmissible, relationEq,
                                      predEq, roleEq, roleTypeEq, invalid,
                                      failure] at success
                                  ·
                                      have resultEq : result =
                                          (mergeResults Ty.content
                                            [relationResult, roleResult] [] []
                                            .m2TJaiRoleAdmissible).withRule
                                            .a0Synth := by
                                        simpa [synthJaiRoleAdmissible, relationEq,
                                          predEq, roleEq, roleTypeEq, invalid]
                                          using success.symm
                                      subst result
                                      exact (typing_manifest_excludes
                                        (rule := .m2TJaiRoleAdmissible) supported
                                        (by simp [mergeResults,
                                          TypingResult.withRule]) (by
                                          decide)).elim

private theorem peerUnit_handler {scope : Nat}
    (environment : Environment scope) (basis unit wholeTerm : Term scope)
    (basisSound : SynthSoundMotive scope environment basis)
    (unitSound : ∀ component,
      CheckSoundMotive scope environment unit (Ty.referents component))
    (wholeSound : ∀ whole,
      CheckSoundMotive scope environment wholeTerm (Ty.referents whole)) :
    PeerUnitSoundMotive scope environment
      (.positional basis (.positional unit (.positional wholeTerm .nil))) := by
  intro result success supported
  cases basisEq : synth environment basis with
  | error error => simp [synthPeerUnitAt, basisEq] at success
  | ok basisResult =>
      cases basisTypeEq : Ty.asBinary basisResult.type
          .typeFormDecompositionBasis with
      | none => simp [synthPeerUnitAt, basisEq, basisTypeEq, failure] at success
      | some pair =>
          rcases pair with ⟨whole, component⟩
          cases unitEq : check environment unit (Ty.referents component) with
          | error error =>
              simp [synthPeerUnitAt, basisEq, basisTypeEq, unitEq] at success
          | ok unitResult =>
              cases wholeEq : check environment wholeTerm (Ty.referents whole) with
              | error error =>
                  simp [synthPeerUnitAt, basisEq, basisTypeEq, unitEq,
                    wholeEq] at success
              | ok wholeResult =>
                  have resultEq : result =
                      (mergeResults Ty.content [basisResult, unitResult, wholeResult]
                        [] [] .m2TPeerUnitAt).withRule .a0Synth := by
                    simpa [synthPeerUnitAt, basisEq, basisTypeEq, unitEq,
                      wholeEq] using success.symm
                  subst result
                  have supportedRaw : TypingManifestSupported
                      (basisResult.trace ++ unitResult.trace ++ wholeResult.trace ++
                        [.m2TPeerUnitAt, .a0Synth]) := by
                    simpa [mergeResults, TypingResult.withRule,
                      List.append_assoc] using supported
                  have basisSupported : TypingManifestSupported basisResult.trace :=
                    typing_manifest_sublist supportedRaw (by
                      intro item member
                      simp [member])
                  have unitSupported : TypingManifestSupported unitResult.trace :=
                    typing_manifest_sublist supportedRaw (by
                      intro item member
                      simp [member])
                  have wholeSupported : TypingManifestSupported wholeResult.trace :=
                    typing_manifest_sublist supportedRaw (by
                      intro item member
                      simp [member])
                  have basisType : basisResult.observation.type =
                      Ty.decompositionBasis whole component := by
                    simpa [TypingResult.observation, Ty.decompositionBasis] using
                      asBinary_eq_some basisTypeEq
                  simpa only [observation_withRule, observation_mergeResults,
                    List.map, judgmentTermList] using
                    PrimitiveJudgment.peerUnitAt environment basis unit wholeTerm
                      basisResult.observation unitResult.observation
                      wholeResult.observation whole component
                      (basisSound basisResult basisEq basisSupported) basisType
                      (unitSound component unitResult unitEq unitSupported)
                      (wholeSound whole wholeResult wholeEq wholeSupported)

private theorem basisUnit_handler {scope : Nat}
    (environment : Environment scope) (basis unit cover : Term scope)
    (basisSound : SynthSoundMotive scope environment basis)
    (unitSound : ∀ component,
      CheckSoundMotive scope environment unit (Ty.referents component))
    (coverSound : ∀ component,
      CheckSoundMotive scope environment cover (Ty.referents component)) :
    BasisUnitSoundMotive scope environment
      (.positional basis (.positional unit (.positional cover .nil))) := by
  intro result success supported
  cases basisEq : synth environment basis with
  | error error => simp [synthBasisUnitAt, basisEq] at success
  | ok basisResult =>
      cases basisTypeEq : Ty.asBinary basisResult.type
          .typeFormDecompositionBasis with
      | none => simp [synthBasisUnitAt, basisEq, basisTypeEq, failure] at success
      | some pair =>
          rcases pair with ⟨whole, component⟩
          cases unitEq : check environment unit (Ty.referents component) with
          | error error =>
              simp [synthBasisUnitAt, basisEq, basisTypeEq, unitEq] at success
          | ok unitResult =>
              cases coverEq : check environment cover (Ty.referents component) with
              | error error =>
                  simp [synthBasisUnitAt, basisEq, basisTypeEq, unitEq,
                    coverEq] at success
              | ok coverResult =>
                  have resultEq : result =
                      (mergeResults Ty.content [basisResult, unitResult, coverResult]
                        [] [] .m2TBasisUnitAt).withRule .a0Synth := by
                    simpa [synthBasisUnitAt, basisEq, basisTypeEq, unitEq,
                      coverEq] using success.symm
                  subst result
                  have supportedRaw : TypingManifestSupported
                      (basisResult.trace ++ unitResult.trace ++ coverResult.trace ++
                        [.m2TBasisUnitAt, .a0Synth]) := by
                    simpa [mergeResults, TypingResult.withRule,
                      List.append_assoc] using supported
                  have basisSupported : TypingManifestSupported basisResult.trace :=
                    typing_manifest_sublist supportedRaw (by
                      intro item member
                      simp [member])
                  have unitSupported : TypingManifestSupported unitResult.trace :=
                    typing_manifest_sublist supportedRaw (by
                      intro item member
                      simp [member])
                  have coverSupported : TypingManifestSupported coverResult.trace :=
                    typing_manifest_sublist supportedRaw (by
                      intro item member
                      simp [member])
                  have basisType : basisResult.observation.type =
                      Ty.decompositionBasis whole component := by
                    simpa [TypingResult.observation, Ty.decompositionBasis] using
                      asBinary_eq_some basisTypeEq
                  simpa only [observation_withRule, observation_mergeResults,
                    List.map, judgmentTermList] using
                    PrimitiveJudgment.basisUnitAt environment basis unit cover
                      basisResult.observation unitResult.observation
                      coverResult.observation whole component
                      (basisSound basisResult basisEq basisSupported) basisType
                      (unitSound component unitResult unitEq unitSupported)
                      (coverSound component coverResult coverEq coverSupported)

private theorem aggregate_handler {scope : Nat}
    (environment : Environment scope) (basis group : Term scope)
    (basisSound : SynthSoundMotive scope environment basis)
    (groupSound : ∀ component,
      CheckSoundMotive scope environment group (Ty.group component)) :
    AggregateSoundMotive scope environment
      (.positional basis (.positional group .nil)) := by
  intro result success supported
  cases basisEq : synth environment basis with
  | error error => simp [synthAggregate, basisEq] at success
  | ok basisResult =>
      cases basisTypeEq : Ty.asBinary basisResult.type
          .typeFormDecompositionBasis with
      | none => simp [synthAggregate, basisEq, basisTypeEq, failure] at success
      | some pair =>
          rcases pair with ⟨whole, component⟩
          cases wholeTypeEq : Ty.asUnary whole .typeFormGroup with
          | none =>
              simp [synthAggregate, basisEq, basisTypeEq, wholeTypeEq,
                failure] at success
          | some inner =>
              cases firstCompatible : Ty.compatible inner component with
              | false =>
                  simp [synthAggregate, basisEq, basisTypeEq, wholeTypeEq,
                    firstCompatible, failure] at success
              | true =>
                  cases secondCompatible : Ty.compatible component inner with
                  | false =>
                      simp [synthAggregate, basisEq, basisTypeEq, wholeTypeEq,
                        firstCompatible, secondCompatible, failure] at success
                  | true =>
                      cases groupEq : check environment group (Ty.group component) with
                      | error error =>
                          simp [synthAggregate, basisEq, basisTypeEq, wholeTypeEq,
                            firstCompatible, secondCompatible, groupEq] at success
                      | ok groupResult =>
                          have resultEq : result =
                              (mergeResults Ty.content [basisResult, groupResult]
                                [] [] .m2TAggregate).withRule .a0Synth := by
                            simpa [synthAggregate, basisEq, basisTypeEq,
                              wholeTypeEq, firstCompatible, secondCompatible,
                              groupEq] using success.symm
                          subst result
                          have supportedRaw : TypingManifestSupported
                              (basisResult.trace ++ groupResult.trace ++
                                [.m2TAggregate, .a0Synth]) := by
                            simpa [mergeResults, TypingResult.withRule] using supported
                          have basisSupported :
                              TypingManifestSupported basisResult.trace :=
                            typing_manifest_sublist supportedRaw (by
                              intro item member
                              simp [member])
                          have groupSupported :
                              TypingManifestSupported groupResult.trace :=
                            typing_manifest_sublist supportedRaw (by
                              intro item member
                              simp [member])
                          have basisType : basisResult.observation.type =
                              Ty.decompositionBasis whole component := by
                            simpa [TypingResult.observation,
                              Ty.decompositionBasis] using
                              asBinary_eq_some basisTypeEq
                          have wholeType : whole = Ty.group inner := by
                            simpa [Ty.group] using asUnary_eq_some wholeTypeEq
                          simpa only [observation_withRule,
                            observation_mergeResults, List.map,
                            judgmentTermList] using
                            PrimitiveJudgment.aggregate environment basis group
                              basisResult.observation groupResult.observation
                              whole component inner
                              (basisSound basisResult basisEq basisSupported)
                              basisType wholeType firstCompatible secondCompatible
                              (groupSound component groupResult groupEq
                                groupSupported)

private theorem contentInterface_handler {scope : Nat}
    (environment : Environment scope) (operator : FirstOrderPrimitive)
    (arguments : TermList scope) (arity : Option Nat)
    (argumentsSound : SynthArgumentsSoundMotive scope environment arguments) :
    ContentInterfaceSoundMotive scope environment operator arguments arity := by
  intro schema result success supported
  cases resultsEq : synthPositionalList environment arguments with
  | error error =>
      simp [synthPrimitive.contentInterface, resultsEq] at success
  | ok results =>
      rcases schema with ⟨rfl, rfl⟩ | ⟨selected, rfl⟩
      · by_cases lengthEq : results.length = 2
        · have resultEq : result =
              (mergeResults Ty.content results [] []
                .m2TContentInterfaces).withRule .a0Synth := by
            simpa [synthPrimitive.contentInterface, resultsEq, lengthEq]
              using success.symm
          subst result
          have resultsSupported : TypingResultsManifestSupported results := by
            apply typing_results_manifest_of_flattened
              (suffix := [.m2TContentInterfaces, .a0Synth])
            simpa [mergeResults, TypingResult.withRule] using supported
          simpa only [observation_withRule, observation_mergeResults] using
            PrimitiveJudgment.contentInterface environment .named arguments
              (results.map TypingResult.observation)
              (argumentsSound results resultsEq resultsSupported)
              (Or.inl ⟨rfl, by simpa using lengthEq⟩)
        · simp [synthPrimitive.contentInterface, resultsEq, lengthEq,
            failure] at success
      · by_cases empty : results = []
        · simp [synthPrimitive.contentInterface, resultsEq, empty, failure]
            at success
        · have resultEq : result =
              (mergeResults Ty.content results [] []
                .m2TContentInterfaces).withRule .a0Synth := by
            simpa [synthPrimitive.contentInterface, resultsEq, empty]
              using success.symm
          subst result
          have resultsSupported : TypingResultsManifestSupported results := by
            apply typing_results_manifest_of_flattened
              (suffix := [.m2TContentInterfaces, .a0Synth])
            simpa [mergeResults, TypingResult.withRule] using supported
          simpa only [observation_withRule, observation_mergeResults] using
            PrimitiveJudgment.contentInterface environment operator arguments
              (results.map TypingResult.observation)
              (argumentsSound results resultsEq resultsSupported)
              (Or.inr ⟨selected, by simpa using empty⟩)

private theorem synth_arguments_nil_handler {scope : Nat}
    (environment : Environment scope) :
    SynthArgumentsSoundMotive scope environment .nil := by
  intro results success _supported
  have resultsEq : results = [] := by
    simpa [synthPositionalList] using success.symm
  subst results
  exact .nil environment

private theorem synth_arguments_cons_handler {scope : Nat}
    (environment : Environment scope) (head : Term scope) (tail : TermList scope)
    (headSound : SynthSoundMotive scope environment head)
    (tailSound : SynthArgumentsSoundMotive scope environment tail) :
    SynthArgumentsSoundMotive scope environment (.positional head tail) := by
  intro results success supported
  cases headEq : synth environment head with
  | error error => simp [synthPositionalList, headEq] at success
  | ok headResult =>
      cases tailEq : synthPositionalList environment tail with
      | error error => simp [synthPositionalList, headEq, tailEq] at success
      | ok tailResults =>
          have resultsEq : results = headResult :: tailResults := by
            simpa [synthPositionalList, headEq, tailEq] using success.symm
          subst results
          rcases typing_results_manifest_cons supported with
            ⟨headSupported, tailSupported⟩
          exact SynthArgumentsJudgment.positional environment head tail
            headResult.observation (tailResults.map TypingResult.observation)
            (headSound headResult headEq headSupported)
            (tailSound tailResults tailEq tailSupported)

private theorem lexical_declared_handler {scope : Nat}
    (environment : Environment scope) (predicate : String)
    (arguments : TermList scope) (type : Ty)
    (found : environment.lookupLexical predicate = some type)
    (applySound : ApplySoundMotive scope environment { type } arguments) :
    LexicalSoundMotive scope environment predicate arguments := by
  intro result success supported
  have applyEq : applyFunction environment { type } arguments = .ok result := by
    simpa [synthLexical, found] using success
  rcases applySound result applyEq supported with ⟨_functionSupported, typing⟩
  exact SynthJudgment.lexicalDeclared environment predicate arguments type
    result.observation found typing

private theorem lexical_row_handler {scope : Nat}
    (environment : Environment scope) (predicate : String)
    (arguments : TermList scope)
    (notDeclared : environment.lookupLexical predicate = none)
    (row : M2LexicalRowRecord) (found : lookupLexicalRow predicate = some row)
    (argumentsSound : LexicalArgumentsSoundMotive scope environment row
      arguments []) :
    LexicalSoundMotive scope environment predicate arguments := by
  intro result success supported
  cases argumentsEq : lexicalArgumentResults environment row arguments with
  | error error =>
      simp [synthLexical, notDeclared, found, argumentsEq] at success
  | ok triple =>
      rcases triple with ⟨results, ordinary, eventFilled⟩
      let complete := ordinary == row.ordinaryArity &&
        (row.eventMode == .holdingState || eventFilled)
      have resultEq : result =
          (mergeResults (if complete then Ty.content else lexicalRowType row)
            results [] [] .m2TLexicalRow).withRule .a0Synth := by
        simpa [synthLexical, notDeclared, found, argumentsEq, complete]
          using success.symm
      subst result
      have resultsSupported : TypingResultsManifestSupported results := by
        apply typing_results_manifest_of_flattened
          (suffix := [.m2TLexicalRow, .a0Synth])
        simpa [mergeResults, TypingResult.withRule] using supported
      rcases argumentsSound results ordinary eventFilled argumentsEq
          resultsSupported with ⟨argumentsTyping, within, _seenInvariant⟩
      simpa only [observation_withRule, observation_mergeResults] using
        SynthJudgment.lexicalRow environment predicate arguments row
          (results.map TypingResult.observation) ordinary eventFilled
          notDeclared found argumentsTyping within

private theorem lexical_arguments_nil_handler {scope : Nat}
    (environment : Environment scope) (row : M2LexicalRowRecord)
    (seen : List String) :
    LexicalArgumentsSoundMotive scope environment row .nil seen := by
  intro results ordinary eventFilled success _supported
  have tripleEq : (results, ordinary, eventFilled) = ([], 0, false) := by
    simpa [lexicalArgumentResults] using success.symm
  cases tripleEq
  exact ⟨LexicalArgumentsJudgment.nil environment row seen, by omega,
    fun _member => rfl⟩

private theorem lexical_arguments_positional_handler {scope : Nat}
    (environment : Environment scope) (row : M2LexicalRowRecord)
    (seen : List String) (head : Term scope) (tail : TermList scope)
    (headSound : SynthSoundMotive scope environment head)
    (tailSound : LexicalArgumentsSoundMotive scope environment row tail seen) :
    LexicalArgumentsSoundMotive scope environment row
      (.positional head tail) seen := by
  intro results ordinaryOut eventFilledOut success supported
  cases headEq : synth environment head with
  | error error =>
      simp [lexicalArgumentResults, headEq] at success
  | ok headResult =>
      cases tailEq : lexicalArgumentResults environment row tail seen with
      | error error =>
          simp [lexicalArgumentResults, headEq, tailEq] at success
      | ok triple =>
          rcases triple with ⟨tailResults, ordinary, eventFilled⟩
          have within : ordinary + 1 ≤ row.ordinaryArity := by
            by_cases over : ordinary + 1 > row.ordinaryArity
            · simp [lexicalArgumentResults, headEq, tailEq, over, failure] at success
            · omega
          have notOver : ¬ordinary + 1 > row.ordinaryArity := by omega
          have outputEq : results = headResult :: tailResults ∧
              ordinaryOut = ordinary + 1 ∧ eventFilledOut = eventFilled := by
            simpa [lexicalArgumentResults, headEq, tailEq, notOver]
              using success.symm
          have constructedSupported : TypingResultsManifestSupported
              (headResult :: tailResults) := by
            simpa [outputEq.1] using supported
          rcases typing_results_manifest_cons constructedSupported with
            ⟨headSupported, tailSupported⟩
          rcases tailSound tailResults ordinary eventFilled tailEq tailSupported with
            ⟨tailTyping, _tailWithin, seenInvariant⟩
          have typing := LexicalArgumentsJudgment.positional environment row head
            tail seen headResult.observation
              (tailResults.map TypingResult.observation) ordinary eventFilled
              (headSound headResult headEq headSupported) tailTyping
          exact ⟨by simpa [outputEq.1, outputEq.2.1, outputEq.2.2] using typing,
            by simpa [outputEq.2.1] using within,
            by simpa [outputEq.2.2] using seenInvariant⟩

private theorem lexical_arguments_event_handler {scope : Nat}
    (environment : Environment scope) (row : M2LexicalRowRecord)
    (seen : List String) (head : Term scope) (tail : TermList scope)
    (headSound : CheckSoundMotive scope environment head
      (Ty.referents Ty.eventuality))
    (tailSound : LexicalArgumentsSoundMotive scope environment row tail
      (":Eventuality" :: seen)) :
    LexicalArgumentsSoundMotive scope environment row
      (.labelled ":Eventuality" head tail) seen := by
  intro results ordinaryOut eventFilledOut success supported
  cases fresh : seen.contains ":Eventuality" with
  | true =>
      have member : ":Eventuality" ∈ seen := by simpa using fresh
      simp [lexicalArgumentResults, member, failure] at success
  | false =>
      have notMember : ":Eventuality" ∉ seen := by simpa using fresh
      cases directGuard : row.eventMode != .directEvent with
      | true =>
          simp [lexicalArgumentResults, notMember, directGuard, failure] at success
      | false =>
          have direct : row.eventMode = .directEvent := by
            cases modeEq : row.eventMode with
            | holdingState =>
                have different :
                    (M2LexicalEventMode.holdingState !=
                      M2LexicalEventMode.directEvent) = true := by
                  decide
                rw [modeEq] at directGuard
                rw [different] at directGuard
                contradiction
            | directEvent => rfl
          cases headEq : check environment head (Ty.referents Ty.eventuality) with
          | error error =>
              simp [lexicalArgumentResults, notMember, directGuard, headEq]
                at success
          | ok headResult =>
              cases tailEq : lexicalArgumentResults environment row tail
                  (":Eventuality" :: seen) with
              | error error =>
                  simp [lexicalArgumentResults, notMember, directGuard, headEq,
                    tailEq] at success
              | ok triple =>
                  rcases triple with ⟨tailResults, ordinary, eventFilled⟩
                  have outputEq : results = headResult :: tailResults ∧
                      ordinaryOut = ordinary ∧ eventFilledOut = true := by
                    simpa [lexicalArgumentResults, notMember, directGuard, headEq,
                      tailEq] using success.symm
                  have constructedSupported : TypingResultsManifestSupported
                      (headResult :: tailResults) := by
                    simpa [outputEq.1] using supported
                  rcases typing_results_manifest_cons constructedSupported with
                    ⟨headSupported, tailSupported⟩
                  rcases tailSound tailResults ordinary eventFilled tailEq
                      tailSupported with
                    ⟨tailTyping, tailWithin, tailInvariant⟩
                  have tailEvent : eventFilled = false :=
                    tailInvariant (by simp)
                  have typing := LexicalArgumentsJudgment.event environment row
                    head tail seen fresh direct headResult.observation
                    (tailResults.map TypingResult.observation) ordinary
                    (headSound headResult headEq headSupported)
                    (by simpa [tailEvent] using tailTyping)
                  exact ⟨by simpa [outputEq.1, outputEq.2.1, outputEq.2.2]
                      using typing,
                    by simpa [outputEq.2.1] using tailWithin,
                    fun member => False.elim (notMember member)⟩

private theorem lexical_arguments_labelled_handler {scope : Nat}
    (environment : Environment scope) (row : M2LexicalRowRecord)
    (seen : List String) (label : String) (head : Term scope)
    (tail : TermList scope) (notEvent : label ≠ ":Eventuality")
    (headSound : SynthSoundMotive scope environment head)
    (tailSound : LexicalArgumentsSoundMotive scope environment row tail
      (label :: seen)) :
    LexicalArgumentsSoundMotive scope environment row
      (.labelled label head tail) seen := by
  intro results ordinaryOut eventFilledOut success supported
  cases fresh : seen.contains label with
  | true =>
      have member : label ∈ seen := by simpa using fresh
      simp [lexicalArgumentResults, member, failure] at success
  | false =>
      have notMember : label ∉ seen := by simpa using fresh
      cases decoded : (label.drop 1).toNat? with
      | none =>
          have decodedDirect : (label.drop 1).toNat? = none := by
            simpa using decoded
          simp [lexicalArgumentResults, notMember, notEvent, decodedDirect,
            failure]
            at success
      | some place =>
          have decodedDirect : (label.drop 1).toNat? = some place := by
            simpa using decoded
          by_cases zero : place = 0
          · simp [lexicalArgumentResults, notMember, notEvent, decodedDirect, zero,
              failure] at success
          · by_cases placeOver : place > row.ordinaryArity
            · simp [lexicalArgumentResults, notMember, notEvent,
                decodedDirect, zero, placeOver, failure] at success
            · cases headEq : synth environment head with
              | error error =>
                  simp [lexicalArgumentResults, notMember, notEvent, decodedDirect,
                    zero, placeOver, headEq] at success
              | ok headResult =>
                  cases tailEq : lexicalArgumentResults environment row tail
                      (label :: seen) with
                  | error error =>
                      simp [lexicalArgumentResults, notMember, notEvent,
                        decodedDirect, zero, placeOver, headEq, tailEq] at success
                  | ok triple =>
                      rcases triple with ⟨tailResults, ordinary, eventFilled⟩
                      by_cases ordinaryOver : ordinary + 1 > row.ordinaryArity
                      · simp [lexicalArgumentResults, notMember, notEvent,
                          decodedDirect, zero, placeOver, headEq, tailEq,
                          ordinaryOver, failure] at success
                      · have outputEq :
                            results = headResult :: tailResults ∧
                            ordinaryOut = ordinary + 1 ∧
                            eventFilledOut = eventFilled := by
                          simpa [lexicalArgumentResults, notMember, notEvent,
                            decodedDirect, zero, placeOver, headEq, tailEq,
                            ordinaryOver] using success.symm
                        have constructedSupported :
                            TypingResultsManifestSupported
                              (headResult :: tailResults) := by
                          simpa [outputEq.1] using supported
                        rcases typing_results_manifest_cons constructedSupported
                            with ⟨headSupported, tailSupported⟩
                        rcases tailSound tailResults ordinary eventFilled tailEq
                            tailSupported with
                          ⟨tailTyping, _tailWithin, tailInvariant⟩
                        have typing := LexicalArgumentsJudgment.labelled
                          environment row label head tail seen fresh notEvent place
                          decoded (by omega) (by omega) headResult.observation
                          (tailResults.map TypingResult.observation) ordinary
                          eventFilled (headSound headResult headEq headSupported)
                          tailTyping
                        exact ⟨by
                            simpa [outputEq.1, outputEq.2.1, outputEq.2.2]
                              using typing,
                          by simpa [outputEq.2.1] using
                            (show ordinary + 1 ≤ row.ordinaryArity by omega),
                          by
                            intro eventSeen
                            have tailEvent : eventFilled = false :=
                              tailInvariant (by simp [eventSeen])
                            simpa [outputEq.2.2] using tailEvent⟩

private theorem lexical_arguments_event_selected_handler {scope : Nat}
    (environment : Environment scope) (row : M2LexicalRowRecord)
    (seen : List String) (label : String) (head : Term scope)
    (tail : TermList scope) (selected : (label == ":Eventuality") = true)
    (headSound : CheckSoundMotive scope environment head
      (Ty.referents Ty.eventuality))
    (tailSound : LexicalArgumentsSoundMotive scope environment row tail
      (label :: seen)) :
    LexicalArgumentsSoundMotive scope environment row
      (.labelled label head tail) seen := by
  have labelShape : label = ":Eventuality" := by simpa using selected
  subst label
  exact lexical_arguments_event_handler environment row seen head tail
    headSound tailSound

private theorem lexical_arguments_unknown_label_impossible {scope : Nat}
    (environment : Environment scope) (row : M2LexicalRowRecord)
    (seen : List String) (label : String) (head : Term scope)
    (tail : TermList scope) (fresh : ¬seen.contains label = true)
    (notEvent : ¬(label == ":Eventuality") = true)
    (decoded : (label.drop 1).toNat? = none) :
    LexicalArgumentsSoundMotive scope environment row
      (.labelled label head tail) seen := by
  intro results ordinary eventFilled success _supported
  have notMember : label ∉ seen := by simpa using fresh
  have notEventShape : label ≠ ":Eventuality" := by simpa using notEvent
  simp [lexicalArgumentResults, notMember, notEventShape, decoded, failure]
    at success

private theorem lexical_arguments_outside_label_impossible {scope : Nat}
    (environment : Environment scope) (row : M2LexicalRowRecord)
    (seen : List String) (label : String) (head : Term scope)
    (tail : TermList scope) (fresh : ¬seen.contains label = true)
    (notEvent : ¬(label == ":Eventuality") = true) (place : Nat)
    (decoded : (label.drop 1).toNat? = some place)
    (outside : (place == 0 || decide (place > row.ordinaryArity)) = true) :
    LexicalArgumentsSoundMotive scope environment row
      (.labelled label head tail) seen := by
  intro results ordinary eventFilled success _supported
  have notMember : label ∉ seen := by simpa using fresh
  have notEventShape : label ≠ ":Eventuality" := by simpa using notEvent
  have outsideShape : place = 0 ∨ place > row.ordinaryArity := by
    simpa using outside
  simp [lexicalArgumentResults, notMember, notEventShape, decoded,
    outsideShape, failure] at success

private theorem lexical_arguments_label_selected_handler {scope : Nat}
    (environment : Environment scope) (row : M2LexicalRowRecord)
    (seen : List String) (label : String) (head : Term scope)
    (tail : TermList scope) (notEvent : ¬(label == ":Eventuality") = true)
    (headSound : SynthSoundMotive scope environment head)
    (tailSound : LexicalArgumentsSoundMotive scope environment row tail
      (label :: seen)) :
    LexicalArgumentsSoundMotive scope environment row
      (.labelled label head tail) seen := by
  have notEventShape : label ≠ ":Eventuality" := by simpa using notEvent
  exact lexical_arguments_labelled_handler environment row seen label head tail
    notEventShape headSound tailSound

private theorem pred_arguments_nil_handler {scope : Nat}
    (environment : Environment scope) :
    PredArgumentsSoundMotive scope environment .nil := by
  intro results ordinary eventFilled success _supported
  have outputEq : (results, ordinary, eventFilled) = ([], 0, false) := by
    simpa [predTermArgumentResults] using success.symm
  cases outputEq
  exact PredArgumentsJudgment.nil environment

private theorem pred_arguments_positional_handler {scope : Nat}
    (environment : Environment scope) (head : Term scope)
    (tail : TermList scope)
    (headSound : SynthSoundMotive scope environment head)
    (tailSound : PredArgumentsSoundMotive scope environment tail) :
    PredArgumentsSoundMotive scope environment (.positional head tail) := by
  intro results ordinaryOut eventFilledOut success supported
  cases headEq : synth environment head with
  | error error => simp [predTermArgumentResults, headEq] at success
  | ok headResult =>
      cases tailEq : predTermArgumentResults environment tail with
      | error error =>
          simp [predTermArgumentResults, headEq, tailEq] at success
      | ok triple =>
          rcases triple with ⟨tailResults, ordinary, eventFilled⟩
          have outputEq : results = headResult :: tailResults ∧
              ordinaryOut = ordinary + 1 ∧ eventFilledOut = eventFilled := by
            simpa [predTermArgumentResults, headEq, tailEq] using success.symm
          have constructedSupported : TypingResultsManifestSupported
              (headResult :: tailResults) := by
            simpa [outputEq.1] using supported
          rcases typing_results_manifest_cons constructedSupported with
            ⟨headSupported, tailSupported⟩
          have typing := PredArgumentsJudgment.positional environment head tail
            headResult.observation (tailResults.map TypingResult.observation)
            ordinary eventFilled (headSound headResult headEq headSupported)
            (tailSound tailResults ordinary eventFilled tailEq tailSupported)
          simpa [outputEq.1, outputEq.2.1, outputEq.2.2] using typing

private theorem pred_arguments_event_handler {scope : Nat}
    (environment : Environment scope) (head : Term scope)
    (tail : TermList scope)
    (headSound : CheckSoundMotive scope environment head
      (Ty.referents Ty.eventuality))
    (tailSound : PredArgumentsSoundMotive scope environment tail) :
    PredArgumentsSoundMotive scope environment
      (.labelled ":Eventuality" head tail) := by
  intro results ordinaryOut eventFilledOut success supported
  cases headEq : check environment head (Ty.referents Ty.eventuality) with
  | error error => simp [predTermArgumentResults, headEq] at success
  | ok headResult =>
      cases tailEq : predTermArgumentResults environment tail with
      | error error =>
          simp [predTermArgumentResults, headEq, tailEq] at success
      | ok triple =>
          rcases triple with ⟨tailResults, ordinary, eventFilled⟩
          cases eventFilled with
          | true =>
              simp [predTermArgumentResults, headEq, tailEq, failure] at success
          | false =>
              have outputEq : results = headResult :: tailResults ∧
                  ordinaryOut = ordinary ∧ eventFilledOut = true := by
                simpa [predTermArgumentResults, headEq, tailEq]
                  using success.symm
              have constructedSupported : TypingResultsManifestSupported
                  (headResult :: tailResults) := by
                simpa [outputEq.1] using supported
              rcases typing_results_manifest_cons constructedSupported with
                ⟨headSupported, tailSupported⟩
              have typing := PredArgumentsJudgment.event environment head tail
                headResult.observation
                (tailResults.map TypingResult.observation) ordinary
                (headSound headResult headEq headSupported)
                (tailSound tailResults ordinary false tailEq tailSupported)
              simpa [outputEq.1, outputEq.2.1, outputEq.2.2] using typing

private theorem pred_arguments_labelled_handler {scope : Nat}
    (environment : Environment scope) (label : String) (head : Term scope)
    (tail : TermList scope) (notEvent : label ≠ ":Eventuality")
    (headSound : SynthSoundMotive scope environment head)
    (tailSound : PredArgumentsSoundMotive scope environment tail) :
    PredArgumentsSoundMotive scope environment (.labelled label head tail) := by
  intro results ordinaryOut eventFilledOut success supported
  cases headEq : synth environment head with
  | error error =>
      simp [predTermArgumentResults, notEvent, headEq] at success
  | ok headResult =>
      cases tailEq : predTermArgumentResults environment tail with
      | error error =>
          simp [predTermArgumentResults, notEvent, headEq, tailEq] at success
      | ok triple =>
          rcases triple with ⟨tailResults, ordinary, eventFilled⟩
          have outputEq : results = headResult :: tailResults ∧
              ordinaryOut = ordinary + 1 ∧ eventFilledOut = eventFilled := by
            simpa [predTermArgumentResults, notEvent, headEq, tailEq]
              using success.symm
          have constructedSupported : TypingResultsManifestSupported
              (headResult :: tailResults) := by
            simpa [outputEq.1] using supported
          rcases typing_results_manifest_cons constructedSupported with
            ⟨headSupported, tailSupported⟩
          have typing := PredArgumentsJudgment.labelled environment label notEvent
            head tail headResult.observation
            (tailResults.map TypingResult.observation) ordinary eventFilled
            (headSound headResult headEq headSupported)
            (tailSound tailResults ordinary eventFilled tailEq tailSupported)
          simpa [outputEq.1, outputEq.2.1, outputEq.2.2] using typing

private theorem value_arguments_nil_handler {scope : Nat}
    (environment : Environment scope) :
    ValueArgumentsSoundMotive scope environment .nil := by
  intro results success _supported
  have outputEq : results = [] := by
    simpa [synthValueOperands] using success.symm
  subst results
  exact ValueArgumentsJudgment.nil environment

private theorem value_arguments_positional_handler {scope : Nat}
    (environment : Environment scope) (head : Term scope)
    (tail : TermList scope)
    (headSound : SynthSoundMotive scope environment head)
    (tailSound : ValueArgumentsSoundMotive scope environment tail) :
    ValueArgumentsSoundMotive scope environment (.positional head tail) := by
  intro results success supported
  cases value : isValue head with
  | false => simp [synthValueOperands, value, failure] at success
  | true =>
      cases headEq : synth environment head with
      | error error => simp [synthValueOperands, value, headEq] at success
      | ok headResult =>
          cases tailEq : synthValueOperands environment tail with
          | error error =>
              simp [synthValueOperands, value, headEq, tailEq] at success
          | ok tailResults =>
              have outputEq : results = headResult :: tailResults := by
                simpa [synthValueOperands, value, headEq, tailEq]
                  using success.symm
              have constructedSupported : TypingResultsManifestSupported
                  (headResult :: tailResults) := by
                simpa [outputEq] using supported
              rcases typing_results_manifest_cons constructedSupported with
                ⟨headSupported, tailSupported⟩
              simpa [outputEq] using ValueArgumentsJudgment.positional environment
                head tail headResult.observation
                (tailResults.map TypingResult.observation) value
                (headSound headResult headEq headSupported)
                (tailSound tailResults tailEq tailSupported)

private theorem apply_function_nil_handler {scope : Nat}
    (environment : Environment scope) (functionResult : TypingResult)
    (effectful : Bool) (parameters : List Ty) (output : Ty)
    (functionType : functionResult.type =
      Ty.function effectful parameters output) :
    ApplySoundMotive scope environment functionResult .nil := by
  intro result success supported
  cases parameters with
  | nil =>
      cases effectful with
      | false =>
          have resultEq : result =
              (mergeResults output [functionResult] [] [] .a0TApplyPure).withRule
                .a0Synth := by
            simpa [applyFunction, functionType] using success.symm
          subst result
          have functionSupported : TypingManifestSupported functionResult.trace :=
            typing_manifest_drop_two (by
              simpa [mergeResults, TypingResult.withRule] using supported)
          exact ⟨functionSupported, by
            simpa [observation_withRule, observation_mergeResults] using
              ApplyJudgment.functionZero environment false output
                functionResult.observation functionType⟩
      | true =>
          have resultEq : result =
              (mergeResults output [functionResult] [.effectfulCall] []
                .a0TApplyEffectful).withRule .a0Synth := by
            simpa [applyFunction, functionType] using success.symm
          subst result
          have functionSupported : TypingManifestSupported functionResult.trace :=
            typing_manifest_drop_two (by
              simpa [mergeResults, TypingResult.withRule] using supported)
          exact ⟨functionSupported, by
            simpa [observation_withRule, observation_mergeResults] using
              ApplyJudgment.functionZero environment true output
                functionResult.observation functionType⟩
  | cons parameter remaining =>
      cases effectful with
      | false =>
          have resultEq : result =
              (mergeResults (Ty.function false (parameter :: remaining) output)
                [functionResult] [] [] .a0TApplyPure).withRule .a0Synth := by
            simpa [applyFunction, functionType] using success.symm
          subst result
          have functionSupported : TypingManifestSupported functionResult.trace :=
            typing_manifest_drop_two (by
              simpa [mergeResults, TypingResult.withRule] using supported)
          exact ⟨functionSupported, by
            simpa [observation_withRule, observation_mergeResults] using
              ApplyJudgment.functionPartialZero environment false
                (parameter :: remaining) output (by simp)
                functionResult.observation functionType⟩
      | true =>
          have resultEq : result =
              (mergeResults (Ty.function true (parameter :: remaining) output)
                [functionResult] [.effectfulCall] [] .a0TApplyEffectful).withRule
                  .a0Synth := by
            simpa [applyFunction, functionType] using success.symm
          subst result
          have functionSupported : TypingManifestSupported functionResult.trace :=
            typing_manifest_drop_two (by
              simpa [mergeResults, TypingResult.withRule] using supported)
          exact ⟨functionSupported, by
            simpa [observation_withRule, observation_mergeResults] using
              ApplyJudgment.functionPartialZero environment true
                (parameter :: remaining) output (by simp)
                functionResult.observation functionType⟩

private theorem apply_function_last_handler {scope : Nat}
    (environment : Environment scope) (functionResult : TypingResult)
    (effectful : Bool) (parameter : Ty) (remaining : List Ty) (output : Ty)
    (argument : Term scope)
    (functionType : functionResult.type =
      Ty.function effectful (parameter :: remaining) output)
    (argumentSound : CheckSoundMotive scope environment argument parameter) :
    ApplySoundMotive scope environment functionResult
      (.positional argument .nil) := by
  intro result success supported
  cases argumentEq : check environment argument parameter with
  | error error => simp [applyFunction, functionType, argumentEq] at success
  | ok argumentResult =>
      let outputType := if remaining.isEmpty then output
        else Ty.function effectful remaining output
      let rule : M2TypingRuleId :=
        if effectful then .a0TApplyEffectful else .a0TApplyPure
      let callEffects : List Effect :=
        if effectful then [.effectfulCall] else []
      let applied := (mergeResults outputType [functionResult, argumentResult]
        callEffects [] rule).withRule .a0Synth
      have resultEq : result = applied := by
        simpa [applyFunction, functionType, argumentEq, outputType, rule,
          callEffects, applied] using success.symm
      subst result
      have inputSupported : TypingResultsManifestSupported
          [functionResult, argumentResult] := by
        apply typing_results_manifest_of_flattened
          (suffix := [rule, .a0Synth])
        simpa [applied, mergeResults, TypingResult.withRule] using supported
      rcases typing_results_manifest_cons inputSupported with
        ⟨functionSupported, argumentTailSupported⟩
      rcases typing_results_manifest_cons argumentTailSupported with
        ⟨argumentSupported, _nilSupported⟩
      exact ⟨functionSupported, by
        simpa [applied, outputType, callEffects, observation_withRule,
          observation_mergeResults] using
            ApplyJudgment.functionLast environment effectful parameter remaining
              output functionResult.observation argumentResult.observation
              argument functionType
              (argumentSound argumentResult argumentEq argumentSupported)⟩

private theorem apply_clause_content_handler {scope : Nat}
    (environment : Environment scope) (functionResult : TypingResult)
    (argument : Term scope)
    (functionType : functionResult.type = Ty.clauseContent)
    (argumentSound : CheckSoundMotive scope environment argument
      (Ty.referents Ty.eventuality)) :
    ApplySoundMotive scope environment functionResult
      (.positional argument .nil) := by
  have explicitType : functionResult.type =
      .named .typeClauseContent [] := by
    simpa [Ty.clauseContent, Ty.named0] using functionType
  intro result success supported
  cases argumentEq : check environment argument (Ty.referents Ty.eventuality) with
  | error error =>
      simp [applyFunction, explicitType, argumentEq] at success
  | ok argumentResult =>
      have resultEq : result =
          (mergeResults Ty.content [functionResult, argumentResult] [] []
            .a0TApplyClauseContent).withRule .a0Synth := by
        simpa [applyFunction, explicitType, argumentEq]
          using success.symm
      subst result
      have inputSupported : TypingResultsManifestSupported
          [functionResult, argumentResult] := by
        apply typing_results_manifest_of_flattened
          (suffix := [.a0TApplyClauseContent, .a0Synth])
        simpa [mergeResults, TypingResult.withRule] using supported
      rcases typing_results_manifest_cons inputSupported with
        ⟨functionSupported, argumentTailSupported⟩
      rcases typing_results_manifest_cons argumentTailSupported with
        ⟨argumentSupported, _nilSupported⟩
      exact ⟨functionSupported, by
        simpa [observation_withRule, observation_mergeResults] using
          ApplyJudgment.clauseContent environment functionResult.observation
            argumentResult.observation argument functionType
            (argumentSound argumentResult argumentEq argumentSupported)⟩

private def applyStepResult (functionResult argumentResult : TypingResult)
    (effectful : Bool) (remaining : List Ty) (output : Ty) : TypingResult :=
  let outputType := if remaining.isEmpty then output
    else Ty.function effectful remaining output
  let rule : M2TypingRuleId :=
    if effectful then .a0TApplyEffectful else .a0TApplyPure
  let callEffects : List Effect :=
    if effectful then [.effectfulCall] else []
  (mergeResults outputType [functionResult, argumentResult]
    callEffects [] rule).withRule .a0Synth

private theorem apply_function_more_handler {scope : Nat}
    (environment : Environment scope) (functionResult : TypingResult)
    (effectful : Bool) (parameter : Ty) (remaining : List Ty) (output : Ty)
    (argument : Term scope) (tail : TermList scope) (tailNonempty : tail ≠ .nil)
    (functionType : functionResult.type =
      Ty.function effectful (parameter :: remaining) output)
    (argumentSound : CheckSoundMotive scope environment argument parameter)
    (continuationSound : ∀ argumentResult,
      ApplySoundMotive scope environment
        (applyStepResult functionResult argumentResult effectful remaining output)
        tail) :
    ApplySoundMotive scope environment functionResult
      (.positional argument tail) := by
  intro result success supported
  cases argumentEq : check environment argument parameter with
  | error error =>
      simp [applyFunction, functionType, tailNonempty, argumentEq] at success
  | ok argumentResult =>
      have tailEq : applyFunction environment
          (applyStepResult functionResult argumentResult effectful remaining output)
          tail = .ok result := by
        simpa [applyFunction, functionType, tailNonempty, argumentEq,
          applyStepResult] using success
      rcases continuationSound argumentResult result tailEq supported with
        ⟨stepSupported, tailTyping⟩
      let outputType := if remaining.isEmpty then output
        else Ty.function effectful remaining output
      let rule : M2TypingRuleId :=
        if effectful then .a0TApplyEffectful else .a0TApplyPure
      let callEffects : List Effect :=
        if effectful then [.effectfulCall] else []
      have inputSupported : TypingResultsManifestSupported
          [functionResult, argumentResult] := by
        apply typing_results_manifest_of_flattened
          (suffix := [rule, .a0Synth])
        simpa [applyStepResult, outputType, rule, callEffects, mergeResults,
          TypingResult.withRule] using stepSupported
      rcases typing_results_manifest_cons inputSupported with
        ⟨functionSupported, argumentTailSupported⟩
      rcases typing_results_manifest_cons argumentTailSupported with
        ⟨argumentSupported, _nilSupported⟩
      have intermediateEquation :
          (applyStepResult functionResult argumentResult effectful remaining output).observation =
            mergeObservations outputType
              [functionResult.observation, argumentResult.observation]
              callEffects := by
        simp [applyStepResult, outputType, rule, callEffects,
          observation_withRule, observation_mergeResults]
      exact ⟨functionSupported,
        ApplyJudgment.functionMore environment effectful parameter remaining output
          functionResult.observation argumentResult.observation
          (applyStepResult functionResult argumentResult effectful remaining output).observation
          result.observation argument tail tailNonempty functionType
          (argumentSound argumentResult argumentEq argumentSupported)
          intermediateEquation tailTyping⟩

private theorem apply_function_more_selected_handler {scope : Nat}
    (environment : Environment scope) (functionResult : TypingResult)
    (effectful : Bool) (output : Ty) (argument : Term scope)
    (tail : TermList scope) (tailNonempty : tail ≠ .nil)
    (parameter : Ty) (remaining : List Ty)
    (functionType : functionResult.type =
      Ty.function effectful (parameter :: remaining) output)
    (argumentSound : CheckSoundMotive scope environment argument parameter)
    (continuation : ∀ argumentResult,
      let outputType := if h : remaining.isEmpty = true then output
        else Ty.function effectful remaining output
      let rule : M2TypingRuleId := if h : effectful = true then
        .a0TApplyEffectful else .a0TApplyPure
      let applied := (mergeResults outputType [functionResult, argumentResult]
        (if h : effectful = true then [.effectfulCall] else []) [] rule).withRule
          .a0Synth
      ApplySoundMotive scope environment applied tail) :
    ApplySoundMotive scope environment functionResult
      (.positional argument tail) := by
  apply apply_function_more_handler environment functionResult effectful
    parameter remaining output argument tail tailNonempty functionType
    argumentSound
  intro argumentResult
  simpa [applyStepResult] using continuation argumentResult

private theorem synth_primitive_result_handler {scope : Nat}
    (environment : Environment scope) (operator : FirstOrderPrimitive)
    (arguments : TermList scope)
    (primitiveSound : PrimitiveSoundMotive scope environment operator arguments) :
    SynthSoundMotive scope environment (.primitive operator arguments) := by
  intro result success supported
  have primitiveSuccess : synthPrimitive environment operator arguments =
      .ok result := by
    simpa [synth] using success
  exact SynthJudgment.primitive environment operator arguments
    result.observation (primitiveSound result primitiveSuccess supported)

theorem predTermShape_some {type : Ty} {ordinary : Nat}
    {eventRequired : Bool}
    (shape : predTermShape type = some (ordinary, eventRequired)) :
    ∃ row, type = Ty.predTerm row ∧
      rowShape row = some (ordinary, eventRequired) := by
  cases type with
  | named name arguments =>
      cases name <;> try simp [predTermShape] at shape
      cases arguments with
      | nil => simp [predTermShape] at shape
      | cons row tail =>
          cases tail with
          | nil => exact ⟨row, rfl, shape⟩
          | cons second rest => simp [predTermShape] at shape
  | «variable» _ | index _ | function _ _ _ =>
      simp [predTermShape] at shape

private theorem apply_predterm_handler {scope : Nat}
    (environment : Environment scope) (functionResult : TypingResult)
    (arguments : TermList scope) (ordinary : Nat) (eventRequired : Bool)
    (shape : predTermShape functionResult.type =
      some (ordinary, eventRequired))
    (argumentsSound : PredArgumentsSoundMotive scope environment arguments) :
    ApplySoundMotive scope environment functionResult arguments := by
  intro result success supported
  rcases predTermShape_some shape with ⟨row, functionType, rowShapeEq⟩
  rw [applyFunction.eq_def, functionType] at success
  cases argumentsEq : predTermArgumentResults environment arguments with
  | error error =>
      simp [Ty.predTerm, predTermShape, rowShapeEq, argumentsEq] at success
  | ok triple =>
      rcases triple with ⟨results, ordinaryFilled, eventFilled⟩
      by_cases badRow : ordinaryFilled > ordinary ∨
          (eventFilled = true ∧ eventRequired = false)
      · simp [Ty.predTerm, predTermShape, rowShapeEq, argumentsEq, badRow,
          failure]
          at success
      · let outputType := if ordinaryFilled == ordinary &&
              (!eventRequired || eventFilled) then Ty.content
            else Ty.predTerm <| Ty.residualRow
              (ordinary - ordinaryFilled) (eventRequired && !eventFilled)
        have resultEq : result =
            (mergeResults outputType (functionResult :: results) [] []
              .m2TPredTermApply).withRule .a0Synth := by
          simpa [Ty.predTerm, predTermShape, rowShapeEq, argumentsEq, badRow,
            outputType]
            using success.symm
        subst result
        have inputSupported : TypingResultsManifestSupported
            (functionResult :: results) := by
          apply typing_results_manifest_of_flattened
            (suffix := [.m2TPredTermApply, .a0Synth])
          simpa [outputType, mergeResults, TypingResult.withRule] using supported
        rcases typing_results_manifest_cons inputSupported with
          ⟨functionSupported, resultsSupported⟩
        have argumentsTyping := argumentsSound results ordinaryFilled eventFilled
          argumentsEq resultsSupported
        have within : ordinaryFilled ≤ ordinary := by omega
        have eventWithin : eventFilled = true → eventRequired = true := by
          intro eventPresent
          cases eventRequired <;> simp_all
        have rowCondition : (decide (ordinaryFilled > ordinary) ||
            eventFilled && !eventRequired) = false := by
          cases eventFilled <;> cases eventRequired <;> simp_all
        exact ⟨functionSupported, by
          simpa [outputType, observation_withRule, observation_mergeResults]
            using ApplyJudgment.predTerm environment functionResult.observation
              arguments row ordinary eventRequired
              (results.map TypingResult.observation) ordinaryFilled eventFilled
              functionType rowShapeEq argumentsTyping within eventWithin
              rowCondition badRow⟩

private theorem apply_nonapp_impossible {scope : Nat}
    (environment : Environment scope) (functionResult : TypingResult)
    (arguments : TermList scope)
    (notFunction : ∀ effectful parameters output,
      functionResult.type ≠ Ty.function effectful parameters output)
    (notClause : functionResult.type ≠ Ty.clauseContent)
    (shape : predTermShape functionResult.type = none) :
    ApplySoundMotive scope environment functionResult arguments := by
  intro result success _supported
  have notClauseExplicit : functionResult.type ≠
      .named .typeClauseContent [] := by
    simpa [Ty.clauseContent, Ty.named0] using notClause
  rw [applyFunction.eq_def] at success
  cases typeEq : functionResult.type with
  | named name arguments =>
      rw [typeEq] at success
      cases name <;> simp_all [predTermShape, failure]
  | «variable» name =>
      rw [typeEq] at success
      simp [predTermShape, failure] at success
  | index value =>
      rw [typeEq] at success
      simp [predTermShape, failure] at success
  | function effectful parameters output =>
      exact False.elim (notFunction effectful parameters output typeEq)

private theorem apply_nonapp_selected_impossible {scope : Nat}
    (environment : Environment scope) (functionResult : TypingResult)
    (arguments : TermList scope)
    (notFunction : ∀ effectful parameters output,
      functionResult.type ≠ Ty.function effectful parameters output)
    (notClause : functionResult.type ≠ .named .typeClauseContent [])
    (shape : predTermShape functionResult.type = none) :
    ApplySoundMotive scope environment functionResult arguments := by
  apply apply_nonapp_impossible environment functionResult arguments notFunction
    (by simpa [Ty.clauseContent, Ty.named0] using notClause) shape

private theorem addition_schema (first second : TypingResult) (output : Ty)
    (success : (match Ty.numberJoin first.type second.type with
      | some type => .ok type
      | none => failure "number-type" "addition operands are not compatible numbers") =
      (.ok output : Except TypingError Ty)) :
    BinaryPrimitiveRule .add first.observation second.observation output := by
  cases joined : Ty.numberJoin first.type second.type with
  | none => simp [joined, failure] at success
  | some type =>
      simp [joined] at success
      subst output
      exact .addition first.observation second.observation type joined

private theorem equality_schema (first second : TypingResult) (output : Ty)
    (success : (if Ty.equalityType first.type && Ty.equalityType second.type &&
        (Ty.compatible first.type second.type || Ty.compatible second.type first.type)
      then pure Ty.content
      else failure "equality-type" "equality operands are incompatible") =
      (.ok output : Except TypingError Ty)) :
    BinaryPrimitiveRule .equal first.observation second.observation output := by
  cases guard : (Ty.equalityType first.type && Ty.equalityType second.type &&
      (Ty.compatible first.type second.type ||
        Ty.compatible second.type first.type)) with
  | false => simp [guard, failure] at success
  | true =>
      simp [guard] at success
      subst output
      have parts : Ty.equalityType first.type = true ∧
          Ty.equalityType second.type = true ∧
          (Ty.compatible first.type second.type = true ∨
            Ty.compatible second.type first.type = true) := by
        have raw := (show
          (Ty.equalityType first.type = true ∧
            Ty.equalityType second.type = true) ∧
            (Ty.compatible first.type second.type = true ∨
              Ty.compatible second.type first.type = true) by
          simpa [Bool.and_eq_true, Bool.or_eq_true] using guard)
        exact ⟨raw.1.1, raw.1.2, raw.2⟩
      exact .equality first.observation second.observation parts.1 parts.2.1
        parts.2.2

private theorem sign_sound_handler {scope : Nat}
    (environment : Environment scope) (operator : FirstOrderPrimitive)
    (kind : String) (property : Term scope)
    (checkSound : CheckSoundMotive scope environment property Ty.text) :
    SignSoundMotive scope environment operator
      (.positional property .nil) kind := by
  intro selected result success supported
  cases checkedEq : check environment property Ty.text with
  | error error =>
      simp [synthPrimitive.signConstructor, checkedEq] at success
  | ok checked =>
      have resultEq : result =
          (mergeResults (Ty.sign kind) [checked] [] [] .m2TSign).withRule
            .a0Synth := by
        simpa [synthPrimitive.signConstructor, checkedEq] using success.symm
      subst result
      have checkedSupported : TypingManifestSupported
          (checked.trace ++ [.m2TSign, .a0Synth]) := by
        simpa [mergeResults, TypingResult.withRule] using supported
      exact PrimitiveJudgment.sign environment operator property kind
        checked.observation selected
        (checkSound checked checkedEq
          (typing_manifest_drop_two checkedSupported))

set_option maxHeartbeats 0 in
theorem synth_execution_sound {scope : Nat} (environment : Environment scope)
    (term : Term scope) : SynthSoundMotive scope environment term := by
  -- Lean generates the `caseNNN` labels from the mutual executable control
  -- flow, so they are unstable dispatch points. Semantic reasoning belongs in
  -- the descriptively named handlers above; numbered blocks only route to them.
  apply synth.induct
    (motive1 := SignSoundMotive)
    (motive2 := CheckSoundMotive)
    (motive3 := CheckExpectedSoundMotive)
    (motive4 := CheckArgumentsSoundMotive)
    (motive5 := CheckReferenceSoundMotive)
    (motive6 := CheckPresupposeSoundMotive)
    (motive7 := SynthSoundMotive)
    (motive8 := PrimitiveSoundMotive)
    (motive9 := PerformSoundMotive)
    (motive10 := ThresholdSoundMotive)
    (motive11 := PresupposeSoundMotive)
    (motive12 := ReferenceBinarySoundMotive)
    (motive13 := QuantifySoundMotive)
    (motive14 := UnaryCheckSoundMotive)
    (motive15 := BinaryCheckSoundMotive)
    (motive16 := BinarySynthSoundMotive)
    (motive17 := JaiRoleSoundMotive)
    (motive18 := PeerUnitSoundMotive)
    (motive19 := BasisUnitSoundMotive)
    (motive20 := AggregateSoundMotive)
    (motive21 := ContentInterfaceSoundMotive)
    (motive22 := SynthArgumentsSoundMotive)
    (motive23 := LexicalSoundMotive)
    (motive24 := LexicalArgumentsSoundMotive)
    (motive25 := ApplySoundMotive)
    (motive26 := PredArgumentsSoundMotive)
    (motive27 := ValueArgumentsSoundMotive)
  case case28 =>
    exact fun _ environment expected head tail _headResult _headSuccess
        _tailResults _tailSuccess headSound tailSound =>
      check_arguments_cons_handler environment expected head tail
        headSound tailSound
  case case29 =>
    exact fun _ environment reference expected inner referenceShape count property
        countSound propertySound =>
      selection_check_handler environment .selectExactly reference expected inner
        referenceShape count property (Or.inl rfl) countSound propertySound
  case case31 =>
    exact fun _ environment reference expected inner referenceShape count property
        countSound propertySound =>
      selection_check_handler environment .selectAtLeast reference expected inner
        referenceShape count property (Or.inr (Or.inl rfl))
        countSound propertySound
  case case33 =>
    exact fun _ environment reference expected inner referenceShape count property
        countSound propertySound =>
      selection_check_handler environment .selectAllBut reference expected inner
        referenceShape count property (Or.inr (Or.inr rfl))
        countSound propertySound
  case case37 =>
    exact fun _ environment expected condition body rejected _conditionSound
        _bodySound =>
      presuppose_rejected_handler environment expected condition body rejected
  case case38 =>
    exact fun _ environment expected condition body _accepted conditionSound
        bodySound =>
      presuppose_check_handler environment expected condition body conditionSound
        bodySound
  case case40 =>
    exact fun _ environment index => synth_bound_handler environment index
  case case41 =>
    exact fun _ environment identity type found =>
      synth_free_handler environment identity type found
  case case43 =>
    exact fun _ environment value => synth_natural_handler environment value
  case case44 =>
    exact fun _ environment value => synth_string_handler environment value
  case case46 =>
    exact fun _ environment binderType body bodySound =>
      synth_lambda_handler environment binderType body bodySound
  case case47 =>
    exact fun _ environment binderType computation body bodySound referenceSound
        performanceSound =>
      synth_bind_handler environment binderType computation body bodySound
        referenceSound performanceSound
  case case48 =>
    exact fun _ environment function arguments functionSound applySound =>
      synth_application_handler environment function arguments functionSound
        applySound
  case case52 =>
    exact fun _ environment operator arguments primitiveSound =>
      synth_primitive_result_handler environment operator arguments
        primitiveSound
  case case53 =>
    exact fun _ environment arguments =>
      primitive_constant_handler environment .speaker arguments
        (Ty.referents Ty.entity) .a0TSpeaker .speaker (by simp [synthPrimitive])
  case case54 =>
    exact fun _ environment arguments =>
      primitive_constant_handler environment .audience arguments
        (Ty.referents Ty.entity) .a0TAudience .audience (by simp [synthPrimitive])
  case case55 =>
    exact fun _ environment arguments =>
      primitive_constant_handler environment .tooManyK arguments
        Ty.thresholdKind .a0TThresholdKind .tooManyK (by simp [synthPrimitive])
  case case56 =>
    exact fun _ environment arguments =>
      primitive_constant_handler environment .currentToken arguments
        (Ty.referents Ty.utteranceToken) .m2TCoreConstant .currentToken
        (by simp [synthPrimitive])
  case case57 =>
    exact fun _ environment arguments =>
      primitive_constant_handler environment .host arguments
        Ty.occurrenceRole .m2TContextConstants .host (by simp [synthPrimitive])
  case case58 =>
    exact fun _ environment arguments =>
      primitive_constant_handler environment .attachedDisplay arguments
        Ty.occurrenceRole .m2TContextConstants .attachedDisplay
        (by simp [synthPrimitive])
  case case59 =>
    exact fun _ environment arguments =>
      primitive_constant_handler environment .attachedAddress arguments
        Ty.occurrenceRole .m2TContextConstants .attachedAddress
        (by simp [synthPrimitive])
  case case60 =>
    exact fun _ environment arguments =>
      primitive_constant_handler environment .typical arguments
        Ty.genericMode .m2TContextConstants .typical (by simp [synthPrimitive])
  case case61 =>
    exact fun _ environment arguments =>
      primitive_constant_handler environment .moderate arguments
        Ty.intensity .m2TContextConstants .moderate (by simp [synthPrimitive])
  case case62 =>
    exact fun _ environment arguments =>
      primitive_constant_handler environment .intense arguments
        Ty.intensity .m2TContextConstants .intense (by simp [synthPrimitive])
  case case63 =>
    exact fun _ environment arguments =>
      primitive_constant_handler environment .observation arguments
        Ty.epistemology .m2TContextConstants .observation (by simp [synthPrimitive])
  case case64 =>
    exact fun _ environment arguments =>
      primitive_constant_handler environment .hearsay arguments
        Ty.epistemology .m2TContextConstants .hearsay (by simp [synthPrimitive])
  case case65 =>
    exact fun _ environment arguments =>
      primitive_constant_handler environment .manyK arguments
        Ty.thresholdKind .m2TContextConstants .manyK (by simp [synthPrimitive])
  case case66 =>
    exact fun _ environment arguments =>
      primitive_constant_handler environment .now arguments
        Ty.time .m2TContextConstants .now (by simp [synthPrimitive])
  case case67 =>
    exact fun _ environment arguments =>
      primitive_projective_constant_handler environment .miAOthers arguments
        .miAOthers (by simp [synthPrimitive])
  case case68 =>
    exact fun _ environment arguments =>
      primitive_projective_constant_handler environment .maAOthers arguments
        .maAOthers (by simp [synthPrimitive])
  case case69 =>
    exact fun _ environment arguments =>
      primitive_projective_constant_handler environment .doOOthers arguments
        .doOOthers (by simp [synthPrimitive])
  case case70 =>
    exact fun _ environment first second firstSound secondSound =>
      primitive_combine_handler environment first second firstSound secondSound
  case case72 =>
    exact fun _ environment arguments _recursiveSound =>
      primitive_memberOf_excluded_handler environment arguments
  case case73 =>
    exact fun _ environment content contentSound =>
      primitive_force_handler environment .assert Ty.assertion content
        (Or.inl ⟨rfl, rfl⟩) contentSound
  case case75 =>
    exact fun _ environment content contentSound =>
      primitive_force_handler environment .express Ty.expressive content
        (Or.inr ⟨rfl, rfl⟩) contentSound
  case case77 =>
    exact fun _ environment value valueSound =>
      primitive_mention_handler environment value valueSound
  case case79 =>
    exact fun _ environment arguments argumentsSound =>
      primitive_discourse_handler environment arguments argumentsSound
  case case80 =>
    exact fun _ environment content contentSound =>
      primitive_polar_handler environment content contentSound
  case case82 =>
    exact fun _ environment property propertySound =>
      primitive_openQ_handler environment property propertySound
  case case84 =>
    exact fun _ environment query querySound =>
      primitive_ask_handler environment query querySound
  case case86 =>
    exact fun _ environment mode property nuclear modeSound propertySound
        nuclearSound =>
      primitive_generic_handler environment mode property nuclear modeSound
        propertySound nuclearSound
  case case88 =>
    exact fun _ environment token locution tokenSound locutionSound =>
      primitive_locution_handler environment token locution tokenSound
        locutionSound
  case case99 =>
    exact fun _ environment proposition propositionSound =>
      primitive_holds_handler environment proposition propositionSound
  case case101 =>
    exact fun _ environment anchor side body anchorSound sideSound bodySound =>
      primitive_supplement_handler environment anchor side body anchorSound
        sideSound bodySound
  case case107 =>
    exact fun _ environment content contentSound =>
      primitive_sentenceSign_handler environment content contentSound
  case case109 =>
    exact fun _ environment content contentSound =>
      primitive_reify_handler environment content contentSound
  case case111 =>
    exact fun _ environment token tokenSound =>
      primitive_realizedContent_handler environment token tokenSound
  case case113 =>
    exact fun _ environment relation label relationSound =>
      primitive_dropPlace_handler environment relation label relationSound
  case case115 =>
    exact fun _ environment base exponent baseSound exponentSound =>
      primitive_teha_handler environment base exponent baseSound exponentSound
  case case117 =>
    exact fun _ environment first second firstSound secondSound =>
      primitive_subtract_handler environment first second firstSound secondSound
  case case119 =>
    exact fun _ environment arguments amountSound scaleSound =>
      primitive_amountValue_handler environment arguments amountSound scaleSound
  case case120 =>
    exact fun _ environment arguments contentSound =>
      primitive_contentRelation_handler environment .niRel arguments
        (Or.inl rfl) contentSound
  case case121 =>
    exact fun _ environment arguments contentSound =>
      primitive_contentRelation_handler environment .jeiRel arguments
        (Or.inr (Or.inl rfl)) contentSound
  case case122 =>
    exact fun _ environment arguments contentSound =>
      primitive_contentRelation_handler environment .suhuRel arguments
        (Or.inr (Or.inr rfl)) contentSound
  case case127 =>
    exact fun _ environment arguments binarySound result success supported =>
      binarySound addition_schema result (by
        simpa [synthPrimitive] using success) supported
  case case128 =>
    exact fun _ environment arguments binarySound result success supported =>
      binarySound equality_schema result (by
        simpa [synthPrimitive] using success) supported
  case case129 =>
    exact fun _ environment => primitive_top_handler environment
  case case130 =>
    exact fun _ environment first second firstSound secondSound =>
      primitive_and_handler environment first second firstSound secondSound
  case case132 =>
    exact fun _ environment arguments binarySound result success supported =>
      binarySound .implies result (by
        simpa [synthPrimitive] using success) supported
  case case133 =>
    exact fun _ environment arguments unarySound result success supported =>
      unarySound .not result (by
        simpa [synthPrimitive] using success) supported
  case case138 =>
    exact fun _ environment property propertySound =>
      primitive_setOf_handler environment property propertySound
  case case140 =>
    exact fun _ environment setTerm setSound =>
      primitive_card_handler environment setTerm setSound
  case case143 =>
    exact fun _ environment content contentSound =>
      primitive_stateClause_handler environment content contentSound
  case case145 =>
    exact fun _ environment clause clauseSound =>
      primitive_closeClause_handler environment clause clauseSound
  case case155 =>
    exact fun _ environment act _actSound =>
      synthPerform_excluded_handler environment (.positional act .nil)
  case case156 =>
    exact fun _ environment role act _roleSound _actSound =>
      synthPerform_excluded_handler environment
        (.positional role (.positional act .nil))
  case case158 =>
    exact fun _ environment kind property purpose kindSound propertySound
        purposeSound =>
      threshold_handler environment kind property purpose kindSound
        propertySound purposeSound
  case case160 =>
    exact fun _ environment condition body _conditionSound _bodySound =>
      synthPresuppose_excluded_handler environment condition body
  case case162 =>
    exact fun _ environment operator rule first second firstSound secondSound =>
      referenceBinary_handler environment operator rule first second firstSound
        secondSound
  case case164 =>
    exact fun _ environment operator rule property propertySound =>
      quantify_handler environment operator rule property propertySound
  case case166 =>
    exact fun _ environment operator rule expected resultType term termSound =>
      unaryCheck_handler environment operator rule term expected resultType termSound
  case case168 =>
    exact fun _ environment operator rule expected resultType first second
        firstSound secondSound =>
      binaryCheck_handler environment operator rule first second expected
        resultType firstSound secondSound
  case case170 =>
    exact fun _ environment operator rule resultType first second firstSound
        secondSound =>
      binarySynth_handler environment operator rule resultType first second
        firstSound secondSound
  case case172 =>
    exact fun _ environment relation role _relationSound _roleSound =>
      jaiRole_excluded_handler environment relation role
  case case174 =>
    exact fun _ environment basis unit wholeTerm basisSound unitSound wholeSound =>
      peerUnit_handler environment basis unit wholeTerm basisSound unitSound
        wholeSound
  case case176 =>
    exact fun _ environment basis unit cover basisSound unitSound coverSound =>
      basisUnit_handler environment basis unit cover basisSound unitSound
        coverSound
  case case178 =>
    exact fun _ environment basis group basisSound groupSound =>
      aggregate_handler environment basis group basisSound groupSound
  case case180 =>
    exact fun _ environment operator arguments arity argumentsSound =>
      contentInterface_handler environment operator arguments arity argumentsSound
  case case181 =>
    exact fun _ environment => synth_arguments_nil_handler environment
  case case185 =>
    exact fun _ environment head tail _headResult _headEq _tailResults _tailEq
        headSound tailSound =>
      synth_arguments_cons_handler environment head tail headSound tailSound
  case case186 =>
    exact fun _ environment predicate arguments type found applySound =>
      lexical_declared_handler environment predicate arguments type found
        applySound
  case case188 =>
    exact fun _ environment predicate arguments notDeclared row found
        argumentsSound =>
      lexical_row_handler environment predicate arguments notDeclared row found
        argumentsSound
  case case189 =>
    exact fun _ environment row seen =>
      lexical_arguments_nil_handler environment row seen
  case case193 =>
    exact fun _ environment row seen head tail _headResult _headEq
        _rest _ordinary _eventFilled _tailEq _within headSound tailSound =>
      lexical_arguments_positional_handler environment row seen head tail
        headSound tailSound
  case case197 =>
    exact fun _ environment row seen label head tail _fresh selected
        _directGuard _headResult _headEq _error _tailEq headSound tailSound =>
      lexical_arguments_event_selected_handler environment row seen label head
        tail selected headSound tailSound
  case case198 =>
    exact fun _ environment row seen label head tail _fresh selected
        _directGuard _headResult _headEq _rest _ordinary _eventFilled _tailEq
        headSound tailSound =>
      lexical_arguments_event_selected_handler environment row seen label head
        tail selected headSound tailSound
  case case199 =>
    exact fun _ environment row seen label head tail fresh notEvent decoded =>
      lexical_arguments_unknown_label_impossible environment row seen label
        head tail fresh notEvent decoded
  case case200 =>
    exact fun _ environment row seen label head tail fresh notEvent place
        decoded outside =>
      lexical_arguments_outside_label_impossible environment row seen label
        head tail fresh notEvent place decoded outside
  case case202 =>
    exact fun _ environment row seen label head tail _fresh notEvent
        _place _decoded _within _headResult _headEq _error _tailEq headSound
        tailSound =>
      lexical_arguments_label_selected_handler environment row seen label head
        tail notEvent headSound tailSound
  case case203 =>
    exact fun _ environment row seen label head tail _fresh notEvent
        _place _decoded _within _headResult _headEq _rest _ordinary
        _eventFilled _tailEq _over headSound tailSound =>
      lexical_arguments_label_selected_handler environment row seen label head
        tail notEvent headSound tailSound
  case case204 =>
    exact fun _ environment row seen label head tail _fresh notEvent
        _place _decoded _within _headResult _headEq _rest _ordinary
        _eventFilled _tailEq _notOver headSound tailSound =>
      lexical_arguments_label_selected_handler environment row seen label head
        tail notEvent headSound tailSound
  case case206 =>
    exact fun _ environment functionResult effectful parameters output
        functionType _empty =>
      apply_function_nil_handler environment functionResult effectful parameters
        output functionType
  case case207 =>
    exact fun _ environment functionResult effectful parameters output
        functionType _nonempty =>
      apply_function_nil_handler environment functionResult effectful parameters
        output functionType
  case case209 =>
    exact fun _ environment functionResult effectful output argument parameter
        remaining functionType argumentSound =>
      apply_function_last_handler environment functionResult effectful parameter
        remaining output argument functionType argumentSound
  case case211 =>
    exact fun _ environment functionResult effectful output argument tail
        tailNonempty parameter remaining functionType argumentSound continuation =>
      apply_function_more_selected_handler environment functionResult effectful
        output argument tail tailNonempty parameter remaining functionType
        argumentSound continuation
  case case212 =>
    exact fun _ environment functionResult functionType argument argumentSound =>
      apply_clause_content_handler environment functionResult argument
        functionType argumentSound
  case case214 =>
    exact fun _ environment functionResult arguments ordinary eventRequired
        _notFunction _notClause shape argumentsSound =>
      apply_predterm_handler environment functionResult arguments ordinary
        eventRequired shape argumentsSound
  case case215 =>
    exact fun _ environment functionResult arguments notFunction notClause
        shape =>
      apply_nonapp_selected_impossible environment functionResult arguments
        notFunction notClause shape
  case case216 =>
    exact fun _ environment => pred_arguments_nil_handler environment
  case case219 =>
    exact fun _ environment head tail _headResult _headEq _rest _ordinary
        _eventFilled _tailEq headSound tailSound =>
      pred_arguments_positional_handler environment head tail headSound tailSound
  case case221 =>
    exact fun _ environment head tail _headResult _headEq _error _tailEq
        headSound tailSound =>
      pred_arguments_event_handler environment head tail headSound tailSound
  case case222 =>
    exact fun _ environment head tail _headResult _headEq _rest _ordinary
        _tailEq headSound tailSound =>
      pred_arguments_event_handler environment head tail headSound tailSound
  case case223 =>
    exact fun _ environment head tail _headResult _headEq _rest _ordinary
        _eventFilled _tailEq _notFilled headSound tailSound =>
      pred_arguments_event_handler environment head tail headSound tailSound
  case case226 =>
    exact fun _ environment label head tail notEvent _headResult _headEq _rest
        _ordinary _eventFilled _tailEq headSound tailSound =>
      pred_arguments_labelled_handler environment label head tail notEvent
        headSound tailSound
  case case227 =>
    exact fun _ environment => value_arguments_nil_handler environment
  case case232 =>
    exact fun _ environment head tail _value _headResult _headEq _tailResults
        _tailEq headSound tailSound =>
      value_arguments_positional_handler environment head tail headSound tailSound
  -- The remaining generated goals are control-flow failure subdivisions and
  -- definitional adapters around the named mechanism handlers. Normalize them
  -- only after every successful recursive/application branch is dispatched.
  all_goals try solve_by_elim [sign_sound_handler, check_success_handler,
    context_check_handler, context_impossible_handler, vague_check_handler,
    vague_impossible_handler, local_check_handler]
  all_goals try solve_by_elim [refer_check_handler]
  all_goals try solve_by_elim [refer_impossible_handler,
    presuppose_impossible_handler, local_impossible_handler]
  all_goals try solve_by_elim [reference_primitive_impossible_handler,
    list_check_handler, list_impossible_handler, no_expected_clause_handler,
    check_arguments_nil_handler, selection_check_handler]
  all_goals try solve_by_elim [reference_primitive_checkExpected_handler]
  all_goals try solve_by_elim [check_arguments_cons_handler]
  all_goals try solve_by_elim [presuppose_check_handler,
    presuppose_checkExpected_handler, lexical_arguments_event_handler,
    lexical_arguments_labelled_handler, pred_arguments_event_handler]
  all_goals try solve_by_elim [synth_bound_handler, synth_free_handler,
    synth_natural_handler, synth_string_handler, synth_lambda_handler,
    synth_bind_handler, synth_application_handler]
  all_goals
    intros
    simp_all [SignSoundMotive, CheckSoundMotive, CheckExpectedSoundMotive,
      CheckArgumentsSoundMotive, CheckReferenceSoundMotive,
      CheckPresupposeSoundMotive, SynthSoundMotive, PrimitiveSoundMotive,
      PerformSoundMotive, ThresholdSoundMotive, PresupposeSoundMotive,
      ReferenceBinarySoundMotive, QuantifySoundMotive, UnaryCheckSoundMotive,
      BinaryCheckSoundMotive, BinarySynthSoundMotive, JaiRoleSoundMotive,
      PeerUnitSoundMotive, BasisUnitSoundMotive, AggregateSoundMotive,
      ContentInterfaceSoundMotive, SynthArgumentsSoundMotive,
      LexicalSoundMotive, LexicalArgumentsSoundMotive, ApplySoundMotive,
      PredArgumentsSoundMotive, ValueArgumentsSoundMotive,
      synth, check, checkExpected, checkPositionalList, checkReferencePrimitive,
      checkPresupposeReference, synthPrimitive, synthPerform,
      synthPrimitive.constant, synthPrimitive.signConstructor,
      synthPrimitive.contentInterface, synthPrimitive.binarySynth,
      synthPrimitive.binaryCheck, synthPrimitive.unaryCheck,
      synthPrimitive.quantify, synthPrimitive.referenceBinary,
      synthAdmissibleThreshold, synthPresuppose, synthJaiRoleAdmissible,
      synthPeerUnitAt, synthBasisUnitAt, synthAggregate, synthPositionalList,
      synthLexical, lexicalArgumentResults, applyFunction,
      predTermArgumentResults, synthValueOperands, judgmentTermList,
      mergeResults, mergeObservations, TypingResult.observation,
      TypingResult.withRule, failure]
    try intros
    repeat' split at * <;>
    (try intros) <;>
    (try simp_all [expectedCheckClause, expectedOnlySynthesisForm,
        positionalTerms, positionalOperands, expectArity,
        oneArgumentFunction, isPure, computationCategoryClassifier,
        mergeResults, mergeObservations, TypingResult.observation,
        TypingResult.withRule, failure]) <;>
    (try subst_vars) <;>
    (try simp_all [TypingResult.observation, mergeObservations]) <;>
    try solve_by_elim [check_from_synth_manifest] <;>
    try solve_by_elim [synth_primitive_manifest] <;>
    try solve_by_elim [
      TypingManifestSupported.mk, TypingResultsManifestSupported.mk,
      typing_manifest_prefix, typing_manifest_prefix_witness,
      typing_manifest_middle_prefix, typing_manifest_drop_one,
      typing_manifest_drop_two, typing_manifest_keep_first_two,
      check_from_synth_manifest, expected_context_term_shape,
      expected_context_shape_contradiction,
      CheckJudgment.fromSynth, CheckJudgment.context, CheckJudgment.vague,
      CheckJudgment.referReference, CheckJudgment.referMember,
      CheckJudgment.local, CheckJudgment.presupposeReference,
      CheckJudgment.list, CheckJudgment.select] <;>
    try solve_by_elim [
      TypingManifestSupported.mk, TypingResultsManifestSupported.mk,
      typing_manifest_prefix, typing_manifest_prefix_witness,
      typing_manifest_middle_prefix, typing_manifest_drop_one,
      typing_manifest_drop_two, typing_manifest_keep_first_two,
      synth_primitive_manifest,
      SynthJudgment.bound, SynthJudgment.free, SynthJudgment.natural,
      SynthJudgment.string, SynthJudgment.lambda, SynthJudgment.bindReference,
      SynthJudgment.application, SynthJudgment.lexicalDeclared,
      SynthJudgment.lexicalRow, SynthJudgment.primitive] <;>
    try solve_by_elim [
      TypingManifestSupported.mk, TypingResultsManifestSupported.mk,
      typing_manifest_prefix, typing_manifest_prefix_witness,
      typing_manifest_middle_prefix, typing_manifest_drop_one,
      typing_manifest_drop_two, typing_manifest_keep_first_two,
      ApplyJudgment.functionZero, ApplyJudgment.functionPartialZero,
      ApplyJudgment.functionLast, ApplyJudgment.functionMore,
      ApplyJudgment.clauseContent, ApplyJudgment.predTerm] <;>
    try solve_by_elim [
      TypingManifestSupported.mk, TypingResultsManifestSupported.mk,
      typing_manifest_prefix, typing_manifest_prefix_witness,
      typing_manifest_middle_prefix, typing_manifest_drop_one,
      typing_manifest_drop_two, typing_manifest_keep_first_two,
      SynthArgumentsJudgment.nil, SynthArgumentsJudgment.positional,
      CheckArgumentsJudgment.nil, CheckArgumentsJudgment.positional,
      ValueArgumentsJudgment.nil, ValueArgumentsJudgment.positional,
      PredArgumentsJudgment.nil, PredArgumentsJudgment.positional,
      PredArgumentsJudgment.event, PredArgumentsJudgment.labelled,
      LexicalArgumentsJudgment.nil, LexicalArgumentsJudgment.positional,
      LexicalArgumentsJudgment.event, LexicalArgumentsJudgment.labelled] <;>
    try solve_by_elim [
      constant_rule_manifest, TypingManifestSupported.mk,
      TypingResultsManifestSupported.mk, typing_manifest_prefix,
      typing_manifest_prefix_witness, typing_manifest_middle_prefix,
      typing_manifest_drop_one, typing_manifest_drop_two,
      typing_manifest_keep_first_two,
      typing_results_manifest_of_flattened,
      PrimitiveJudgment.constant, PrimitiveJudgment.binarySynth,
      PrimitiveJudgment.unaryCheck, PrimitiveJudgment.binaryCheck,
      PrimitiveJudgment.top, PrimitiveJudgment.and, PrimitiveJudgment.quantify,
      PrimitiveJudgment.setOf, PrimitiveJudgment.card,
      PrimitiveJudgment.admissibleThreshold, PrimitiveJudgment.closeClause,
      PrimitiveJudgment.aggregate, PrimitiveJudgment.basisUnitAt,
      PrimitiveJudgment.peerUnitAt, PrimitiveJudgment.forceContent,
      PrimitiveJudgment.mention, PrimitiveJudgment.discourse,
      PrimitiveJudgment.combine, PrimitiveJudgment.locutionOf,
      PrimitiveJudgment.sign, PrimitiveJudgment.sentenceSign,
      PrimitiveJudgment.reify, PrimitiveJudgment.realizedContent,
      PrimitiveJudgment.teha, PrimitiveJudgment.polar,
      PrimitiveJudgment.openQ, PrimitiveJudgment.ask,
      PrimitiveJudgment.generic, PrimitiveJudgment.contentInterface,
      PrimitiveJudgment.holds, PrimitiveJudgment.supplement,
      PrimitiveJudgment.dropPlace,
      ConstantPrimitiveRule.speaker, ConstantPrimitiveRule.audience,
      ConstantPrimitiveRule.tooManyK, ConstantPrimitiveRule.currentToken,
      ConstantPrimitiveRule.host, ConstantPrimitiveRule.attachedDisplay,
      ConstantPrimitiveRule.attachedAddress, ConstantPrimitiveRule.typical,
      ConstantPrimitiveRule.moderate, ConstantPrimitiveRule.intense,
      ConstantPrimitiveRule.observation, ConstantPrimitiveRule.hearsay,
      ConstantPrimitiveRule.manyK, ConstantPrimitiveRule.now,
      ConstantPrimitiveRule.miAOthers, ConstantPrimitiveRule.maAOthers,
      ConstantPrimitiveRule.doOOthers,
      BinaryPrimitiveRule.addition, BinaryPrimitiveRule.equality,
      BinaryPrimitiveRule.among, UnaryCheckedPrimitiveRule.not,
      UnaryCheckedPrimitiveRule.stateClause,
      BinaryCheckedPrimitiveRule.implies, BinaryCheckedPrimitiveRule.subtract]

theorem synth_success_sound {scope : Nat} {environment : Environment scope}
    {term : Term scope} {result : TypingResult}
    (success : synth environment term = .ok result)
    (manifest : result.trace.all typingRuleImplemented = true) :
    SynthJudgment environment term result.observation :=
  synth_execution_sound environment term result success ⟨manifest⟩

theorem synth_success_sound_on_manifest {scope : Nat}
    {environment : Environment scope} {term : Term scope}
    {result : TypingResult}
    (success : synth environment term = .ok result)
    (manifest : TypingManifestSupported result.trace) :
    SynthJudgment environment term result.observation :=
  synth_execution_sound environment term result success manifest

end M2
end SmusniPilot
