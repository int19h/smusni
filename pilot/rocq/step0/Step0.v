From Stdlib Require Import List Arith Bool String Program.Equality ZArith.
From QuickChick Require Import QuickChick.

(* QuickChick 2.2.0's bundled extraction maps [mkRandomSeed : Z -> _]
   directly to [Random.init : int -> _].  Preserve the public Coq API while
   making the fixed replay seed executable. *)
Extract Constant mkRandomSeed =>
  "(fun x -> Random.init (Big_int_Z.int_of_big_int x); Random.get_state())".

Import ListNotations.
Open Scope string_scope.

Set Warnings "-deprecated-dirpath-Coq,-deprecated-since-9.0,-non-recursive".

(* A bounded type universe closed over the selected A0 rules. *)
Inductive purity : Type := Pure | Effectful.

Inductive ty : Type :=
| TEntity
| TNatural
| TNumber
| TContent
| TRef (member : ty)
| TRefComp (result : ty)
| TArrow (class : purity) (argument result : ty).

Inductive effect : Type :=
| EContext
| ERefer
| EEffectfulCall.

(* No selected rule originates an obligation.  The opaque atom preserves the
   correlated live record field without inventing an origin rule. *)
Inductive obligation : Type :=
| OpaqueObligation (identity : nat).

Record typing_record : Type := MkTyping {
  result_type : ty;
  result_effects : list effect;
  result_obligations : list obligation
}.

(* Context's recursive spine represents an arbitrary argument list while
   keeping the datatype regular enough for Rocq/QuickChick derivation. *)
Inductive term : Type :=
| TVar (lookup_index : nat)
| TNat (literal : nat)
| TTop
| TLam (binder_type : ty) (body_term : term)
| TContextNil
| TContextCons (context_argument context_rest : term)
| TSelectExactly (count_term property_term : term)
| TSelectSome (property_term : term)
| TBind (annotation : ty) (computation_term body_term : term)
| TApply (function_term argument_term : term)
| TEquality (first_term second_term : term).

Inductive direction : Type :=
| Synth
| Check (expected : ty).

Inductive rule_id : Type :=
| R_A0_Synth
| R_A0_Check
| R_Natural
| R_Top
| R_Variable
| R_LambdaPure
| R_LambdaEffectful
| R_CheckSynth
| R_Context
| R_SelectExactly
| R_SelectSome
| R_BindReference
| R_ApplyPure
| R_ApplyEffectful
| R_Equality.

Definition env := list ty.
Definition trace := list rule_id.

Scheme Equality for purity.
Scheme Equality for ty.
Scheme Equality for effect.
Scheme Equality for obligation.
Scheme Equality for term.
Scheme Equality for direction.
Scheme Equality for rule_id.

QCDerive (Show, Arbitrary, Shrink, EnumSized) for purity.
QCDerive (Show, Arbitrary, Shrink, EnumSized) for ty.
QCDerive (Show, Arbitrary, Shrink, EnumSized) for effect.
QCDerive (Show, Arbitrary, Shrink, EnumSized) for obligation.
QCDerive (Show, Arbitrary, Shrink, EnumSized) for term.
QCDerive (Show, Arbitrary, Shrink) for direction.
QCDerive (Show, Arbitrary, Shrink, EnumSized) for rule_id.

Definition show_typing_record_impl (record : typing_record) : string :=
  "MkTyping(" ++ show (result_type record) ++ "," ++
  show (result_effects record) ++ "," ++
  show (result_obligations record) ++ ")".

#[global] Instance show_typing_record : Show typing_record :=
  {| show := show_typing_record_impl |}.

QCDerive EnumSized for typing_record.

#[global] Instance dec_purity (first second : purity) : Dec (first = second).
Proof. constructor. exact (purity_eq_dec first second). Defined.

#[global] Instance dec_ty (first second : ty) : Dec (first = second).
Proof. constructor. exact (ty_eq_dec first second). Defined.

#[global] Instance dec_effect (first second : effect) : Dec (first = second).
Proof. constructor. exact (effect_eq_dec first second). Defined.

#[global] Instance dec_obligation
    (first second : obligation) : Dec (first = second).
Proof. constructor. exact (obligation_eq_dec first second). Defined.

Definition typing_record_eq_dec
    (first second : typing_record) : {first = second} + {first <> second}.
Proof.
  decide equality.
  - apply list_eq_dec. exact obligation_eq_dec.
  - apply list_eq_dec. exact effect_eq_dec.
  - apply ty_eq_dec.
Defined.

#[global] Instance dec_typing_record
    (first second : typing_record) : Dec (first = second).
Proof. constructor. exact (typing_record_eq_dec first second). Defined.

#[global] Instance dec_rule_id
    (first second : rule_id) : Dec (first = second).
Proof. constructor. exact (rule_id_eq_dec first second). Defined.

#[global] Instance dec_term (first second : term) : Dec (first = second).
Proof. constructor. exact (term_eq_dec first second). Defined.

Fixpoint ty_eqb (first second : ty) : bool :=
  match first, second with
  | TEntity, TEntity
  | TNatural, TNatural
  | TNumber, TNumber
  | TContent, TContent => true
  | TRef first_inner, TRef second_inner
  | TRefComp first_inner, TRefComp second_inner =>
      ty_eqb first_inner second_inner
  | TArrow first_class first_argument first_result,
    TArrow second_class second_argument second_result =>
      match first_class, second_class with
      | Pure, Pure | Effectful, Effectful =>
          ty_eqb first_argument second_argument &&
          ty_eqb first_result second_result
      | _, _ => false
      end
  | _, _ => false
  end.

Fixpoint compatible_fuel (fuel : nat) (actual expected : ty) : bool :=
  match fuel with
  | 0 => false
  | S remaining =>
      ty_eqb actual expected ||
      match actual, expected with
      | TNatural, TNumber => true
      | TArrow Pure actual_argument actual_result,
        TArrow Effectful expected_argument expected_result =>
          compatible_fuel remaining expected_argument actual_argument &&
          compatible_fuel remaining actual_result expected_result
      | _, _ => false
      end
  end.

Definition compatible (actual expected : ty) : bool :=
  compatible_fuel 64 actual expected.

Definition equality_type (candidate : ty) : bool :=
  match candidate with
  | TEntity | TNatural | TNumber => true
  | _ => false
  end.

Definition effect_equal (first second : effect) : bool :=
  if effect_eq_dec first second then true else false.

Definition obligation_equal (first second : obligation) : bool :=
  if obligation_eq_dec first second then true else false.

Definition effect_rank (candidate : effect) : nat :=
  match candidate with
  | EContext => 0
  | EEffectfulCall => 1
  | ERefer => 2
  end.

Fixpoint add_effect (candidate : effect)
    (values : list effect) : list effect :=
  match values with
  | [] => [candidate]
  | existing :: rest =>
      if effect_equal candidate existing then values
      else if Nat.ltb (effect_rank candidate) (effect_rank existing)
        then candidate :: values
        else existing :: add_effect candidate rest
  end.

Fixpoint union_effects (first second : list effect) : list effect :=
  match second with
  | [] => first
  | candidate :: rest => union_effects (add_effect candidate first) rest
  end.

Definition add_obligation (candidate : obligation)
    (values : list obligation) : list obligation :=
  if existsb (fun existing => obligation_equal candidate existing) values
  then values else values ++ [candidate].

Fixpoint union_obligations
    (first second : list obligation) : list obligation :=
  match second with
  | [] => first
  | candidate :: rest =>
      union_obligations (add_obligation candidate first) rest
  end.

Definition merge_two (output : ty) (first second : typing_record)
    (extra : list effect) : typing_record :=
  MkTyping output
    (union_effects extra
      (union_effects (result_effects first) (result_effects second)))
    (union_obligations
      (result_obligations first) (result_obligations second)).

Inductive env_lookup : env -> nat -> ty -> Prop :=
| LookupNow : forall G lookup_type,
    env_lookup (lookup_type :: G) 0 lookup_type
| LookupLater : forall G lookup_index lookup_type skipped_type,
    env_lookup G lookup_index lookup_type ->
    env_lookup (skipped_type :: G) (S lookup_index) lookup_type.

QCDerive ArbitrarySizedSuchThat for
  (fun lookup_index => env_lookup G lookup_index lookup_type).
QCDerive EnumSizedSuchThat for
  (fun lookup_type => env_lookup G lookup_index lookup_type).
QCDerive DecOpt for (env_lookup G lookup_index lookup_type).

Record typed_case : Type := MkTypedCase {
  case_term : term;
  case_record : typing_record;
  case_trace : trace
}.

Definition show_typed_case_impl (generated : typed_case) : string :=
  "TypedCase(" ++ show (case_term generated) ++ "," ++
  show (case_record generated) ++ "," ++ show (case_trace generated) ++ ")".

#[global] Instance show_typed_case : Show typed_case :=
  {| show := show_typed_case_impl |}.

Definition shrink_typed_case_impl (generated : typed_case) : list typed_case :=
  map
    (fun smaller_term =>
      MkTypedCase smaller_term (case_record generated) (case_trace generated))
    (shrink (case_term generated)).

#[global] Instance shrink_typed_case : Shrink typed_case :=
  {| shrink := shrink_typed_case_impl |}.

Definition typed_case_eq_dec
    (first second : typed_case) : {first = second} + {first <> second}.
Proof.
  decide equality.
  - apply list_eq_dec. exact rule_id_eq_dec.
  - apply typing_record_eq_dec.
  - apply term_eq_dec.
Defined.

#[global] Instance dec_typed_case
    (first second : typed_case) : Dec (first = second).
Proof. constructor. exact (typed_case_eq_dec first second). Defined.

Definition strip_context_trace (context_trace : trace) : trace :=
  match context_trace with
  | R_Context :: rest => rest
  | rest => rest
  end.

Fixpoint context_spine (candidate : term) : bool :=
  match candidate with
  | TContextNil => true
  | TContextCons _ context_rest => context_spine context_rest
  | _ => false
  end.

Definition provably_positive (candidate : term) : bool :=
  match candidate with
  | TNat literal => Nat.ltb 0 literal
  | _ => false
  end.

Definition record_effects_empty (record : typing_record) : bool :=
  match result_effects record with
  | [] => true
  | _ => false
  end.

Definition record_effects_nonempty (record : typing_record) : bool :=
  negb (record_effects_empty record).

(* The actual two-mode, record-valued relation.  All generated fields are in
   the one packed output; no rule-specific generator exists beside it. *)
Inductive a0_type : env -> direction -> typed_case -> Prop :=
| A0_T_Natural : forall G literal,
    a0_type G Synth
      (MkTypedCase (TNat literal) (MkTyping TNatural [] []) [R_Natural])
| A0_T_Top : forall G,
    a0_type G Synth
      (MkTypedCase TTop (MkTyping TContent [] []) [R_Top])
| A0_T_Variable : forall G lookup_index lookup_type,
    env_lookup G lookup_index lookup_type ->
    a0_type G Synth
      (MkTypedCase (TVar lookup_index)
        (MkTyping lookup_type [] []) [R_Variable])
| A0_T_Lambda_Pure :
    forall G binder_type body_term body_record body_trace,
    a0_type (binder_type :: G) Synth
      (MkTypedCase body_term body_record body_trace) ->
    record_effects_empty body_record = true ->
    a0_type G Synth
      (MkTypedCase (TLam binder_type body_term)
        (MkTyping (TArrow Pure binder_type (result_type body_record)) []
          (result_obligations body_record))
        (R_LambdaPure :: body_trace))
| A0_T_Lambda_Effectful :
    forall G binder_type body_term body_record body_trace,
    a0_type (binder_type :: G) Synth
      (MkTypedCase body_term body_record body_trace) ->
    record_effects_nonempty body_record = true ->
    a0_type G Synth
      (MkTypedCase (TLam binder_type body_term)
        (MkTyping (TArrow Effectful binder_type (result_type body_record)) []
          (result_obligations body_record))
        (R_LambdaEffectful :: body_trace))
| A0_T_Check_Synth :
    forall G expected actual_term actual_record actual_trace,
    a0_type G Synth
      (MkTypedCase actual_term actual_record actual_trace) ->
    compatible (result_type actual_record) expected = true ->
    a0_type G (Check expected)
      (MkTypedCase actual_term actual_record
        (R_CheckSynth :: actual_trace))
| A0_T_Context_Nil : forall G expected,
    a0_type G (Check (TRefComp expected))
      (MkTypedCase TContextNil
        (MkTyping (TRefComp expected) [EContext] []) [R_Context])
| A0_T_Context_Cons :
    forall G expected context_argument argument_record argument_trace
      context_rest rest_record rest_trace,
    a0_type G Synth
      (MkTypedCase context_argument argument_record argument_trace) ->
    a0_type G (Check (TRefComp expected))
      (MkTypedCase context_rest rest_record rest_trace) ->
    context_spine context_rest = true ->
    a0_type G (Check (TRefComp expected))
      (MkTypedCase (TContextCons context_argument context_rest)
        (merge_two (TRefComp expected) argument_record rest_record [EContext])
        (R_Context :: argument_trace ++ strip_context_trace rest_trace))
| A0_T_Select_Exactly :
    forall G member count_term count_record count_trace property_term
      property_obligations property_trace,
    a0_type G (Check TNatural)
      (MkTypedCase count_term count_record count_trace) ->
    provably_positive count_term = true ->
    a0_type G Synth
      (MkTypedCase property_term
        (MkTyping (TArrow Pure member TContent) [] property_obligations)
        property_trace) ->
    a0_type G (Check (TRefComp (TRef member)))
      (MkTypedCase (TSelectExactly count_term property_term)
        (merge_two (TRefComp (TRef member)) count_record
          (MkTyping (TArrow Pure member TContent) [] property_obligations)
          [ERefer])
        (R_SelectExactly :: count_trace ++ property_trace))
| A0_T_Select_Some :
    forall G member property_term property_obligations property_trace,
    a0_type G Synth
      (MkTypedCase property_term
        (MkTyping (TArrow Pure member TContent) [] property_obligations)
        property_trace) ->
    a0_type G (Check (TRefComp (TRef member)))
      (MkTypedCase (TSelectSome property_term)
        (MkTyping (TRefComp (TRef member)) [ERefer] property_obligations)
        (R_SelectSome :: property_trace))
| A0_T_Bind_Reference :
    forall G annotation computation_term computation_record computation_trace
      body_term body_record body_trace,
    a0_type G (Check (TRefComp annotation))
      (MkTypedCase computation_term computation_record computation_trace) ->
    a0_type (annotation :: G) Synth
      (MkTypedCase body_term body_record body_trace) ->
    a0_type G Synth
      (MkTypedCase (TBind annotation computation_term body_term)
        (merge_two (result_type body_record)
          computation_record body_record [])
        (R_BindReference :: computation_trace ++ body_trace))
| A0_T_Apply_Pure :
    forall G argument_type output_type function_term function_record
      function_trace argument_term argument_record argument_trace,
    a0_type G Synth
      (MkTypedCase function_term function_record function_trace) ->
    result_type function_record = TArrow Pure argument_type output_type ->
    a0_type G (Check argument_type)
      (MkTypedCase argument_term argument_record argument_trace) ->
    a0_type G Synth
      (MkTypedCase (TApply function_term argument_term)
        (merge_two output_type function_record argument_record [])
        (R_ApplyPure :: function_trace ++ argument_trace))
| A0_T_Apply_Effectful :
    forall G argument_type output_type function_term function_record
      function_trace argument_term argument_record argument_trace,
    a0_type G Synth
      (MkTypedCase function_term function_record function_trace) ->
    result_type function_record =
      TArrow Effectful argument_type output_type ->
    a0_type G (Check argument_type)
      (MkTypedCase argument_term argument_record argument_trace) ->
    a0_type G Synth
      (MkTypedCase (TApply function_term argument_term)
        (merge_two output_type function_record argument_record
          [EEffectfulCall])
        (R_ApplyEffectful :: function_trace ++ argument_trace))
| A0_T_Equality :
    forall G first_term first_record first_trace
      second_term second_record second_trace,
    a0_type G Synth
      (MkTypedCase first_term first_record first_trace) ->
    a0_type G Synth
      (MkTypedCase second_term second_record second_trace) ->
    equality_type (result_type first_record) = true ->
    equality_type (result_type second_record) = true ->
    (compatible (result_type first_record) (result_type second_record) ||
     compatible (result_type second_record) (result_type first_record)) = true ->
    a0_type G Synth
      (MkTypedCase (TEquality first_term second_term)
        (merge_two TContent first_record second_record [])
        (R_Equality :: first_trace ++ second_trace)).

QCDerive ArbitrarySizedSuchThat for
  (fun generated => a0_type G mode generated).
QCDerive DecOpt for (a0_type G mode generated).

Inductive synth_query (G : env) : typed_case -> Prop :=
| A0_Synth : forall generated,
    a0_type G Synth generated ->
    synth_query G generated.

Inductive check_query (G : env) (expected : ty) : typed_case -> Prop :=
| A0_Check : forall generated,
    a0_type G (Check expected) generated ->
    check_query G expected generated.

QCDerive ArbitrarySizedSuchThat for
  (fun generated => synth_query G generated).
QCDerive ArbitrarySizedSuchThat for
  (fun generated => check_query G expected generated).
QCDerive DecOpt for (synth_query G generated).
QCDerive DecOpt for (check_query G expected generated).

Fixpoint rule_bit (rule : rule_id) : nat :=
  match rule with
  | R_A0_Synth => 1
  | R_A0_Check => 2
  | R_Natural => 4
  | R_Top => 8
  | R_Variable => 16
  | R_LambdaPure => 32
  | R_LambdaEffectful => 64
  | R_CheckSynth => 128
  | R_Context => 256
  | R_SelectExactly => 512
  | R_SelectSome => 1024
  | R_BindReference => 2048
  | R_ApplyPure => 4096
  | R_ApplyEffectful => 8192
  | R_Equality => 16384
  end.

Fixpoint trace_mask (rules : trace) : nat :=
  match rules with
  | [] => 0
  | rule :: rest => Nat.lor (rule_bit rule) (trace_mask rest)
  end.

Fixpoint term_depth (candidate : term) : nat :=
  match candidate with
  | TVar _ | TNat _ | TTop | TContextNil => 0
  | TLam _ body_term => S (term_depth body_term)
  | TContextCons context_argument context_rest =>
      Nat.max (term_depth context_argument) (term_depth context_rest)
  | TSelectExactly count_term property_term =>
      Nat.max (term_depth count_term) (term_depth property_term)
  | TSelectSome property_term => term_depth property_term
  | TBind _ computation_term body_term =>
      Nat.max (term_depth computation_term) (S (term_depth body_term))
  | TApply function_term argument_term
  | TEquality function_term argument_term =>
      Nat.max (term_depth function_term) (term_depth argument_term)
  end.

Fixpoint well_scoped (depth : nat) (candidate : term) : bool :=
  match candidate with
  | TVar lookup_index => Nat.ltb lookup_index depth
  | TNat _ | TTop | TContextNil => true
  | TLam _ body_term => well_scoped (S depth) body_term
  | TContextCons context_argument context_rest =>
      well_scoped depth context_argument &&
      well_scoped depth context_rest
  | TSelectExactly count_term property_term =>
      well_scoped depth count_term && well_scoped depth property_term
  | TSelectSome property_term => well_scoped depth property_term
  | TBind _ computation_term body_term =>
      well_scoped depth computation_term &&
      well_scoped (S depth) body_term
  | TApply function_term argument_term
  | TEquality function_term argument_term =>
      well_scoped depth function_term &&
      well_scoped depth argument_term
  end.

Definition dec_true {P : Prop} `{DecOpt P} (fuel : nat) : bool :=
  match @decOpt P _ fuel with
  | Some true => true
  | _ => false
  end.

Definition synth_generated_with_fuel (fuel : nat) : Checker :=
  forAllMaybe (genST (fun generated => synth_query [] generated))
    (fun generated =>
       collect
         (trace_mask (R_A0_Synth :: case_trace generated),
          term_depth (case_term generated))
         (checker (dec_true (P := synth_query [] generated) fuel))).

Definition synth_generated : Checker := synth_generated_with_fuel 120.

Definition check_generated : Checker :=
  forAll arbitrary (fun expected =>
    forAllMaybe (genST (fun generated => check_query [] expected generated))
      (fun generated =>
         collect
           (trace_mask (R_A0_Check :: case_trace generated),
            term_depth (case_term generated))
           (checker
             (dec_true (P := check_query [] expected generated) 120)))).

(* Diagnostic-only producer measurements.  These deliberately do not claim
   validation: the full producer-plus-derived-checker path is [synth_generated]
   and [check_generated] above. *)
Definition synth_generation_only : Checker :=
  forAllMaybe (genST (fun generated => synth_query [] generated))
    (fun generated =>
       collect
         (trace_mask (R_A0_Synth :: case_trace generated),
          term_depth (case_term generated))
         (checker true)).

Definition check_generation_only : Checker :=
  forAll arbitrary (fun expected =>
    forAllMaybe (genST (fun generated => check_query [] expected generated))
      (fun generated =>
         collect
           (trace_mask (R_A0_Check :: case_trace generated),
            term_depth (case_term generated))
           (checker true))).

Definition synth_scope_preserving_shrinks : Checker :=
  forAllMaybe (genST (fun generated => synth_query [] generated))
    (fun generated =>
       checker (forallb
         (fun shrunk => well_scoped 0 (case_term shrunk))
         (shrink generated))).

Definition synth_derivation_preserving_shrinks : Checker :=
  forAllMaybe (genST (fun generated => synth_query [] generated))
    (fun generated =>
       checker (forallb
         (fun shrunk => dec_true (P := synth_query [] shrunk) 120)
         (shrink generated))).

Definition check_scope_preserving_shrinks : Checker :=
  forAll arbitrary (fun expected =>
    forAllMaybe (genST (fun generated => check_query [] expected generated))
      (fun generated =>
         checker (forallb
           (fun shrunk => well_scoped 0 (case_term shrunk))
           (shrink generated)))).

Definition check_derivation_preserving_shrinks : Checker :=
  forAll arbitrary (fun expected =>
    forAllMaybe (genST (fun generated => check_query [] expected generated))
      (fun generated =>
         checker (forallb
           (fun shrunk =>
             dec_true (P := check_query [] expected shrunk) 120)
           (shrink generated)))).

Definition measured_args (successes discards max_size : nat) : Args :=
  match stdArgs with
  | MkArgs _ _ _ max_shrinks _ chatty analysis =>
      MkArgs (Some (mkRandomSeed (740019%Z), 0))
        successes discards max_shrinks max_size chatty analysis
  end.

Definition step0_args := measured_args 20000 100000 7.
Definition shrink_args := measured_args 2000 20000 7.
Definition fuel_probe_args := measured_args 300 3000 7.

Example positive_context_two_arguments :
  exists result_record result_trace,
    a0_type [] (Check (TRefComp TEntity))
      (MkTypedCase
        (TContextCons TTop (TContextCons (TNat 1) TContextNil))
        result_record result_trace).
Proof.
  eexists. eexists.
  eapply A0_T_Context_Cons.
  - apply A0_T_Top.
  - eapply A0_T_Context_Cons.
    + apply A0_T_Natural.
    + apply A0_T_Context_Nil.
    + reflexivity.
  - reflexivity.
Qed.

Example positive_selection_under_bind :
  exists result_record result_trace,
    a0_type [] Synth
      (MkTypedCase
        (TBind (TRef TEntity)
          (TSelectExactly (TNat 2) (TLam TEntity TTop))
          (TVar 0))
        result_record result_trace).
Proof.
  eexists. eexists.
  eapply A0_T_Bind_Reference.
  - eapply A0_T_Select_Exactly with
      (count_record := MkTyping TNatural [] [])
      (count_trace := [R_CheckSynth; R_Natural])
      (property_obligations := [])
      (property_trace := [R_LambdaPure; R_Top]).
    + eapply A0_T_Check_Synth.
      * apply A0_T_Natural.
      * reflexivity.
    + reflexivity.
    + eapply A0_T_Lambda_Pure with
        (body_record := MkTyping TContent [] [])
        (body_trace := [R_Top]).
      * apply A0_T_Top.
      * reflexivity.
  - eapply A0_T_Variable.
    apply LookupNow.
Qed.

Example canonical_mixed_effect_record :
  merge_two TContent
    (MkTyping (TRefComp (TRef TEntity)) [ERefer] [])
    (MkTyping TContent [EContext] []) [] =
  MkTyping TContent [EContext; ERefer] [].
Proof. reflexivity. Qed.

Example positive_refer_before_context_is_canonical :
  exists result_trace,
    a0_type [] Synth
      (MkTypedCase
        (TBind (TRef TEntity)
          (TSelectSome (TLam TEntity TTop))
          (TBind TContent TContextNil TTop))
        (MkTyping TContent [EContext; ERefer] [])
        result_trace).
Proof.
  rewrite <- canonical_mixed_effect_record.
  eexists.
  eapply A0_T_Bind_Reference with
    (computation_record :=
      MkTyping (TRefComp (TRef TEntity)) [ERefer] [])
    (body_record := MkTyping TContent [EContext] []).
  - eapply A0_T_Select_Some with
      (property_obligations := [])
      (property_trace := [R_LambdaPure; R_Top]).
    eapply A0_T_Lambda_Pure with
      (body_record := MkTyping TContent [] [])
      (body_trace := [R_Top]).
    + apply A0_T_Top.
    + reflexivity.
  - eapply A0_T_Bind_Reference with
      (computation_record := MkTyping (TRefComp TContent) [EContext] [])
      (body_record := MkTyping TContent [] []).
    + apply A0_T_Context_Nil.
    + apply A0_T_Top.
Qed.

Lemma plural_self_equality_body_negative :
  ~ a0_type [TRef TEntity] Synth
      (MkTypedCase (TEquality (TVar 0) (TVar 0))
        (MkTyping TContent [] [])
        [R_Equality; R_Variable; R_Variable]).
Proof.
  intro derivation.
  dependent destruction derivation.
  repeat match goal with
  | nested : a0_type _ _ _ |- _ => dependent destruction nested
  end.
  repeat match goal with
  | lookup : env_lookup _ _ _ |- _ => dependent destruction lookup
  end.
  simpl in *; discriminate.
Qed.

Example closed_lambda_plural_self_equality_negative :
  ~ a0_type [] Synth
      (MkTypedCase
        (TLam (TRef TEntity) (TEquality (TVar 0) (TVar 0)))
        (MkTyping (TArrow Pure (TRef TEntity) TContent) [] [])
        [R_LambdaPure; R_Equality; R_Variable; R_Variable]).
Proof.
  intro derivation.
  dependent destruction derivation.
  repeat match goal with
  | nested : a0_type _ _ _ |- _ => dependent destruction nested
  end.
  repeat match goal with
  | lookup : env_lookup _ _ _ |- _ => dependent destruction lookup
  end.
  simpl in *; discriminate.
Qed.

Example negative_wrong_expected :
  ~ a0_type [] (Check TEntity)
      (MkTypedCase (TNat 0) (MkTyping TNatural [] [])
        [R_CheckSynth; R_Natural]).
Proof.
  intro derivation.
  inversion derivation; subst; simpl in *; discriminate.
Qed.

Example negative_zero_selection :
  ~ a0_type [] (Check (TRefComp (TRef TEntity)))
      (MkTypedCase
        (TSelectExactly (TNat 0) (TLam TEntity TTop))
        (MkTyping (TRefComp (TRef TEntity)) [ERefer] [])
        [R_SelectExactly; R_CheckSynth; R_Natural;
         R_LambdaPure; R_Top]).
Proof.
  intro derivation.
  inversion derivation; subst; simpl in *; discriminate.
Qed.

Example negative_unbound_variable :
  ~ exists result_record result_trace,
      a0_type [] Synth
        (MkTypedCase (TVar 0) result_record result_trace).
Proof.
  intros [result_record [result_trace derivation]].
  inversion derivation; subst.
  match goal with
  | lookup : env_lookup [] _ _ |- _ => inversion lookup
  end.
Qed.
