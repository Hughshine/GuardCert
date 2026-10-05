From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightNoWrap ClightDecisionRule ClightCondition ClightPureExpr ClightCountedLoop ClightCountedProtocol
  ClightRegionProgress ClightSameAddress ClightTempFrame ClightTempFootprint ClightLoopExecution ClightStraightLine ClightLoopSyntax.
From GuardInterface Require Import ClightStrictLoopProgress ClightStableLoadBody ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition signed_pointer_temp pointer := Etempvar pointer (Tpointer type_int32s noattr).
Definition signed_load pointer := Ederef (signed_pointer_temp pointer) type_int32s.
Definition loaded_bound_test iterator bound :=
  Ebinop Olt (Etempvar iterator type_int32s) (signed_load bound) type_int32s.
Definition loaded_bound_body out iterator :=
  Sassign (signed_load out)
    (Ebinop Oadd (Etempvar iterator type_int32s) (Econst_int Int.one type_int32s) type_int32s).
Definition loaded_bound_loop iterator bound body :=
  strict_frontend_loop iterator (loaded_bound_test iterator bound) body.

Lemma signed_load_inv ge locals le m pointer value : eval_expr ge locals le m (signed_load pointer) value ->
  exists block offset, le ! pointer = Some (Vptr block offset) /\
    Mem.loadv Mint32 m (Vptr block offset) = Some value.
Proof.
  intro RUN; inversion RUN; subst.
  match goal with LV : eval_lvalue _ _ _ _ (signed_load pointer) _ _ _ |- _ => inversion LV; subst end.
  match goal with TEMP : eval_expr _ _ _ _ (signed_pointer_temp pointer) _ |- _ =>
    apply scalar_temp_inv in TEMP end.
  match goal with LOAD : deref_loc _ _ _ _ _ _ |- _ => inversion LOAD; subst; try discriminate end.
  match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end.
  do 2 eexists; split; eassumption.
Qed.

Theorem loaded_bound_test_facts ge locals le m iterator bound flag :
  expression_test (loaded_bound_test iterator bound) (Entry ge locals le m) flag ->
  exists x upper block offset,
    le ! iterator = Some (Vint x) /\ le ! bound = Some (Vptr block offset) /\
    Mem.loadv Mint32 m (Vptr block offset) = Some (Vint upper) /\ flag = Int.lt x upper.
Proof.
  intros [value [EVAL BOOL]]; apply scalar_binary_inv in EVAL.
  destruct EVAL as [x [upper [X [UP OP]]]]; apply scalar_temp_inv in X.
  apply signed_load_inv in UP; destruct UP as [b [ofs [Q READ]]].
  destruct x; destruct upper; try discriminate OP.
  change (Some (Val.of_bool (Int.lt i i0)) = Some value) in OP; injection OP as VALUE; subst value.
  rewrite bool_of_bool in BOOL; exists i, i0, b, ofs; repeat split; try assumption; congruence.
Qed.

Theorem loaded_bound_test_strict ge locals le m iterator bound :
  expression_test (loaded_bound_test iterator bound) (Entry ge locals le m) true ->
  strict_counter_active iterator le.
Proof.
  intro TEST; destruct (loaded_bound_test_facts TEST) as [x [upper [b [ofs [I [Q [READ LT]]]]]]].
  exists x; split; [exact I|].
  unfold Int.lt in LT; destruct (zlt (Int.signed x) (Int.signed upper));
    pose proof (Int.signed_range upper); try discriminate; lia.
Qed.

Lemma loaded_bound_test_eval ge locals le m iterator bound x upper b ofs :
  le ! iterator = Some (Vint x) -> le ! bound = Some (Vptr b ofs) ->
  Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint upper) ->
  expression_test (loaded_bound_test iterator bound) (Entry ge locals le m) (Int.lt x upper).
Proof.
  intros I Q READ; exists (Val.of_bool (Int.lt x upper)); split; [|apply bool_of_bool].
  eapply eval_Ebinop with (v1 := Vint x) (v2 := Vint upper); [constructor; exact I| |reflexivity].
  apply eval_Elvalue with (loc := b) (ofs := ofs) (bf := Full).
  - apply eval_Ederef, eval_Etempvar; exact Q.
  - apply deref_loc_value with (chunk := Mint32); [reflexivity|exact READ].
Qed.

Lemma loaded_bound_cached_test ge locals le m iterator bound cache upper b ofs flag :
  le ! bound = Some (Vptr b ofs) -> Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint upper) ->
  le ! cache = Some (Vint upper) ->
  expression_test (loaded_bound_test iterator bound) (Entry ge locals le m) flag ->
  expression_test (counter_condition iterator cache) (Entry ge locals le m) flag.
Proof.
  intros Q READ CACHE [value [EVAL BOOL]].
  apply scalar_binary_inv in EVAL; destruct EVAL as [x [word [I [LOAD OP]]]].
  apply signed_load_inv in LOAD; destruct LOAD as [other [offset [OTHER LOADED]]].
  cbn [entry_ge entry_env entry_temps entry_memory] in OTHER, LOADED.
  assert (PTR : Vptr other offset = Vptr b ofs) by congruence; injection PTR; intros; subst.
  assert (WORD : word = Vint upper) by congruence; subst word.
  exists value; split; [eapply eval_Ebinop; [exact I|constructor; exact CACHE|exact OP]|exact BOOL].
Qed.

Lemma loaded_bound_body_store fe ge locals le m out iterator trace after final outcome :
  exec_stmt fe ge locals le m (loaded_bound_body out iterator) trace after final outcome ->
  exists b ofs value, le ! out = Some (Vptr b ofs) /\
    Mem.storev Mint32 m (Vptr b ofs) value = Some final.
Proof.
  intro RUN; inversion RUN; subst.
  match goal with LV : eval_lvalue _ _ _ _ (signed_load out) _ _ _ |- _ => inversion LV; subst end.
  match goal with POINTER : eval_expr _ _ _ _ (signed_pointer_temp out) _ |- _ =>
    apply scalar_temp_inv in POINTER end.
  match goal with STORE : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion STORE; subst; try discriminate end.
  match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end.
  do 3 eexists; split; eassumption.
Qed.

Lemma loaded_bound_body_preserves fe ge locals le m out iterator bound b ofs upper body trace after final outcome :
  le ! bound = Some (Vptr b ofs) -> Mem.loadv Mint32 m (Vptr b ofs) = Some upper ->
  le ! out <> le ! bound ->
  flatten_region body = [loaded_bound_body out iterator] ->
  exec_stmt fe ge locals le m body trace after final outcome ->
  Mem.loadv Mint32 final (Vptr b ofs) = Some upper.
Proof.
  intros Q READ APART FLAT RUN.
  assert (QUIET : quiet_statement body = true).
  { apply flatten_quiet_certificate; rewrite FLAT; constructor; [reflexivity|constructor]. }
  assert (NORMAL : normal_statement body = true).
  { apply flatten_normal_certificate; rewrite FLAT; constructor; [reflexivity|constructor]. }
  pose proof (@quiet_execution_silent fe ge locals le m body trace after final outcome RUN QUIET) as SILENT; subst trace.
  pose proof (@normal_statement_execution fe ge locals body NORMAL le m E0 after final outcome RUN) as EXIT; subst outcome.
  apply (flattened_singleton_execution FLAT) in RUN.
  destruct (loaded_bound_body_store RUN) as [p [off [value [P STORE]]]].
  eapply mint32_load_survives_apart_store; [exact STORE|exact READ|].
  intro EQ; apply APART; congruence.
Qed.
Print Assumptions loaded_bound_test_strict.
Print Assumptions loaded_bound_cached_test.
Print Assumptions loaded_bound_body_preserves.
