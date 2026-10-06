From Stdlib Require Import List Bool Arith ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightNoWrap ClightPureExpr ClightSameAddress.
From GuardInterface Require Import ClightCounterProgress ClightCircularCounter.
Set Implicit Arguments.

Definition circular_store out iterator := Sassign (word_load out)
  (Ebinop Oadd (Etempvar iterator type_int32u)
    (Econst_int (Int.repr 2) type_int32u) type_int32u).
Definition circular_loaded_test iterator bound :=
  Ebinop One (Etempvar iterator type_int32u) (word_load bound) type_int32s.
Definition circular_cached_test iterator cache :=
  Ebinop One (Etempvar iterator type_int32u) (Etempvar cache type_int32u) type_int32s.
Definition circular_increment_expression iterator :=
  Ebinop Oadd (Etempvar iterator type_int32u) (Econst_int Int.one type_int32s) type_int32u.
Definition circular_memory_loop iterator out head :=
  generic_frontend_loop iterator (circular_increment_expression iterator) head (Ssequence Sskip (circular_store out iterator)).

Inductive circular_phase :=
| cm_start | cm_header | cm_inner | cm_head_skip | cm_test | cm_body_skip
| cm_store_pre | cm_store_skip | cm_store | cm_after_store | cm_increment | cm_increment_skip | cm_set
| cm_after_set | cm_break_seq | cm_break_loop | cm_done.

Definition circular_phase_equal (a b : circular_phase) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

Section MACHINE.
Variable iterator out : ident.
Definition cm_check head := Sifthenelse head Sskip Sbreak.
Definition cm_pre head := Ssequence Sskip (cm_check head).
Definition cm_body_code := Ssequence Sskip (circular_store out iterator).
Definition cm_header_code head := Ssequence (cm_pre head) cm_body_code.
Definition cm_increment_code := Ssequence Sskip (Sset iterator (circular_increment_expression iterator)).
Definition cm_loop1 head outside := Kloop1 (cm_header_code head) cm_increment_code outside.
Definition cm_loop2 head outside := Kloop2 (cm_header_code head) cm_increment_code outside.
Definition circular_machine_state fn outside locals head phase le m : state :=
  match phase with
  | cm_start => State fn (circular_memory_loop iterator out head) outside locals le m
  | cm_header => State fn (cm_header_code head) (cm_loop1 head outside) locals le m
  | cm_inner => State fn (cm_pre head) (Kseq cm_body_code (cm_loop1 head outside)) locals le m
  | cm_head_skip => State fn Sskip (Kseq (cm_check head) (Kseq cm_body_code (cm_loop1 head outside))) locals le m
  | cm_test => State fn (cm_check head) (Kseq cm_body_code (cm_loop1 head outside)) locals le m
  | cm_body_skip => State fn Sskip (Kseq cm_body_code (cm_loop1 head outside)) locals le m
  | cm_store_pre => State fn cm_body_code (cm_loop1 head outside) locals le m
  | cm_store_skip => State fn Sskip (Kseq (circular_store out iterator) (cm_loop1 head outside)) locals le m
  | cm_store => State fn (circular_store out iterator) (cm_loop1 head outside) locals le m
  | cm_after_store => State fn Sskip (cm_loop1 head outside) locals le m
  | cm_increment => State fn cm_increment_code (cm_loop2 head outside) locals le m
  | cm_increment_skip => State fn Sskip (Kseq (Sset iterator (circular_increment_expression iterator)) (cm_loop2 head outside)) locals le m
  | cm_set => State fn (Sset iterator (circular_increment_expression iterator)) (cm_loop2 head outside) locals le m
  | cm_after_set => State fn Sskip (cm_loop2 head outside) locals le m
  | cm_break_seq => State fn Sbreak (Kseq cm_body_code (cm_loop1 head outside)) locals le m
  | cm_break_loop => State fn Sbreak (cm_loop1 head outside) locals le m
  | cm_done => State fn Sskip outside locals le m
  end.

Inductive circular_move temps ge locals head : circular_phase -> temp_env -> mem -> circular_phase -> temp_env -> mem -> Prop :=
| move_start : forall le m, circular_move temps ge locals head cm_start le m cm_header le m
| move_header : forall le m, circular_move temps ge locals head cm_header le m cm_inner le m
| move_inner : forall le m, circular_move temps ge locals head cm_inner le m cm_head_skip le m
| move_head_skip : forall le m, circular_move temps ge locals head cm_head_skip le m cm_test le m
| move_test : forall le m flag, expression_test head (Entry ge locals le m) flag ->
    circular_move temps ge locals head cm_test le m (if flag then cm_body_skip else cm_break_seq) le m
| move_body_skip : forall le m, circular_move temps ge locals head cm_body_skip le m cm_store_pre le m
| move_store_pre : forall le m, circular_move temps ge locals head cm_store_pre le m cm_store_skip le m
| move_store_skip : forall le m, circular_move temps ge locals head cm_store_skip le m cm_store le m
| move_store : forall le m final,
    exec_stmt (adapter_entry temps) ge locals le m (circular_store out iterator) E0 le final Out_normal ->
    circular_move temps ge locals head cm_store le m cm_after_store le final
| move_after_store : forall le m, circular_move temps ge locals head cm_after_store le m cm_increment le m
| move_increment : forall le m, circular_move temps ge locals head cm_increment le m cm_increment_skip le m
| move_increment_skip : forall le m, circular_move temps ge locals head cm_increment_skip le m cm_set le m
| move_set : forall le m value,
    eval_expr ge locals le m (circular_increment_expression iterator) value ->
    circular_move temps ge locals head cm_set le m cm_after_set (PTree.set iterator value le) m
| move_after_set : forall le m, circular_move temps ge locals head cm_after_set le m cm_start le m
| move_break_seq : forall le m, circular_move temps ge locals head cm_break_seq le m cm_break_loop le m
| move_break_loop : forall le m, circular_move temps ge locals head cm_break_loop le m cm_done le m.

Lemma circular_machine_step_sound temps ge fn outside locals head phase le m next_phase after final :
  circular_move temps ge locals head phase le m next_phase after final ->
  adapter_step temps ge (circular_machine_state fn outside locals head phase le m) E0
    (circular_machine_state fn outside locals head next_phase after final).
Proof.
  intro MOVE; inversion MOVE; subst; cbn [circular_machine_state circular_memory_loop generic_frontend_loop
    cm_header_code cm_body_code cm_pre cm_check cm_increment_code cm_loop1 cm_loop2].
  all: try solve [unfold adapter_step; econstructor; eauto].
  - destruct H as [value [EVAL BOOL]]. destruct flag;
      cbn [circular_machine_state cm_check cm_loop1]; unfold adapter_step;
      [eapply step_ifthenelse with (b := true) | eapply step_ifthenelse with (b := false)]; eauto.
  - inversion H; subst; unfold adapter_step; eapply step_assign; eauto.
Qed.

Lemma circular_machine_step_closed temps ge fn outside locals head phase le m events next :
  phase <> cm_done ->
  adapter_step temps ge (circular_machine_state fn outside locals head phase le m) events next ->
  exists next_phase after final, events = E0 /\
    next = circular_machine_state fn outside locals head next_phase after final /\
    circular_move temps ge locals head phase le m next_phase after final.
Proof.
  intros ACTIVE STEP; destruct phase; try contradiction;
    cbv [circular_machine_state circular_memory_loop generic_frontend_loop
      cm_header_code cm_body_code cm_pre cm_check cm_increment_code cm_loop1 cm_loop2] in STEP;
    inversion STEP; subst.
  all: try match goal with BAD : _ = _ \/ _ = _ |- _ =>
    destruct BAD; try discriminate end.
  all: try solve [match goal with BAD : is_call_cont _ |- _ => contradiction BAD end].
  all: try solve [eexists; exists le, m; split; [reflexivity |];
    split; [| constructor]; reflexivity].
  - exists (if b then cm_body_skip else cm_break_seq), le, m.
    split; [reflexivity | split; [destruct b; reflexivity |]].
    constructor; exists v1; split; assumption.
  - exists cm_after_store, le, m'; split; [reflexivity | split; [reflexivity |]].
    constructor; econstructor; eauto.
  - exists cm_after_set, (PTree.set iterator v le), m; split; [reflexivity |].
    split; [reflexivity | constructor; assumption].
Qed.

Lemma circular_machine_source_shape fn outside locals head phase le m :
  exists code stack, circular_machine_state fn outside locals head phase le m = State fn code stack locals le m.
Proof. destruct phase; repeat eexists; reflexivity. Qed.

Lemma circular_store_facts temps ge locals le m final :
  exec_stmt (adapter_entry temps) ge locals le m (circular_store out iterator) E0 le final Out_normal ->
  exists b ofs value, le ! out = Some (Vptr b ofs) /\
    Mem.storev Mint32 m (Vptr b ofs) value = Some final.
Proof.
  intro RUN; inversion RUN; subst.
  match goal with LV : eval_lvalue _ _ _ _ (word_load out) _ _ _ |- _ => inversion LV; subst end.
  match goal with PTR : eval_expr _ _ _ _ (pointer_temp out) _ |- _ => apply scalar_temp_inv in PTR end.
  match goal with STORE : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion STORE; subst; try discriminate end.
  match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end.
  do 3 eexists; split; eassumption.
Qed.
End MACHINE.

Lemma circular_loaded_test_facts ge locals le m iterator bound flag :
  expression_test (circular_loaded_test iterator bound) (Entry ge locals le m) flag ->
  exists word upper b ofs, le ! iterator = Some (Vint word) /\ le ! bound = Some (Vptr b ofs) /\
    Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint upper) /\ flag = negb (Int.eq word upper).
Proof.
  intros [value [EVAL BOOL]]. apply scalar_binary_inv in EVAL.
  destruct EVAL as [word [upper [ITER [BOUND OP]]]]. apply scalar_temp_inv in ITER.
  apply word_load_inv in BOUND; destruct BOUND as [b [ofs [PTR READ]]].
  destruct word, upper; try discriminate OP.
  change (Some (Val.of_bool (negb (Int.eq i i0))) = Some value) in OP.
  injection OP as SAME; subst value; rewrite bool_of_bool in BOOL.
  exists i, i0, b, ofs; repeat split; try assumption; congruence.
Qed.

Lemma circular_word_load_eval ge locals le m bound b ofs value :
  le ! bound = Some (Vptr b ofs) -> Mem.loadv Mint32 m (Vptr b ofs) = Some value ->
  eval_expr ge locals le m (word_load bound) value.
Proof.
  intros PTR READ; eapply eval_Elvalue with (loc := b) (ofs := ofs) (bf := Full).
  - apply eval_Ederef, eval_Etempvar; exact PTR.
  - apply deref_loc_value with (chunk := Mint32); [reflexivity | exact READ].
Qed.

Print Assumptions circular_machine_step_sound.
Print Assumptions circular_machine_step_closed.
Print Assumptions circular_store_facts.
Print Assumptions circular_loaded_test_facts.
