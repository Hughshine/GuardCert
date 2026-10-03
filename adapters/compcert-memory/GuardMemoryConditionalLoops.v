From Stdlib Require Import List Bool ZArith Lia.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryLoops GuardMemoryLoopTrace GuardMemoryPolyhedral.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Refine each executed instruction by a mathematical affine test.
    The eventual Clight encoder independently checks machine representability. *)
Fixpoint guard_memory_instructions (test : L.test) (st : L.stmt) : L.stmt :=
  match st with
  | L.Instr instruction arguments => L.Guard test (L.Instr instruction arguments)
  | L.Seq sts => L.Seq (guard_memory_instruction_list test sts)
  | L.Guard original body => L.Guard original (guard_memory_instructions test body)
  | L.Loop lower upper body => L.Loop lower upper (guard_memory_instructions test body)
  end
with guard_memory_instruction_list (test : L.test) (sts : L.stmt_list) : L.stmt_list :=
  match sts with
  | L.SNil => L.SNil
  | L.SCons st rest => L.SCons (guard_memory_instructions test st) (guard_memory_instruction_list test rest)
  end.

Lemma memory_filter_flat_map {A B} (keep : B -> bool) (events : A -> list B) xs :
  filter keep (flat_map events xs) = flat_map (fun x => filter keep (events x)) xs.
Proof. induction xs; cbn; [reflexivity|rewrite filter_app, IHxs; reflexivity]. Qed.
Lemma memory_map_filter {A B} (f : A -> B) (keep : B -> bool) xs :
  filter keep (map f xs) = map f (filter (fun x => keep (f x)) xs).
Proof. induction xs; cbn; [reflexivity|destruct (keep (f a)); cbn; rewrite IHxs; reflexivity]. Qed.
Lemma memory_filter_ext_in {A} (first second : A -> bool) xs :
  (forall x, In x xs -> first x = second x) -> filter first xs = filter second xs.
Proof.
  induction xs; intro SAME; cbn; [reflexivity|].
  rewrite SAME by (left; reflexivity); rewrite IHxs; [reflexivity|].
  intros; apply SAME; right; assumption.
Qed.

Theorem guarded_memory_trace_contracts test :
  (forall st env, memory_loop_trace (guard_memory_instructions test st) env =
    filter (fun event => L.eval_test (event_environment event) test) (memory_loop_trace st env)) /\
  (forall sts env, memory_loop_list_trace (guard_memory_instruction_list test sts) env =
    filter (fun event => L.eval_test (event_environment event) test) (memory_loop_list_trace sts env)).
Proof.
  apply trace_stmt_list_ind.
  - intros lower upper body IH env; cbn; rewrite memory_filter_flat_map.
    apply flat_map_ext; intro x; apply IH.
  - intros instruction arguments env; cbn; destruct (L.eval_test env test); reflexivity.
  - intros sts IH; exact IH.
  - intros original body IH env; cbn; destruct (L.eval_test env original); [apply IH|reflexivity].
  - intro env; reflexivity.
  - intros st IH sts REST env; cbn; rewrite IH,REST,filter_app; reflexivity.
Qed.
Theorem guarded_memory_trace test st env :
  memory_loop_trace (guard_memory_instructions test st) env =
  filter (fun event => L.eval_test (event_environment event) test) (memory_loop_trace st env).
Proof. apply guarded_memory_trace_contracts. Qed.

Definition memory_affine_cut_test row_coefficient column_coefficient limit :=
  L.LE (L.Sum (L.Mult row_coefficient (L.Var 1)) (L.Mult column_coefficient (L.Var 0)))
    (L.Constant limit).
Lemma memory_affine_cut_test_at row_coefficient column_coefficient limit j i rest :
  L.eval_test (j::i::rest) (memory_affine_cut_test row_coefficient column_coefficient limit) =
  (row_coefficient*i+column_coefficient*j <=? limit).
Proof. reflexivity. Qed.

Print Assumptions guarded_memory_trace.

Theorem conditional_memory_loop_points test st env emit keep :
  (forall event, In event (memory_loop_trace st env) ->
    keep (emit event) = L.eval_test (event_environment event) test) ->
  (forall event before after, In event (memory_loop_trace st env) ->
    memory_event_step event before after <-> GuardMemoryIRs.PolyLang.instr_point_sema (emit event) before after) ->
  forall before after, L.loop_semantics (guard_memory_instructions test st) env before after <->
    GuardMemoryIRs.PolyLang.instr_point_list_semantics (filter keep (map emit (memory_loop_trace st env))) before after.
Proof.
  intros KEEP STEP before after; rewrite memory_loop_trace_correct,guarded_memory_trace,memory_map_filter.
  assert (FILTER : filter (fun event => keep (emit event)) (memory_loop_trace st env) =
    filter (fun event => L.eval_test (event_environment event) test) (memory_loop_trace st env)).
  { apply memory_filter_ext_in; exact KEEP. }
  rewrite FILTER; apply memory_trace_points; intros event first final MEMBER.
  apply filter_In in MEMBER as [MEMBER _]; apply STEP; exact MEMBER.
Qed.
