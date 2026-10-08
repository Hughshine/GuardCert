From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightPureExpr ClightNoWrap.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryArrayBackend GuardMemoryAffineInnerPointerSyntax
  GuardMemoryAffineInnerPointerSourceDomain GuardMemoryAffineSourceValuation GuardMemoryParametricGuard
  GuardMemoryParametricSourceDomain.
From GuardInterface Require Import GuardedRewrite ReadonlyConditionComposition
  ClightConditionComposition ClightReadonlyRewrite ClightReadonlyCompletedCondition
  ClightAffineSnapshotSyntax ClightAffineSnapshotRows ClightAffineSnapshotSourceInputs
  ClightAffineZeroSnapshotPreparation ClightAffinePointerGuard ClightAffineEmptyWidth.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section CONDITION.
Variable original : statement.
Variable site : affine_snapshot_source_package original.
Let package:=snapshot_cached_package site.
Let shape:=affine_inner_pointer_shape package.
Let row:=affine_inner_pointer_row shape.
Let bound:=affine_inner_pointer_bound shape.
Let expression:=affine_inner_pointer_expression package.
Let header:=memory_affine_inner_pointer_header shape expression.
Let bounds:=affine_zero_snapshot_header_bounds site.
Variable width : decision_tree.
Hypothesis WIDTH : compile_affine_empty_width row header bounds expression=Some width.
Variable fe : genv->function->list val->mem->env->temp_env->mem->Prop.
Variable O : Type.
Variable observe : fragment_observation->O->Prop.
Let H:=readonly_clight_host fe observe.
Let D:=affine_snapshot_original_domain package(snapshot_root site)(snapshot_child site)
  (snapshot_child_cache site)(snapshot_original_header site)fe.
Let HEAD entry:=memory_affine_inner_pointer_header_accept shape(affine_inner_pointer_row_limit package)entry=true.
Let RANGE entry:=MemoryNested.A.env_within bounds(memory_source_parameter_values header entry).
Definition affine_empty_snapshot_width_fact entry:=affine_empty_width_fact expression
  (memory_source_word_valuation(entry_temps entry))row bound.
Definition affine_empty_snapshot_facts entry:=HEAD entry /\ affine_empty_snapshot_width_fact entry.
Definition affine_empty_snapshot_tree:=decision_bind(affine_zero_snapshot_header_tree site)width(Decision false).

Definition affine_empty_snapshot_width_condition : readonly_condition H
  (fun entry=>D entry /\(HEAD entry /\ RANGE entry))affine_empty_snapshot_width_fact width.
Proof.
  apply readonly_completed_tree_condition.
  - intros entry[DOMAIN[HEAD_FACT RANGE_FACT]].
    destruct(@compile_affine_empty_width_exact row header bounds expression width
      (memory_source_parameter_values header entry)(entry_ge entry)(entry_env entry)(entry_temps entry)
      (entry_memory entry)WIDTH
      (@affine_zero_snapshot_head_view original site fe entry DOMAIN HEAD_FACT)RANGE_FACT)
      as [first[last[ENDS EXACT]]].
    replace(Entry(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry))with entry
      in EXACT by(destruct entry; reflexivity).
    eexists; apply(proj2(EXACT _)); reflexivity.
  - intros entry[DOMAIN[HEAD_FACT RANGE_FACT]]RUN.
    assert(VALUES:memory_source_parameter_values header entry=
      map(memory_source_word_valuation(entry_temps entry))header).
    { unfold memory_source_parameter_values; apply map_ext; intro id;
        symmetry; apply memory_source_word_temp. }
    pose proof(@affine_zero_snapshot_head_view original site fe entry DOMAIN HEAD_FACT)as VIEW.
    unfold RANGE in RANGE_FACT.
    change(MemoryNested.A.typed_view header(memory_source_parameter_values header entry)(entry_temps entry))in VIEW.
    rewrite VALUES in RANGE_FACT,VIEW.
    replace entry with(Entry(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry))
      in RUN by(destruct entry; reflexivity).
    eapply compile_affine_empty_width_sound; [exact WIDTH| |exact RANGE_FACT|exact RUN].
    exact VIEW.
Defined.

Definition affine_empty_snapshot_condition : readonly_condition H D affine_empty_snapshot_facts
  affine_empty_snapshot_tree.
Proof.
  eapply readonly_condition_entails.
  - exact(@sequence_readonly_conditions clight_entry H(clight_readonly_check_algebra fe observe)
      D(fun entry=>HEAD entry /\ RANGE entry)affine_empty_snapshot_width_fact
      (affine_zero_snapshot_header_tree site)width
      (@affine_zero_snapshot_header_condition original site fe O observe)
      affine_empty_snapshot_width_condition).
  - intros entry DOMAIN[[HEAD_FACT RANGE_FACT]WIDTH_FACT]; split; assumption.
Defined.
End CONDITION.

Print Assumptions affine_empty_snapshot_width_condition.
Print Assumptions affine_empty_snapshot_condition.
