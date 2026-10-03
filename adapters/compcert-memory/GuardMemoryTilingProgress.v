From Stdlib Require Import List Bool ZArith Lia Sorting.Sorted Sorting.Permutation Sorting.SetoidList.
From polcert.lib Require Import Linalg ImpureAlarmConfig.
From polcert.src Require Import PointWitness TilingWitness SelectionSort.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryPolyhedral.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Module TV := GuardMemoryTilingValidator.
Module T := TV.Tiling.
Module TP := T.PL.

(** A constructive forward bridge is needed in addition to the inherited
    after-to-before tiling theorem. This bridge preserves the actual parameter
    values and reconstructs a finite execution, without a progress axiom. *)
Section SINGLE_STATEMENT.
Variable before after : TP.PolyInstr.
Variable witness : statement_tiling_witness.
Variable context : list TP.ident.
Variable variables : list (TP.ident * TP.Ty.t).
Variable parameters : list Z.
Hypothesis STRUCTURE : T.tiling_rel_pprog_structure_source
  ([before],context,variables) ([after],context,variables)
  [T.compiled_pinstr_tiling_witness witness].
Hypothesis ENVIRONMENT : length parameters = length context.
Hypothesis WELLFORMED : T.wf_statement_tiling_witness_with_param_dim (length parameters) witness.
Hypothesis POSITIVE : Forall (fun link => 0 < tl_tile_size link) (stw_links witness).
Hypothesis DEPTH : stw_point_dim witness = TP.pi_depth before.
Hypothesis IDENTITY : TP.pi_point_witness before = PSWIdentity (TP.pi_depth before).

Definition retiled_instruction := T.retiled_old_pinstr (length parameters) before after witness.
Definition project_old := T.before_of_retiled_old_point (length parameters)
  (length (stw_links witness)) before.
Definition lift_before (ip : TP.InstrPoint) : TP.InstrPoint :=
  let index := T.eval_pinstr_tiling_index_with_env parameters
    (skipn (length parameters) (TP.ip_index ip)) parameters (T.compiled_pinstr_tiling_witness witness) in
  {| TP.ip_nth := TP.ip_nth ip; TP.ip_index := index;
     TP.ip_transformation := TP.current_transformation_of retiled_instruction index;
     TP.ip_time_stamp := affine_product (TP.pi_schedule retiled_instruction) index;
     TP.ip_instruction := TP.pi_instr retiled_instruction;
     TP.ip_depth := TP.pi_depth retiled_instruction |}.
Definition valid_point (instruction : TP.PolyInstr) (ip : TP.InstrPoint) :=
  firstn (length parameters) (TP.ip_index ip) = parameters /\
  TP.belongs_to ip instruction /\ TP.ip_nth ip = 0%nat /\
  length (TP.ip_index ip) = (length parameters + TP.pi_depth instruction)%nat.

Lemma statement_structure : T.tiling_rel_pinstr_structure_source (length parameters)
  before after (T.compiled_pinstr_tiling_witness witness).
Proof.
  rewrite ENVIRONMENT.
  eapply T.tiling_rel_pprog_structure_source_nth with
    (before_pis := [before]) (after_pis := [after])
    (before_ctxt := context) (after_ctxt := context)
    (before_vars := variables) (after_vars := variables)
    (ws := [T.compiled_pinstr_tiling_witness witness]) (n := 0%nat);
    exact STRUCTURE || reflexivity.
Qed.
Lemma after_depth : TP.pi_depth after = (TP.pi_depth before + length (stw_links witness))%nat.
Proof. pose proof statement_structure as [_ [D _]]; exact D. Qed.

Lemma lift_before_shape ip : valid_point before ip ->
  valid_point retiled_instruction (lift_before ip) /\ project_old (lift_before ip) = ip.
Proof.
  intros [PREFIX [BELONGS [NTH LENGTH]]].
  destruct (@T.tiling_rel_pprog_structure_source_before_point_has_retiled_old_preimage_nth
    [before] context variables [after] context variables [witness] 0 before after witness
    parameters ip STRUCTURE eq_refl eq_refl eq_refl ENVIRONMENT WELLFORMED POSITIVE DEPTH
    PREFIX BELONGS NTH LENGTH) as [old [OLD_BELONGS [INDEX INVERSE]]].
  assert (OLD_NTH : TP.ip_nth old = TP.ip_nth ip).
  { apply (f_equal TP.ip_nth) in INVERSE; exact INVERSE. }
  assert (CANONICAL : old = lift_before ip).
  { destruct old as [nth index transformation timestamp instruction depth].
    destruct OLD_BELONGS as [DOMAIN [TRANSFORMATION [TIMESTAMP [INSTRUCTION DEPTH_OLD]]]].
    unfold lift_before, retiled_instruction; cbn in *.
    subst; reflexivity. }
  subst old; split; [|exact INVERSE].
  split.
  - unfold lift_before; cbn.
    unfold T.eval_pinstr_tiling_index_with_env, eval_statement_tiling_witness_with_env.
    rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r; reflexivity.
  - split; [exact OLD_BELONGS|]. split; [exact NTH|].
    unfold lift_before, T.eval_pinstr_tiling_index_with_env,
      eval_statement_tiling_witness_with_env, eval_statement_tiling_witness, lift_point,
      retiled_instruction; cbn.
    rewrite !app_length, eval_tile_links_length, skipn_length, after_depth.
    cbn; lia.
Qed.

Lemma project_old_shape ip : valid_point retiled_instruction ip -> valid_point before (project_old ip).
Proof.
  intros [PREFIX [BELONGS [NTH LENGTH]]].
  split; [apply T.before_of_retiled_old_point_prefix; exact PREFIX|].
  split.
  - eapply T.tiling_rel_pprog_structure_source_before_of_retiled_old_point_belongs_to_nth
      with (before_pis := [before]) (after_pis := [after]) (ws := [witness])
      (before_ctxt := context) (after_ctxt := context)
      (before_vars := variables) (after_vars := variables) (n := 0%nat);
      exact STRUCTURE || exact ENVIRONMENT || exact WELLFORMED || exact POSITIVE ||
      exact DEPTH || exact BELONGS || exact LENGTH || exact PREFIX || reflexivity.
  - split; [exact NTH|]. unfold project_old; cbn.
    apply T.before_index_of_retiled_old_length; [exact DEPTH|].
    unfold retiled_instruction in LENGTH; cbn in LENGTH; rewrite after_depth in LENGTH; lia.
Qed.

Lemma project_old_injective first second :
  valid_point retiled_instruction first -> valid_point retiled_instruction second ->
  project_old first = project_old second -> first = second.
Proof.
  intros [PF [BF [NF LF]]] [PS [BS [NS LS]]] SAME.
  eapply T.tiling_rel_pinstr_structure_source_before_of_retiled_old_point_injective
    with (env := parameters) (before := before) (after := after)
      (w := T.compiled_pinstr_tiling_witness witness);
    exact statement_structure || apply T.wf_compiled_pinstr_tiling_witness ||
    apply T.compiled_pinstr_tiling_witness_matches || exact WELLFORMED || exact POSITIVE ||
    exact DEPTH || exact BF || exact BS || exact LF || exact LS || exact PF || exact PS || exact SAME.
Qed.

Lemma lift_project_old ip : valid_point retiled_instruction ip -> lift_before (project_old ip) = ip.
Proof.
  intro VALID; pose proof (project_old_shape VALID) as SOURCE.
  destruct (lift_before_shape SOURCE) as [LIFT INVERSE].
  eapply project_old_injective; [exact LIFT|exact VALID|exact INVERSE].
Qed.

Lemma lift_before_execution ip initial final : valid_point before ip ->
  (TP.instr_point_sema ip initial final <-> TP.instr_point_sema (lift_before ip) initial final).
Proof.
  intro VALID; destruct (lift_before_shape VALID) as [[PREFIX [BELONGS [_ LENGTH]]] INVERSE].
  pose proof (@T.tiling_rel_pprog_structure_source_before_of_retiled_old_instr_semantics_iff_nth
    [before] context variables [after] context variables [witness] 0 before after witness
    parameters (lift_before ip) initial final STRUCTURE eq_refl eq_refl eq_refl ENVIRONMENT
    WELLFORMED POSITIVE DEPTH IDENTITY BELONGS LENGTH PREFIX) as EQUIVALENT.
  unfold project_old in INVERSE; rewrite INVERSE in EQUIVALENT; symmetry; exact EQUIVALENT.
Qed.

Lemma lift_before_timestamp ip : valid_point before ip ->
  TP.ip_time_stamp (lift_before ip) = TP.ip_time_stamp ip.
Proof.
  intro VALID; destruct (lift_before_shape VALID) as [[PREFIX [BELONGS [_ LENGTH]]] INVERSE].
  pose proof (@T.tiling_rel_pinstr_structure_source_before_of_retiled_old_time_stamp
    parameters before after (T.compiled_pinstr_tiling_witness witness) (lift_before ip)
    statement_structure (T.wf_compiled_pinstr_tiling_witness witness) DEPTH BELONGS LENGTH PREFIX) as SAME.
  change (TP.ip_time_stamp (project_old (lift_before ip)) = TP.ip_time_stamp (lift_before ip)) in SAME.
  rewrite INVERSE in SAME; symmetry; exact SAME.
Qed.

Lemma singleton_flatten instruction points :
  TP.flatten_instrs parameters [instruction] points <->
  (forall ip, In ip points <-> valid_point instruction ip) /\
  NoDup points /\ Sorted TP.np_lt points.
Proof.
  unfold TP.flatten_instrs, valid_point.
  split.
  - intros [_ [MEMBERS REST]]; split; [|exact REST].
    intro ip; rewrite MEMBERS; split.
    + intros [pi [NTH [PREFIX [BELONGS LENGTH]]]].
      destruct (TP.ip_nth ip) eqn:N; cbn in NTH.
      * inversion NTH; subst pi; auto.
      * destruct n; discriminate.
    + intros [PREFIX [BELONGS [NTH LENGTH]]].
      exists instruction; rewrite NTH; auto.
  - intros [MEMBERS REST]; split.
    + intros ip MEMBER; apply MEMBERS in MEMBER; tauto.
    + split; [|exact REST].
      intro ip; rewrite MEMBERS; split.
      * intros [PREFIX [BELONGS [NTH LENGTH]]].
        exists instruction; rewrite NTH; auto.
      * intros [pi [NTH [PREFIX [BELONGS LENGTH]]]].
        destruct (TP.ip_nth ip) eqn:N; cbn in NTH.
        -- inversion NTH; subst pi; auto.
        -- destruct n; discriminate.
Qed.

Lemma lift_flatten_source points : TP.flatten_instrs parameters [before] points ->
  exists old_points, TP.flatten_instrs parameters [retiled_instruction] old_points /\
    Permutation (map lift_before points) old_points.
Proof.
  intro FLAT; apply singleton_flatten in FLAT as [MEMBERS [NODUP SORTED]].
  set (raw := map lift_before points).
  set (ordered := SelectionSort T.instr_point_np_ltb T.instr_point_np_eqb raw).
  assert (PERMUTE : Permutation raw ordered) by (apply selection_sort_perm).
  assert (RAW_MEMBERS : forall ip, In ip raw <-> valid_point retiled_instruction ip).
  { intro ip; split.
    - intros MEMBER; apply in_map_iff in MEMBER as [source [<- MEMBER]].
      apply MEMBERS in MEMBER; exact (proj1 (lift_before_shape MEMBER)).
    - intro VALID; apply in_map_iff; exists (project_old ip); split.
      + apply lift_project_old; exact VALID.
      + apply MEMBERS; apply project_old_shape; exact VALID. }
  assert (RAW_NODUP : NoDup raw).
  { assert (MAP_NODUP : forall xs, NoDup xs ->
      (forall ip, In ip xs -> valid_point before ip) -> NoDup (map lift_before xs)).
    { intros xs ND; induction ND as [|a xs NOT ND IH]; intro VALID; cbn; constructor.
      - intro MEMBER; apply in_map_iff in MEMBER as [source [SAME MEMBER]].
        apply (f_equal project_old) in SAME.
        rewrite (proj2 (lift_before_shape (VALID a (or_introl eq_refl)))) in SAME.
        rewrite (proj2 (lift_before_shape (VALID source (or_intror MEMBER)))) in SAME.
        subst source; contradiction.
      - apply IH; intros ip MEMBER; apply VALID; right; exact MEMBER. }
    apply MAP_NODUP; [exact NODUP|]. intros ip MEMBER; apply MEMBERS; exact MEMBER. }
  assert (ORDERED_MEMBERS : forall ip, In ip ordered <-> valid_point retiled_instruction ip).
  { intro ip; rewrite <- RAW_MEMBERS.
    split; eapply Permutation_in; [apply Permutation_sym; exact PERMUTE|exact PERMUTE]. }
  assert (ORDERED_NODUP : NoDup ordered) by (eapply Permutation_NoDup; eauto).
  assert (ORDERED_NODUPA : NoDupA TP.np_eq ordered).
  { eapply TP.belongs_to_implies_NoDupA_np with (pi := retiled_instruction)
      (len := (length parameters + TP.pi_depth retiled_instruction)%nat) (n := 0%nat).
    - intros ip MEMBER; apply ORDERED_MEMBERS in MEMBER; unfold valid_point in MEMBER; tauto.
    - exact ORDERED_NODUP. }
  exists ordered; split; [apply singleton_flatten|exact PERMUTE].
  split; [exact ORDERED_MEMBERS|]; split; [exact ORDERED_NODUP|].
  apply T.sortedb_instr_point_np_implies_sorted_np; [|exact ORDERED_NODUPA].
  apply selection_sort_sorted; apply T.instr_point_np_ltb_trans ||
    apply T.instr_point_np_eqb_trans || apply T.instr_point_np_eqb_refl ||
    apply T.instr_point_np_eqb_symm || apply T.instr_point_np_cmp_total ||
    apply T.instr_point_np_eqb_ltb_implies_ltb || apply T.instr_point_np_ltb_eqb_implies_ltb.
Qed.

Theorem before_to_retiled_old_progress initial final :
  TP.poly_instance_list_semantics parameters ([before],context,variables) initial final ->
  TP.poly_instance_list_semantics parameters ([retiled_instruction],context,variables) initial final.
Proof.
  intro RUN; inversion RUN as [env program instructions ctxt vars source target points ordered
    PROGRAM FLAT PERMUTE SORTED EXECUTION].
  injection PROGRAM as INSTRUCTIONS CONTEXT VARIABLES; subst instructions ctxt vars.
  pose proof (proj1 (singleton_flatten before points) FLAT) as [MEMBERS _].
  assert (ORDERED_VALID : forall ip, In ip ordered -> valid_point before ip).
  { intros ip MEMBER; apply MEMBERS; eapply Permutation_in;
      [apply Permutation_sym; exact PERMUTE|exact MEMBER]. }
  destruct (lift_flatten_source FLAT) as [old_points [OLD_FLAT OLD_PERMUTE]].
  eapply TP.PolyPointListSema with (ipl := old_points) (sorted_ipl := map lift_before ordered).
  - reflexivity.
  - exact OLD_FLAT.
  - transitivity (map lift_before points).
    + apply Permutation_sym; exact OLD_PERMUTE.
    + apply Permutation_map; exact PERMUTE.
  - apply T.sorted_sched_map_time_stamp_preserved; [|exact SORTED].
    intros ip MEMBER; apply lift_before_timestamp; apply ORDERED_VALID; exact MEMBER.
  - apply T.instr_point_list_semantics_map_preserved; [|exact EXECUTION].
    intros ip before_state after_state MEMBER; apply lift_before_execution;
      apply ORDERED_VALID; exact MEMBER.
Qed.
End SINGLE_STATEMENT.

Definition validate_memory_tiling_equivalence_internal (source candidate : TP.t)
    (witnesses : list statement_tiling_witness) :=
  if TV.TilingCheck.check_pprog_tiling_sourceb source candidate witnesses then
    let '(before_pis, context, variables) := source in
    let '(after_pis, _, _) := candidate in
    let retiled := (T.retiled_old_pinstrs (length context) before_pis after_pis witnesses, context, variables) in
    BIND backward <- TV.GeneralValidator.validate_general retiled candidate -;
    BIND forward <- TV.GeneralValidator.validate_general candidate retiled -;
    pure (backward && forward)
  else pure false.
Definition validate_memory_tiling_equivalence source candidate witnesses :=
  validate_memory_tiling_equivalence_internal
    (TV.outer_to_tiling_pprog source) (TV.outer_to_tiling_pprog candidate) witnesses.

Lemma tiling_equivalence_implies_checked source candidate witnesses :
  mayReturn (validate_memory_tiling_equivalence_internal source candidate witnesses) true ->
  mayReturn (TV.checked_tiling_validate source candidate witnesses) true.
Proof.
  unfold validate_memory_tiling_equivalence_internal, TV.checked_tiling_validate.
  destruct (TV.TilingCheck.check_pprog_tiling_sourceb source candidate witnesses);
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct source as [[before context] variables]; destruct candidate as [[after context'] variables'].
  intro CHECK; bind_imp_destruct CHECK backward BACKWARD.
  bind_imp_destruct CHECK forward FORWARD.
  apply mayReturn_pure in CHECK; apply andb_true_iff in CHECK as [BACK _]; subst backward; exact BACKWARD.
Qed.

Theorem guarded_memory_tiling_equivalence_refines source candidate witnesses initial final :
  mayReturn (validate_memory_tiling_equivalence source candidate witnesses) true ->
  GuardMemoryIRs.PolyLang.instance_list_semantics candidate initial final ->
  GuardMemoryIRs.PolyLang.instance_list_semantics source initial final.
Proof.
  intros CHECK RUN; apply guarded_memory_checked_tiling_refines with
    (candidate := candidate) (witnesses := witnesses); [|exact RUN].
  unfold validate_memory_tiling_equivalence in CHECK.
  exact (@tiling_equivalence_implies_checked
    (TV.outer_to_tiling_pprog source) (TV.outer_to_tiling_pprog candidate) witnesses CHECK).
Qed.

Theorem validated_single_tiling_progress_at before after witness context variables parameters initial final :
  length parameters = length context ->
  GuardMemoryInstr.NonAlias initial ->
  mayReturn (validate_memory_tiling_equivalence_internal
    ([before],context,variables) ([after],context,variables) [witness]) true ->
  TP.poly_instance_list_semantics parameters ([before],context,variables) initial final ->
  TP.poly_instance_list_semantics parameters ([after],context,variables) initial final.
Proof.
  intros ENVIRONMENT NONALIAS CHECK SOURCE.
  unfold validate_memory_tiling_equivalence_internal in CHECK.
  destruct (TV.TilingCheck.check_pprog_tiling_sourceb
    ([before],context,variables) ([after],context,variables) [witness]) eqn:STRUCTURE_CHECK.
  2: apply mayReturn_pure in CHECK; discriminate.
  bind_imp_destruct CHECK backward BACKWARD.
  bind_imp_destruct CHECK forward FORWARD.
  apply mayReturn_pure in CHECK; apply andb_true_iff in CHECK as [BACK FOR]; subst backward forward.
  destruct (@TV.TilingCheck.check_pprog_tiling_sourceb_sound
    ([before],context,variables) ([after],context,variables) [witness] STRUCTURE_CHECK)
    as [STRUCTURE [IDENTITIES [WELLFORMED [POSITIVES DEPTHS]]]].
  inversion IDENTITIES; inversion WELLFORMED; inversion POSITIVES; inversion DEPTHS; subst.
  match goal with WF : T.wf_statement_tiling_witness_with_param_dim (length context) witness |- _ =>
    rewrite <- ENVIRONMENT in WF end.
  assert (RETILED : TP.poly_instance_list_semantics parameters
    ([retiled_instruction before after witness parameters],context,variables) initial final).
  { eapply before_to_retiled_old_progress; eauto. }
  cbn -[TV.GeneralValidator.validate_tiling] in FORWARD.
  rewrite <- ENVIRONMENT in FORWARD.
  destruct (@TV.GeneralValidator.validate_tiling_correct'
    ([after],context,variables)
    ([retiled_instruction before after witness parameters],context,variables)
    context context [after] [retiled_instruction before after witness parameters]
    variables variables parameters initial final true FORWARD eq_refl eq_refl eq_refl
    (eq_sym ENVIRONMENT) NONALIAS RETILED) as [result [RUN SAME]].
  unfold GuardMemoryIRs.State.eq, GuardMemoryInstr.State.eq in SAME; subst result; exact RUN.
Qed.

Corollary validated_memory_single_tiling_progress_at before after witness context variables parameters initial final :
  length parameters = length context ->
  GuardMemoryInstr.NonAlias initial ->
  mayReturn (validate_memory_tiling_equivalence
    ([before],context,variables) ([after],context,variables) [witness]) true ->
  GuardMemoryIRs.PolyLang.poly_instance_list_semantics parameters
    ([before],context,variables) initial final ->
  GuardMemoryIRs.PolyLang.poly_instance_list_semantics parameters
    ([after],context,variables) initial final.
Proof.
  intros ENVIRONMENT NONALIAS CHECK RUN.
  apply (proj1 (@TV.outer_to_tiling_poly_instance_list_semantics_iff parameters
    ([after],context,variables) initial final)).
  eapply validated_single_tiling_progress_at; [exact ENVIRONMENT|exact NONALIAS|exact CHECK|].
  apply (proj2 (@TV.outer_to_tiling_poly_instance_list_semantics_iff parameters
    ([before],context,variables) initial final)); exact RUN.
Qed.

Print Assumptions lift_before_shape.
Print Assumptions lift_before_execution.
Print Assumptions before_to_retiled_old_progress.
Print Assumptions validated_single_tiling_progress_at.
Print Assumptions guarded_memory_tiling_equivalence_refines.
Print Assumptions validated_memory_single_tiling_progress_at.
