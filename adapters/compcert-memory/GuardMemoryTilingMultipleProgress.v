From Stdlib Require Import List Bool ZArith Lia Sorting.Sorted Sorting.Permutation Sorting.SetoidList.
From polcert.lib Require Import Linalg LinalgExt Misc ImpureAlarmConfig.
From polcert.src Require Import PointWitness TilingWitness SelectionSort.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryPolyhedral GuardMemoryTilingProgress.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Module TV := GuardMemoryTilingValidator.
Module T := TV.Tiling.
Module TP := T.PL.

Section INDEXED_STATEMENT.
Variable source candidate : list TP.PolyInstr.
Variable witnesses : list statement_tiling_witness.
Variable statement_number : nat.
Variable before after : TP.PolyInstr.
Variable witness : statement_tiling_witness.
Variable context : list TP.ident.
Variable variables : list (TP.ident * TP.Ty.t).
Variable parameters : list Z.
Hypothesis SOURCE_NTH : nth_error source statement_number = Some before.
Hypothesis CANDIDATE_NTH : nth_error candidate statement_number = Some after.
Hypothesis WITNESS_NTH : nth_error witnesses statement_number = Some witness.
Hypothesis STRUCTURE : T.tiling_rel_pprog_structure_source
  (source,context,variables) (candidate,context,variables)
  (map T.compiled_pinstr_tiling_witness witnesses).
Hypothesis ENVIRONMENT : length parameters = length context.
Hypothesis WELLFORMED : T.wf_statement_tiling_witness_with_param_dim (length parameters) witness.
Hypothesis POSITIVE : Forall (fun link => 0 < tl_tile_size link) (stw_links witness).
Hypothesis DEPTH : stw_point_dim witness = TP.pi_depth before.
Hypothesis IDENTITY : TP.pi_point_witness before = PSWIdentity (TP.pi_depth before).

Definition indexed_retiled_instruction := T.retiled_old_pinstr (length parameters) before after witness.
Definition indexed_project_old := T.before_of_retiled_old_point (length parameters)
  (length (stw_links witness)) before.
Definition indexed_lift_before (ip : TP.InstrPoint) : TP.InstrPoint :=
  let index := T.eval_pinstr_tiling_index_with_env parameters
    (skipn (length parameters) (TP.ip_index ip)) parameters (T.compiled_pinstr_tiling_witness witness) in
  {| TP.ip_nth := TP.ip_nth ip; TP.ip_index := index;
     TP.ip_transformation := TP.current_transformation_of indexed_retiled_instruction index;
     TP.ip_time_stamp := affine_product (TP.pi_schedule indexed_retiled_instruction) index;
     TP.ip_instruction := TP.pi_instr indexed_retiled_instruction;
     TP.ip_depth := TP.pi_depth indexed_retiled_instruction |}.
Definition indexed_valid_point (instruction : TP.PolyInstr) (ip : TP.InstrPoint) :=
  firstn (length parameters) (TP.ip_index ip) = parameters /\
  TP.belongs_to ip instruction /\ TP.ip_nth ip = statement_number /\
  length (TP.ip_index ip) = (length parameters + TP.pi_depth instruction)%nat.

Lemma indexed_statement_structure : T.tiling_rel_pinstr_structure_source (length parameters)
  before after (T.compiled_pinstr_tiling_witness witness).
Proof.
  rewrite ENVIRONMENT.
  eapply T.tiling_rel_pprog_structure_source_nth with
    (before_pis := source) (after_pis := candidate)
    (before_ctxt := context) (after_ctxt := context)
    (before_vars := variables) (after_vars := variables)
    (ws := map T.compiled_pinstr_tiling_witness witnesses) (n := statement_number).
  - exact STRUCTURE.
  - exact SOURCE_NTH.
  - exact CANDIDATE_NTH.
  - rewrite nth_error_map,WITNESS_NTH; reflexivity.
Qed.
Lemma indexed_after_depth : TP.pi_depth after = (TP.pi_depth before + length (stw_links witness))%nat.
Proof. pose proof indexed_statement_structure as [_ [D _]]; exact D. Qed.

Lemma indexed_lift_before_shape ip : indexed_valid_point before ip ->
  indexed_valid_point indexed_retiled_instruction (indexed_lift_before ip) /\ indexed_project_old (indexed_lift_before ip) = ip.
Proof.
  intros [PREFIX [BELONGS [NTH LENGTH]]].
  destruct (@T.tiling_rel_pprog_structure_source_before_point_has_retiled_old_preimage_nth
    source context variables candidate context variables witnesses statement_number before after witness
    parameters ip STRUCTURE SOURCE_NTH CANDIDATE_NTH WITNESS_NTH ENVIRONMENT WELLFORMED POSITIVE DEPTH
    PREFIX BELONGS NTH LENGTH) as [old [OLD_BELONGS [INDEX INVERSE]]].
  assert (OLD_NTH : TP.ip_nth old = TP.ip_nth ip).
  { apply (f_equal TP.ip_nth) in INVERSE; exact INVERSE. }
  assert (CANONICAL : old = indexed_lift_before ip).
  { destruct old as [nth index transformation timestamp instruction depth].
    destruct OLD_BELONGS as [DOMAIN [TRANSFORMATION [TIMESTAMP [INSTRUCTION DEPTH_OLD]]]].
    unfold indexed_lift_before, indexed_retiled_instruction; cbn in *.
    subst; reflexivity. }
  subst old; split; [|exact INVERSE].
  split.
  - unfold indexed_lift_before; cbn.
    unfold T.eval_pinstr_tiling_index_with_env, eval_statement_tiling_witness_with_env.
    rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r; reflexivity.
  - split; [exact OLD_BELONGS|]. split; [exact NTH|].
    unfold indexed_lift_before, T.eval_pinstr_tiling_index_with_env,
      eval_statement_tiling_witness_with_env, eval_statement_tiling_witness, lift_point,
      indexed_retiled_instruction; cbn.
    rewrite !app_length, eval_tile_links_length, skipn_length, indexed_after_depth.
    cbn; lia.
Qed.

Lemma indexed_project_old_shape ip : indexed_valid_point indexed_retiled_instruction ip -> indexed_valid_point before (indexed_project_old ip).
Proof.
  intros [PREFIX [BELONGS [NTH LENGTH]]].
  split; [apply T.before_of_retiled_old_point_prefix; exact PREFIX|].
  split.
  - eapply T.tiling_rel_pprog_structure_source_before_of_retiled_old_point_belongs_to_nth
      with (before_pis := source) (after_pis := candidate) (ws := witnesses)
      (before_ctxt := context) (after_ctxt := context)
      (before_vars := variables) (after_vars := variables) (n := statement_number);
      exact STRUCTURE || exact SOURCE_NTH || exact CANDIDATE_NTH || exact WITNESS_NTH || exact ENVIRONMENT || exact WELLFORMED || exact POSITIVE ||
      exact DEPTH || exact BELONGS || exact LENGTH || exact PREFIX || reflexivity.
  - split; [exact NTH|]. unfold indexed_project_old; cbn.
    apply T.before_index_of_retiled_old_length; [exact DEPTH|].
    unfold indexed_retiled_instruction in LENGTH; cbn in LENGTH; rewrite indexed_after_depth in LENGTH; lia.
Qed.

Lemma indexed_project_old_injective first second :
  indexed_valid_point indexed_retiled_instruction first -> indexed_valid_point indexed_retiled_instruction second ->
  indexed_project_old first = indexed_project_old second -> first = second.
Proof.
  intros [PF [BF [NF LF]]] [PS [BS [NS LS]]] SAME.
  eapply T.tiling_rel_pinstr_structure_source_before_of_retiled_old_point_injective
    with (env := parameters) (before := before) (after := after)
      (w := T.compiled_pinstr_tiling_witness witness);
    exact indexed_statement_structure || apply T.wf_compiled_pinstr_tiling_witness ||
    apply T.compiled_pinstr_tiling_witness_matches || exact WELLFORMED || exact POSITIVE ||
    exact DEPTH || exact BF || exact BS || exact LF || exact LS || exact PF || exact PS || exact SAME.
Qed.

Lemma indexed_lift_project_old ip : indexed_valid_point indexed_retiled_instruction ip -> indexed_lift_before (indexed_project_old ip) = ip.
Proof.
  intro VALID; pose proof (indexed_project_old_shape VALID) as SOURCE.
  destruct (indexed_lift_before_shape SOURCE) as [LIFT INVERSE].
  eapply indexed_project_old_injective; [exact LIFT|exact VALID|exact INVERSE].
Qed.

Lemma indexed_lift_before_execution ip initial final : indexed_valid_point before ip ->
  (TP.instr_point_sema ip initial final <-> TP.instr_point_sema (indexed_lift_before ip) initial final).
Proof.
  intro VALID; destruct (indexed_lift_before_shape VALID) as [[PREFIX [BELONGS [_ LENGTH]]] INVERSE].
  pose proof (@T.tiling_rel_pprog_structure_source_before_of_retiled_old_instr_semantics_iff_nth
    source context variables candidate context variables witnesses statement_number before after witness
    parameters (indexed_lift_before ip) initial final STRUCTURE SOURCE_NTH CANDIDATE_NTH WITNESS_NTH ENVIRONMENT
    WELLFORMED POSITIVE DEPTH IDENTITY BELONGS LENGTH PREFIX) as EQUIVALENT.
  unfold indexed_project_old in INVERSE; rewrite INVERSE in EQUIVALENT; symmetry; exact EQUIVALENT.
Qed.

Lemma indexed_lift_before_timestamp ip : indexed_valid_point before ip ->
  TP.ip_time_stamp (indexed_lift_before ip) = TP.ip_time_stamp ip.
Proof.
  intro VALID; destruct (indexed_lift_before_shape VALID) as [[PREFIX [BELONGS [_ LENGTH]]] INVERSE].
  pose proof (@T.tiling_rel_pinstr_structure_source_before_of_retiled_old_time_stamp
    parameters before after (T.compiled_pinstr_tiling_witness witness) (indexed_lift_before ip)
    indexed_statement_structure (T.wf_compiled_pinstr_tiling_witness witness) DEPTH BELONGS LENGTH PREFIX) as SAME.
  change (TP.ip_time_stamp (indexed_project_old (indexed_lift_before ip)) = TP.ip_time_stamp (indexed_lift_before ip)) in SAME.
  rewrite INVERSE in SAME; symmetry; exact SAME.
Qed.

End INDEXED_STATEMENT.
Print Assumptions indexed_lift_before_shape.
Print Assumptions indexed_lift_before_execution.

Definition multiple_program_point parameters instructions ip :=
  exists instruction, nth_error instructions (TP.ip_nth ip) = Some instruction /\
    indexed_valid_point (TP.ip_nth ip) parameters instruction ip.
Definition multiple_lift_before parameters source candidate witnesses ip :=
  match nth_error source (TP.ip_nth ip),nth_error candidate (TP.ip_nth ip),
        nth_error witnesses (TP.ip_nth ip) with
  | Some before,Some after,Some witness => indexed_lift_before before after witness parameters ip
  | _,_,_ => ip end.
Definition multiple_project_old (parameters : list Z) source witnesses :=
  T.before_of_retiled_old_pprog_point (length parameters) source witnesses.
Definition multiple_retiled (parameters : list Z) source candidate witnesses :=
  T.retiled_old_pinstrs (length parameters) source candidate witnesses.

Section MULTIPLE_STATEMENTS.
Variable source candidate : list TP.PolyInstr.
Variable witnesses : list statement_tiling_witness.
Variable context : list TP.ident.
Variable variables : list (TP.ident * TP.Ty.t).
Variable parameters : list Z.
Hypothesis CHECK : TV.TilingCheck.check_pprog_tiling_sourceb
  (source,context,variables) (candidate,context,variables) witnesses = true.
Hypothesis ENVIRONMENT : length parameters = length context.

Lemma multiple_structure : T.tiling_rel_pprog_structure_source
  (source,context,variables) (candidate,context,variables)
  (map T.compiled_pinstr_tiling_witness witnesses).
Proof. exact (proj1 (TV.TilingCheck.check_pprog_tiling_sourceb_sound _ _ _ CHECK)). Qed.
Lemma multiple_lengths : length source = length candidate /\ length source = length witnesses.
Proof.
  pose proof (@T.tiling_rel_pprog_structure_source_lengths source context variables candidate context variables
    (map T.compiled_pinstr_tiling_witness witnesses) multiple_structure) as [FIRST SECOND].
  rewrite map_length in SECOND; auto; lia.
Qed.
Lemma multiple_metadata n before witness :
  nth_error source n = Some before -> nth_error witnesses n = Some witness ->
  T.wf_statement_tiling_witness_with_param_dim (length parameters) witness /\
  Forall (fun link => 0 < tl_tile_size link) (stw_links witness) /\
  stw_point_dim witness = TP.pi_depth before /\
  TP.pi_point_witness before = PSWIdentity (TP.pi_depth before).
Proof.
  intros BEFORE WITNESS.
  destruct (TV.TilingCheck.check_pprog_tiling_sourceb_sound _ _ _ CHECK)
    as [_ [IDENTITIES [WELLFORMED [POSITIVE DEPTH]]]].
  rewrite <- ENVIRONMENT in WELLFORMED.
  split; [|split; [|split]].
  - rewrite Forall_forall in WELLFORMED; apply WELLFORMED; eapply nth_error_In; exact WITNESS.
  - rewrite Forall_forall in POSITIVE; apply POSITIVE; eapply nth_error_In; exact WITNESS.
  - exact (@Misc.Forall2_nth_error_both _ _ _ n source witnesses before witness DEPTH BEFORE WITNESS).
  - rewrite Forall_forall in IDENTITIES; apply IDENTITIES; eapply nth_error_In; exact BEFORE.
Qed.
Lemma multiple_lookup n : (n < length source)%nat ->
  exists before after witness, nth_error source n = Some before /\ nth_error candidate n = Some after /\
    nth_error witnesses n = Some witness.
Proof.
  intro BOUND; pose proof multiple_lengths as [FIRST SECOND].
  destruct (nth_error source n) as [before|] eqn:BEFORE;
    [|apply nth_error_None in BEFORE; lia].
  destruct (nth_error candidate n) as [after|] eqn:AFTER;
    [|apply nth_error_None in AFTER; lia].
  destruct (nth_error witnesses n) as [witness|] eqn:WITNESS;
    [|apply nth_error_None in WITNESS; lia].
  exists before,after,witness; auto.
Qed.
Lemma multiple_source_lookup ip : multiple_program_point parameters source ip ->
  exists before after witness,
    nth_error source (TP.ip_nth ip) = Some before /\
    nth_error candidate (TP.ip_nth ip) = Some after /\
    nth_error witnesses (TP.ip_nth ip) = Some witness /\
    indexed_valid_point (TP.ip_nth ip) parameters before ip.
Proof.
  intros [instruction [NTH VALID]].
  destruct (multiple_lookup (TP.nth_error_Some' _ _ _ NTH)) as [before [after [witness [BEFORE [AFTER WITNESS]]]]].
  rewrite NTH in BEFORE; inversion BEFORE; subst before; eauto 8.
Qed.
Lemma multiple_retiled_length : length (multiple_retiled parameters source candidate witnesses) = length source.
Proof. apply T.retiled_old_pinstrs_preserve_length; pose proof multiple_lengths; tauto. Qed.
Lemma multiple_target_lookup ip :
  multiple_program_point parameters (multiple_retiled parameters source candidate witnesses) ip ->
  exists before after witness,
    nth_error source (TP.ip_nth ip) = Some before /\
    nth_error candidate (TP.ip_nth ip) = Some after /\
    nth_error witnesses (TP.ip_nth ip) = Some witness /\
    indexed_valid_point (TP.ip_nth ip) parameters (indexed_retiled_instruction before after witness parameters) ip.
Proof.
  intros [instruction [NTH VALID]].
  assert (BOUND : (TP.ip_nth ip < length source)%nat).
  { rewrite <- multiple_retiled_length; exact (TP.nth_error_Some' _ _ _ NTH). }
  destruct (multiple_lookup BOUND) as [before [after [witness [BEFORE [AFTER WITNESS]]]]].
  pose proof (@T.nth_error_retiled_old_pinstrs (length parameters) source candidate witnesses (TP.ip_nth ip)
    before after witness BEFORE AFTER WITNESS) as RETILED.
  change (nth_error (multiple_retiled parameters source candidate witnesses) (TP.ip_nth ip) =
    Some (indexed_retiled_instruction before after witness parameters)) in RETILED.
  rewrite NTH in RETILED; inversion RETILED; subst instruction; eauto 8.
Qed.

Lemma multiple_lift_shape ip : multiple_program_point parameters source ip ->
  multiple_program_point parameters (multiple_retiled parameters source candidate witnesses)
    (multiple_lift_before parameters source candidate witnesses ip) /\
  multiple_project_old parameters source witnesses (multiple_lift_before parameters source candidate witnesses ip) = ip.
Proof.
  intro VALID; destruct (multiple_source_lookup VALID) as [before [after [witness [BEFORE [AFTER [WITNESS POINT]]]]]].
  destruct (multiple_metadata (TP.ip_nth ip) BEFORE WITNESS) as [WF [POS [DEPTH IDENTITY]]].
  unfold multiple_lift_before; rewrite BEFORE,AFTER,WITNESS.
  destruct (@indexed_lift_before_shape source candidate witnesses (TP.ip_nth ip) before after witness
    context variables parameters BEFORE AFTER WITNESS multiple_structure ENVIRONMENT WF POS DEPTH ip POINT)
    as [LIFT INVERSE].
  split.
  - exists (indexed_retiled_instruction before after witness parameters); split; [|exact LIFT].
    unfold indexed_lift_before; cbn.
    apply T.nth_error_retiled_old_pinstrs; assumption.
  - unfold multiple_project_old,T.before_of_retiled_old_pprog_point.
    change (match nth_error source (TP.ip_nth ip),nth_error witnesses (TP.ip_nth ip) with
      | Some pi,Some w => T.before_of_retiled_old_point (length parameters) (length (stw_links w)) pi
          (indexed_lift_before before after witness parameters ip)
      | _,_ => indexed_lift_before before after witness parameters ip end = ip).
    rewrite BEFORE,WITNESS; exact INVERSE.
Qed.
Lemma multiple_project_shape ip :
  multiple_program_point parameters (multiple_retiled parameters source candidate witnesses) ip ->
  multiple_program_point parameters source (multiple_project_old parameters source witnesses ip).
Proof.
  intro VALID; destruct (multiple_target_lookup VALID) as [before [after [witness [BEFORE [AFTER [WITNESS POINT]]]]]].
  destruct (multiple_metadata (TP.ip_nth ip) BEFORE WITNESS) as [WF [POS [DEPTH IDENTITY]]].
  unfold multiple_project_old,T.before_of_retiled_old_pprog_point; rewrite BEFORE,WITNESS.
  exists before; split; [exact BEFORE|].
  exact (@indexed_project_old_shape source candidate witnesses (TP.ip_nth ip) before after witness
    context variables parameters BEFORE AFTER WITNESS multiple_structure ENVIRONMENT WF POS DEPTH ip POINT).
Qed.
Lemma multiple_lift_project ip :
  multiple_program_point parameters (multiple_retiled parameters source candidate witnesses) ip ->
  multiple_lift_before parameters source candidate witnesses (multiple_project_old parameters source witnesses ip) = ip.
Proof.
  intro VALID; destruct (multiple_target_lookup VALID) as [before [after [witness [BEFORE [AFTER [WITNESS POINT]]]]]].
  destruct (multiple_metadata (TP.ip_nth ip) BEFORE WITNESS) as [WF [POS [DEPTH IDENTITY]]].
  unfold multiple_project_old,T.before_of_retiled_old_pprog_point; rewrite BEFORE,WITNESS.
  unfold multiple_lift_before; change (TP.ip_nth (T.before_of_retiled_old_point (length parameters)
    (length (stw_links witness)) before ip)) with (TP.ip_nth ip); rewrite BEFORE,AFTER,WITNESS.
  exact (@indexed_lift_project_old source candidate witnesses (TP.ip_nth ip) before after witness
    context variables parameters BEFORE AFTER WITNESS multiple_structure ENVIRONMENT WF POS DEPTH ip POINT).
Qed.
Lemma multiple_lift_execution ip initial final : multiple_program_point parameters source ip ->
  (TP.instr_point_sema ip initial final <-> TP.instr_point_sema
    (multiple_lift_before parameters source candidate witnesses ip) initial final).
Proof.
  intro VALID; destruct (multiple_source_lookup VALID) as [before [after [witness [BEFORE [AFTER [WITNESS POINT]]]]]].
  destruct (multiple_metadata (TP.ip_nth ip) BEFORE WITNESS) as [WF [POS [DEPTH IDENTITY]]].
  unfold multiple_lift_before; rewrite BEFORE,AFTER,WITNESS.
  exact (@indexed_lift_before_execution source candidate witnesses (TP.ip_nth ip) before after witness
    context variables parameters BEFORE AFTER WITNESS multiple_structure ENVIRONMENT WF POS DEPTH IDENTITY
    ip initial final POINT).
Qed.
Lemma multiple_lift_timestamp ip : multiple_program_point parameters source ip ->
  TP.ip_time_stamp (multiple_lift_before parameters source candidate witnesses ip) = TP.ip_time_stamp ip.
Proof.
  intro VALID; destruct (multiple_source_lookup VALID) as [before [after [witness [BEFORE [AFTER [WITNESS POINT]]]]]].
  destruct (multiple_metadata (TP.ip_nth ip) BEFORE WITNESS) as [WF [POS [DEPTH IDENTITY]]].
  unfold multiple_lift_before; rewrite BEFORE,AFTER,WITNESS.
  exact (@indexed_lift_before_timestamp source candidate witnesses (TP.ip_nth ip) before after witness
    context variables parameters BEFORE AFTER WITNESS multiple_structure ENVIRONMENT WF POS DEPTH ip POINT).
Qed.
End MULTIPLE_STATEMENTS.
Print Assumptions multiple_lift_shape.
Print Assumptions multiple_lift_execution.

Lemma multiple_flatten_spec parameters instructions points :
  TP.flatten_instrs parameters instructions points <->
  (forall ip, In ip points <-> multiple_program_point parameters instructions ip) /\
  NoDup points /\ Sorted TP.np_lt points.
Proof.
  unfold TP.flatten_instrs; split.
  - intros [_ [MEMBERS REST]]; split; [|exact REST].
    intro ip; rewrite MEMBERS; unfold multiple_program_point,indexed_valid_point; split.
    + intros [instruction [NTH [PREFIX [BELONG LENGTH]]]].
      exists instruction; split; [exact NTH|]; split; [exact PREFIX|]; split; [exact BELONG|]; auto.
    + intros [instruction [NTH [PREFIX [BELONG [_ LENGTH]]]]]; exists instruction; auto.
  - intros [MEMBERS REST]; split.
    + intros ip MEMBER; apply MEMBERS in MEMBER as [instruction [_ [PREFIX _]]]; exact PREFIX.
    + split; [|exact REST].
      intro ip; rewrite MEMBERS; unfold multiple_program_point,indexed_valid_point; split.
      * intros [instruction [NTH [PREFIX [BELONG [_ LENGTH]]]]]; exists instruction; auto.
      * intros [instruction [NTH [PREFIX [BELONG LENGTH]]]].
        exists instruction; split; [exact NTH|]; split; [exact PREFIX|]; split; [exact BELONG|]; auto.
Qed.
Lemma multiple_program_np_unique parameters instructions first second :
  multiple_program_point parameters instructions first -> multiple_program_point parameters instructions second ->
  TP.np_eq first second -> first = second.
Proof.
  intros [pi [NTH [PREF [BELONG [_ LENGTH]]]]] [pi' [NTH' [PREF' [BELONG' [_ LENGTH']]]]] [NUMBER COMPARE].
  rewrite <- NUMBER in NTH'; rewrite NTH in NTH'; inversion NTH'; subst pi'.
  assert (INDEX : TP.ip_index first = TP.ip_index second).
  { apply same_length_eq; [rewrite LENGTH,LENGTH'; reflexivity|].
    rewrite <- is_eq_veq; apply is_eq_iff_cmp_eq; exact COMPARE. }
  destruct BELONG as [_ [TRANS [TIME [INSTRUCTION DEPTH]]]].
  destruct BELONG' as [_ [TRANS' [TIME' [INSTRUCTION' DEPTH']]]].
  destruct first,second; cbn in *; subst; reflexivity.
Qed.
Lemma multiple_program_nodupA parameters instructions points :
  (forall ip, In ip points -> multiple_program_point parameters instructions ip) ->
  NoDup points -> NoDupA TP.np_eq points.
Proof.
  intros VALID NODUP; induction NODUP as [|point points ABSENT NODUP IH]; constructor.
  - intro PRESENT; apply InA_alt in PRESENT as [other [SAME MEMBER]].
    assert (EQ : point = other) by (eapply multiple_program_np_unique; [apply VALID; left; reflexivity|
      apply VALID; right; exact MEMBER|exact SAME]); subst other; contradiction.
  - apply IH; intros ip MEMBER; apply VALID; right; exact MEMBER.
Qed.

Section GLOBAL_PROGRESS.
Variable source candidate : list TP.PolyInstr.
Variable witnesses : list statement_tiling_witness.
Variable context : list TP.ident.
Variable variables : list (TP.ident * TP.Ty.t).
Variable parameters : list Z.
Hypothesis CHECK : TV.TilingCheck.check_pprog_tiling_sourceb
  (source,context,variables) (candidate,context,variables) witnesses = true.
Hypothesis ENVIRONMENT : length parameters = length context.
Let lift := multiple_lift_before parameters source candidate witnesses.
Let project := multiple_project_old parameters source witnesses.
Let retiled := multiple_retiled parameters source candidate witnesses.

Lemma multiple_lift_flatten points : TP.flatten_instrs parameters source points ->
  exists old_points, TP.flatten_instrs parameters retiled old_points /\ Permutation (map lift points) old_points.
Proof.
  intro FLAT; apply multiple_flatten_spec in FLAT as [MEMBERS [NODUP SORTED]].
  assert (SHAPE : forall ip, multiple_program_point parameters source ip ->
    multiple_program_point parameters retiled (lift ip) /\ project (lift ip) = ip).
  { intros ip VALID; exact (@multiple_lift_shape source candidate witnesses context variables parameters
      CHECK ENVIRONMENT ip VALID). }
  assert (BACK : forall ip, multiple_program_point parameters retiled ip ->
    multiple_program_point parameters source (project ip) /\ lift (project ip) = ip).
  { intros ip VALID; split.
    - exact (@multiple_project_shape source candidate witnesses context variables parameters CHECK ENVIRONMENT ip VALID).
    - exact (@multiple_lift_project source candidate witnesses context variables parameters CHECK ENVIRONMENT ip VALID). }
  set (raw := map lift points).
  set (ordered := SelectionSort T.instr_point_np_ltb T.instr_point_np_eqb raw).
  assert (PERMUTE : Permutation raw ordered) by apply selection_sort_perm.
  assert (RAW_MEMBERS : forall ip, In ip raw <-> multiple_program_point parameters retiled ip).
  { intro ip; split.
    - intro MEMBER; apply in_map_iff in MEMBER as [old [<- MEMBER]].
      apply MEMBERS in MEMBER; exact (proj1 (SHAPE old MEMBER)).
    - intro VALID; apply in_map_iff; exists (project ip); split;
        [exact (proj2 (BACK ip VALID))|apply MEMBERS; exact (proj1 (BACK ip VALID))]. }
  assert (RAW_NODUP : NoDup raw).
  { assert (MAP_NODUP : forall xs, NoDup xs ->
      (forall ip, In ip xs -> multiple_program_point parameters source ip) -> NoDup (map lift xs)).
    { intros xs ND; induction ND as [|a xs ABSENT ND IH]; intro VALID; cbn; constructor.
      - intro MEMBER; apply in_map_iff in MEMBER as [old [SAME MEMBER]].
        apply (f_equal project) in SAME.
        rewrite (proj2 (SHAPE old (VALID old (or_intror MEMBER)))) in SAME.
        rewrite (proj2 (SHAPE a (VALID a (or_introl eq_refl)))) in SAME.
        subst old; contradiction.
      - apply IH; intros ip MEMBER; apply VALID; right; exact MEMBER. }
    apply MAP_NODUP; [exact NODUP|]. intros ip MEMBER; apply MEMBERS; exact MEMBER. }
  assert (ORDERED_MEMBERS : forall ip, In ip ordered <-> multiple_program_point parameters retiled ip).
  { intro ip; rewrite <- RAW_MEMBERS; split; eapply Permutation_in;
      [apply Permutation_sym; exact PERMUTE|exact PERMUTE]. }
  assert (ORDERED_NODUP : NoDup ordered) by (eapply Permutation_NoDup; eauto).
  assert (ORDERED_NODUPA : NoDupA TP.np_eq ordered).
  { eapply multiple_program_nodupA; [|exact ORDERED_NODUP]. intros ip MEMBER; apply ORDERED_MEMBERS; exact MEMBER. }
  exists ordered; split; [apply multiple_flatten_spec|exact PERMUTE].
  split; [exact ORDERED_MEMBERS|]; split; [exact ORDERED_NODUP|].
  apply T.sortedb_instr_point_np_implies_sorted_np; [|exact ORDERED_NODUPA].
  apply selection_sort_sorted; apply T.instr_point_np_ltb_trans ||
    apply T.instr_point_np_eqb_trans || apply T.instr_point_np_eqb_refl ||
    apply T.instr_point_np_eqb_symm || apply T.instr_point_np_cmp_total ||
    apply T.instr_point_np_eqb_ltb_implies_ltb || apply T.instr_point_np_ltb_eqb_implies_ltb.
Qed.
Theorem before_to_retiled_multiple_progress initial final :
  TP.poly_instance_list_semantics parameters (source,context,variables) initial final ->
  TP.poly_instance_list_semantics parameters (retiled,context,variables) initial final.
Proof.
  intro RUN; inversion RUN as [env program instructions ctxt vars before after points ordered
    PROGRAM FLAT PERMUTE SORTED EXECUTION].
  injection PROGRAM as INSTRUCTIONS CONTEXT VARIABLES; subst instructions ctxt vars.
  pose proof (proj1 (multiple_flatten_spec parameters source points) FLAT) as [MEMBERS _].
  assert (ORDERED_VALID : forall ip, In ip ordered -> multiple_program_point parameters source ip).
  { intros ip MEMBER; apply MEMBERS; eapply Permutation_in;
      [apply Permutation_sym; exact PERMUTE|exact MEMBER]. }
  destruct (multiple_lift_flatten FLAT) as [old_points [OLD_FLAT OLD_PERMUTE]].
  eapply TP.PolyPointListSema with (ipl := old_points) (sorted_ipl := map lift ordered).
  - reflexivity.
  - exact OLD_FLAT.
  - transitivity (map lift points).
    + apply Permutation_sym; exact OLD_PERMUTE.
    + apply Permutation_map; exact PERMUTE.
  - apply T.sorted_sched_map_time_stamp_preserved; [|exact SORTED].
    intros ip MEMBER; exact (@multiple_lift_timestamp source candidate witnesses context variables parameters
      CHECK ENVIRONMENT ip (ORDERED_VALID ip MEMBER)).
  - apply T.instr_point_list_semantics_map_preserved; [|exact EXECUTION].
    intros ip before_state after_state MEMBER; exact (@multiple_lift_execution source candidate witnesses context variables
      parameters CHECK ENVIRONMENT ip before_state after_state (ORDERED_VALID ip MEMBER)).
Qed.
End GLOBAL_PROGRESS.
Print Assumptions before_to_retiled_multiple_progress.

Theorem validated_multiple_tiling_progress_at source candidate witnesses context variables parameters initial final :
  length parameters = length context -> GuardMemoryInstr.NonAlias initial ->
  mayReturn (validate_memory_tiling_equivalence_internal (source,context,variables)
    (candidate,context,variables) witnesses) true ->
  TP.poly_instance_list_semantics parameters (source,context,variables) initial final ->
  TP.poly_instance_list_semantics parameters (candidate,context,variables) initial final.
Proof.
  intros ENVIRONMENT NONALIAS CHECK SOURCE.
  unfold validate_memory_tiling_equivalence_internal in CHECK.
  destruct (TV.TilingCheck.check_pprog_tiling_sourceb (source,context,variables) (candidate,context,variables) witnesses)
    eqn:STRUCTURE_CHECK.
  2: apply mayReturn_pure in CHECK; discriminate.
  bind_imp_destruct CHECK backward BACKWARD; bind_imp_destruct CHECK forward FORWARD.
  apply mayReturn_pure in CHECK; apply andb_true_iff in CHECK as [BACK FOR]; subst backward forward.
  assert (RETILED : TP.poly_instance_list_semantics parameters
    (multiple_retiled parameters source candidate witnesses,context,variables) initial final).
  { eapply before_to_retiled_multiple_progress; eauto. }
  cbn -[TV.GeneralValidator.validate_tiling] in FORWARD.
  rewrite <- ENVIRONMENT in FORWARD.
  destruct (@TV.GeneralValidator.validate_tiling_correct'
    (candidate,context,variables) (multiple_retiled parameters source candidate witnesses,context,variables)
    context context candidate (multiple_retiled parameters source candidate witnesses)
    variables variables parameters initial final true FORWARD eq_refl eq_refl eq_refl
    (eq_sym ENVIRONMENT) NONALIAS RETILED) as [result [RUN SAME]].
  unfold GuardMemoryIRs.State.eq,GuardMemoryInstr.State.eq in SAME; subst result; exact RUN.
Qed.
Corollary validated_memory_multiple_tiling_progress_at source candidate witnesses context variables parameters initial final :
  length parameters = length context -> GuardMemoryInstr.NonAlias initial ->
  mayReturn (validate_memory_tiling_equivalence (source,context,variables) (candidate,context,variables) witnesses) true ->
  GuardMemoryIRs.PolyLang.poly_instance_list_semantics parameters (source,context,variables) initial final ->
  GuardMemoryIRs.PolyLang.poly_instance_list_semantics parameters (candidate,context,variables) initial final.
Proof.
  intros ENVIRONMENT NONALIAS CHECK SOURCE.
  apply (proj1 (@TV.outer_to_tiling_poly_instance_list_semantics_iff parameters
    (candidate,context,variables) initial final)).
  eapply validated_multiple_tiling_progress_at; [exact ENVIRONMENT|exact NONALIAS|exact CHECK|].
  apply (proj2 (@TV.outer_to_tiling_poly_instance_list_semantics_iff parameters
    (source,context,variables) initial final)); exact SOURCE.
Qed.
Print Assumptions validated_memory_multiple_tiling_progress_at.
