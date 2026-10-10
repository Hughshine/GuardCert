From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightGlobalScope ClightTempFootprint.
From GuardMemory Require Import GuardMemoryDynamicTensorLayout GuardMemoryDoubleSourceInstruction
  GuardMemoryDoubleSourceTransport GuardMemoryDoubleAffineSourceAccess GuardMemoryDoubleSourceTreeData GuardMemoryDoubleSourceTreeDecode
  GuardMemoryDoubleSourceTreeCertificates GuardMemoryDoubleSourceTreeState GuardMemoryDoubleTreeGuarded
  GuardMemoryDoubleTreeCaptureData GuardMemoryDoubleTreeCacheFrame GuardMemoryDoubleNestedBackend
  GuardMemoryDoubleTensorBackend.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition double_tree_layout_span_check tree := forallb
  (fun entry=>8*tensor_volume (snd entry)<=?Ptrofs.modulus) (PTree.elements (double_source_tree_layouts tree)).
Theorem double_tree_layout_span_check_sound tree ge locals :
  double_tree_layout_span_check tree=true -> locals_avoid (double_tree_public_globals tree) locals ->
  double_tensor_static ge locals (double_source_tree_layouts tree).
Proof.
  intros CHECK LOCAL identifier dimensions LAYOUT.
  pose proof (@PTree.elements_correct (list Z) _ identifier dimensions LAYOUT) as MEMBER; split.
  - apply LOCAL; unfold double_tree_public_globals; apply in_or_app; right.
    apply in_map_iff; exists (identifier,dimensions); split; [reflexivity|exact MEMBER].
  - unfold double_tree_layout_span_check in CHECK; apply forallb_forall with (x:=(identifier,dimensions)) in CHECK;
      [cbn [snd] in CHECK; apply Z.leb_le; exact CHECK|exact MEMBER].
Qed.
Theorem checked_double_tree_public_scope p source tree locals :
  checked_double_source_tree p source=Some tree -> locals_avoid (double_tree_public_globals tree) locals ->
  double_source_tree_scope tree locals /\ locals_avoid (double_source_tree_headers tree) locals.
Proof.
  intros CHECK LOCAL; split.
  - intros instruction POINT identifier MEMBER; unfold double_source_instruction_globals in MEMBER.
    apply in_map_iff in MEMBER as [access [SAME ACCESS]]; subst identifier.
    apply LOCAL; unfold double_tree_public_globals; apply in_or_app; right.
    apply in_map_iff; exists (fst (double_affine_source_function access),double_affine_source_dimensions access).
    split; [reflexivity|apply PTree.elements_correct; eapply checked_double_source_tree_layout_certificate; eassumption].
  - intros identifier MEMBER; apply LOCAL; unfold double_tree_public_globals; apply in_or_app; left; exact MEMBER.
Qed.
Definition double_tree_profile_check tree (lower upper : ident -> Z) := forallb
  (fun header=>(Int.min_signed<=?lower header) && (lower header<=?upper header) && (upper header<=?Int.max_signed))
  (double_source_tree_parameters tree).
Theorem double_tree_profile_check_sound tree lower upper : double_tree_profile_check tree lower upper=true ->
  forall header, In header (double_source_tree_headers tree) ->
    Int.min_signed<=lower header<=Int.max_signed /\ Int.min_signed<=upper header<=Int.max_signed.
Proof.
  intros CHECK header MEMBER; unfold double_tree_profile_check in CHECK.
  apply forallb_forall with (x:=header) in CHECK; [|apply double_source_tree_parameter_membership; exact MEMBER].
  apply andb_true_iff in CHECK as [CHECK MAXIMUM]; apply andb_true_iff in CHECK as [MINIMUM ORDER].
  apply Z.leb_le in MINIMUM,ORDER,MAXIMUM; lia.
Qed.

Lemma double_tree_distinct_cache_values (headers : list ident) (cache : ident -> ident) :
  NoDup (map cache headers) -> forall first second,
  In first headers -> In second headers -> cache first=cache second -> first=second.
Proof.
  induction headers as [|header headers IH]; intros DISTINCT first second FIRST SECOND SAME; [contradiction|].
  inversion DISTINCT as [|key keys FRESH TAIL]; subst key keys.
  destruct FIRST as [FIRST|FIRST],SECOND as [SECOND|SECOND].
  - congruence.
  - subst first; exfalso; apply FRESH; rewrite SAME; apply in_map; exact SECOND.
  - subst second; exfalso; apply FRESH; rewrite <- SAME; apply in_map; exact FIRST.
  - eapply IH; eassumption.
Qed.
Definition double_tree_resources source tree cache flag live := DoubleNested.N.fresh_names
  (flag::map cache (double_source_tree_parameters tree)) ((statement_temps source++live)++double_source_tree_writes tree).
Theorem double_tree_resources_sound source tree cache flag live : double_tree_resources source tree cache flag live=true ->
  double_tree_cache_distinct (double_source_tree_headers tree) cache /\
  (forall header, In header (double_source_tree_headers tree) -> cache header<>flag) /\
  (forall header, In header (double_source_tree_headers tree) -> ~ In (cache header) (double_source_tree_writes tree)) /\
  (forall key, In key (statement_temps source++live) -> ~ In key (double_tree_capture_private tree cache flag)).
Proof.
  intro CHECK; destruct (DoubleNested.N.fresh_names_sound _ _ CHECK) as [DISTINCT FRESH].
  apply NoDup_cons_iff in DISTINCT as [FLAG CACHES].
  assert (MEMBERSHIP : forall header, In header (double_source_tree_headers tree) -> In header (double_source_tree_parameters tree)).
  { intros header MEMBER; apply double_source_tree_parameter_membership; exact MEMBER. }
  split.
  - intros first second FIRST SECOND SAME; eapply double_tree_distinct_cache_values;
      [exact CACHES|apply MEMBERSHIP; exact FIRST|apply MEMBERSHIP; exact SECOND|exact SAME].
  - split.
    + intros header MEMBER SAME; apply FLAG; rewrite <- SAME; apply in_map,MEMBERSHIP; exact MEMBER.
    + split.
      * intros header MEMBER WRITE; apply (FRESH (cache header) ltac:(right; apply in_map,MEMBERSHIP; exact MEMBER)).
        apply in_or_app; right; exact WRITE.
      * intros key PUBLIC RESOURCE; apply (FRESH key); [|apply in_or_app; left; exact PUBLIC].
        destruct RESOURCE as [SAME|MEMBER]; [left; exact SAME|right].
        apply in_map_iff in MEMBER as [header [SAME MEMBER]]; subst key; apply in_map,MEMBERSHIP; exact MEMBER.
Qed.

Print Assumptions double_tree_layout_span_check_sound.
Print Assumptions checked_double_tree_public_scope.
Print Assumptions double_tree_profile_check_sound.
Print Assumptions double_tree_distinct_cache_values.
Print Assumptions double_tree_resources_sound.
