From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryLongPositiveCapture
  GuardMemoryRectangularCapture GuardMemoryDoubleRectangularNestSource.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Successful dependent capture produces the same observations used by the
    concrete source/model bridge. This theorem does not license the reads. *)
Definition rectangular_capture_observation ge locals memory after step
  (observation : ident*(block*nat)) :=
  fst observation=rectangular_capture_header step /\
  double_global_binding ge locals (fst observation) (fst (snd observation)) /\
  Mem.load Mint64 memory (fst (snd observation)) 0=
    Some (Vlong (Int64.repr (Z.of_nat (snd (snd observation))))) /\
  1<=Z.of_nat (snd (snd observation))<=rectangular_capture_limit step /\
  Z.of_nat (snd (snd observation))<=Int64.max_signed /\
  after ! (rectangular_capture_cache step)=
    Some (Vint (Int.repr (Z.of_nat (snd (snd observation))))).

Theorem rectangular_capture_accepted_observations ge locals memory flag steps temps after :
  rectangular_capture_receipt ge locals memory flag steps temps after true ->
  NoDup (map rectangular_capture_cache steps) -> ~ In flag (map rectangular_capture_cache steps) ->
  exists observations, Forall2 (rectangular_capture_observation ge locals memory after) steps observations.
Proof.
  intro RECEIPT; remember true as accepted eqn:TRUE; revert TRUE.
  induction RECEIPT; intros TRUE DISTINCT FLAG; [exists []; constructor|discriminate|].
  subst accepted; inversion DISTINCT as [|cache caches FRESH TAIL]; subst cache caches.
  assert (CHILD_FLAG : ~ In flag (map rectangular_capture_cache steps))
    by (intro MEMBER; apply FLAG; right; exact MEMBER).
  destruct (IHRECEIPT eq_refl TAIL CHILD_FLAG) as [observations OBSERVATIONS].
  assert (RANGE : 1<=Int64.signed word<=rectangular_capture_limit step).
  { unfold rectangular_capture_step_accept in H2; apply memory_long_positive_accept_spec; exact H2. }
  assert (COUNT : Z.of_nat (Z.to_nat (Int64.signed word))=Int64.signed word) by (apply Z2Nat.id; lia).
  exists ((rectangular_capture_header step,(bound_block,Z.to_nat (Int64.signed word)))::observations).
  constructor; [|exact OBSERVATIONS].
  unfold rectangular_capture_observation; cbn [fst snd]; rewrite COUNT.
  split; [reflexivity|split; [exact H|split]].
  - rewrite Int64.repr_signed; exact H0.
  - split; [exact RANGE|split; [pose proof (Int64.signed_range word); lia|]].
    rewrite (@rectangular_capture_receipt_frame ge locals memory flag steps _ after true RECEIPT
      (rectangular_capture_cache step) ltac:(intro SAME; subst; apply FLAG; left; reflexivity) FRESH).
    exact (proj1 (@memory_long_positive_captured_cache temps (rectangular_capture_cache step) flag word
      (rectangular_capture_limit step) ltac:(intro SAME; subst; apply FLAG; left; reflexivity) H1 H2)).
Qed.

Theorem rectangular_capture_observations_loads ge locals memory after steps observations :
  Forall2 (rectangular_capture_observation ge locals memory after) steps observations ->
  double_rectangular_observed_loads observations memory /\
  (forall header bound_block count, In (header,(bound_block,count)) observations ->
    double_global_binding ge locals header bound_block).
Proof.
  intro OBSERVATIONS; split; intros header bound_block count MEMBER;
    apply in_split in MEMBER as [prefix [suffix SAME]]; subst observations.
  - assert (FACT : Forall (fun observation => Mem.load Mint64 memory (fst (snd observation)) 0=
      Some (Vlong (Int64.repr (Z.of_nat (snd (snd observation))))))
      (prefix++(header,(bound_block,count))::suffix)).
    { induction OBSERVATIONS; constructor; [unfold rectangular_capture_observation in H; tauto|exact IHOBSERVATIONS]. }
    apply Forall_app in FACT as [_ FACT]; inversion FACT; assumption.
  - assert (FACT : Forall (fun observation => double_global_binding ge locals
      (fst observation) (fst (snd observation))) (prefix++(header,(bound_block,count))::suffix)).
    { induction OBSERVATIONS; constructor; [unfold rectangular_capture_observation in H; tauto|exact IHOBSERVATIONS]. }
    apply Forall_app in FACT as [_ FACT]; inversion FACT; assumption.
Qed.

Theorem rectangular_capture_observations_counts ge locals memory after steps observations :
  Forall2 (rectangular_capture_observation ge locals memory after) steps observations ->
  Forall (fun count => Z.of_nat count<=Int64.max_signed) (map (fun observation => snd (snd observation)) observations) /\
  Forall2 (fun step count => 1<=Z.of_nat count<=rectangular_capture_limit step)
    steps (map (fun observation => snd (snd observation)) observations).
Proof.
  intro OBSERVATIONS; induction OBSERVATIONS; cbn [map]; split; try constructor.
  - unfold rectangular_capture_observation in H; tauto.
  - tauto.
  - unfold rectangular_capture_observation in H; tauto.
  - tauto.
Qed.

Theorem rectangular_capture_observations_axes ge locals memory after axes steps observations :
  Forall2 (fun axis step => snd axis=rectangular_capture_header step) axes steps ->
  Forall2 (rectangular_capture_observation ge locals memory after) steps observations ->
  double_rectangular_observed_axes axes (map (fun observation => snd (snd observation)) observations) observations.
Proof.
  intro LINK; revert observations; induction LINK; intros observations RECEIPTS.
  - inversion RECEIPTS; constructor.
  - inversion RECEIPTS as [|step observation steps observations' FACT REST]; subst step steps observations.
    cbn [map]; constructor.
    + exists (fst (snd observation)).
      destruct observation as [header [bound_block count]]; cbn [fst snd].
      left; f_equal; unfold rectangular_capture_observation in FACT; cbn [fst snd] in FACT.
      destruct FACT as [HEADER _]; congruence.
    + pose proof (IHLINK observations' REST) as TAIL.
      unfold double_rectangular_observed_axes in *.
      eapply Forall2_impl; [|exact TAIL].
      intros axis count [bound_block MEMBER]; exists bound_block; right; exact MEMBER.
Qed.

Print Assumptions rectangular_capture_accepted_observations.
Print Assumptions rectangular_capture_observations_loads.
Print Assumptions rectangular_capture_observations_counts.
Print Assumptions rectangular_capture_observations_axes.
