From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers.
From Guard Require Import ClightCondition ClightNoWrap.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryArrayBackend GuardMemoryPointerBackend
  GuardMemoryParamPointerBounds GuardMemoryParamPointerSyntax GuardMemoryParamPointerProjectedCandidate GuardMemoryParameterRanges.
From GuardMemory Require Import GuardMemoryStartedPackage GuardMemoryStartedHeader GuardMemoryStartedPointerHeader.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition memory_started_pointer_static_bounds source (package : memory_started_pointer_package source) :=
  memory_param_pointer_static_bounds (param_pointer_region_limits (started_pointer_package package))
    (param_pointer_region_parameter_limits (started_pointer_package package)) (length (param_pointer_region_scalars (started_pointer_package package)))++
  [MemoryFramedNested.N.A.Interval 0 (memory_started_pointer_root_cap package-1)].
Definition memory_started_static_bounds source (package : memory_started_pointer_package source) :=
  memory_param_static_bounds (param_pointer_region_limits (started_pointer_package package))
    (param_pointer_region_parameter_limits (started_pointer_package package)) (length (param_pointer_region_scalars (started_pointer_package package)))++
  [MemoryNested.A.Interval 0 (memory_started_pointer_root_cap package-1)].
Lemma memory_started_pointer_root_range source (package : memory_started_pointer_package source) s :
  memory_started_pointer_header_domain package s -> memory_started_pointer_header_accept package s = true ->
  0 <= Int.signed (temp_word (started_pointer_iterator package) (entry_temps s)) < memory_started_pointer_root_cap package.
Proof.
  intros [[WORD [BOUND DOMAIN]] PARAMS] ACCEPT.
  unfold memory_started_pointer_header_accept,memory_started_pointer_bounds_accept,memory_started_bounds_accept in ACCEPT.
  rewrite !andb_true_iff in ACCEPT; destruct ACCEPT as [[ACTIVE [ROOT COUNTS]] PARAMETERS].
  destruct (memory_started_pointer_root_cap_sound package) as [POS SIGNED].
  apply (@memory_parameter_range_sound (started_pointer_iterator package) (memory_started_pointer_root_cap package) s POS SIGNED ROOT).
Qed.
Lemma memory_started_validator_within_append bounds values extra rest :
  length bounds = length values -> MemoryNested.A.env_within bounds values ->
  MemoryNested.A.env_within extra rest -> MemoryNested.A.env_within (bounds++extra) (values++rest).
Proof.
  revert values; induction bounds as [|bound bounds IH]; intros [|value values] LENGTH WITHIN TAIL;
    cbn [length app] in *; try discriminate.
  - exact TAIL.
  - apply MemoryNested.A.env_within_cons.
    + exact (WITHIN O bound eq_refl).
    + apply IH; [lia| |exact TAIL].
      intros index item LOOKUP; exact (WITHIN (S index) item LOOKUP).
Qed.
Print Assumptions memory_started_validator_within_append.
Lemma memory_started_encoder_within_append bounds values extra rest :
  length bounds = length values -> MemoryFramedNested.N.A.env_within bounds values ->
  MemoryFramedNested.N.A.env_within extra rest -> MemoryFramedNested.N.A.env_within (bounds++extra) (values++rest).
Proof.
  revert values; induction bounds as [|bound bounds IH]; intros [|value values] LENGTH WITHIN TAIL;
    cbn [length app] in *; try discriminate.
  - exact TAIL.
  - apply MemoryFramedNested.N.A.env_within_cons.
    + exact (WITHIN O bound eq_refl).
    + apply IH; [lia| |exact TAIL].
      intros index item LOOKUP; exact (WITHIN (S index) item LOOKUP).
Qed.
Print Assumptions memory_started_encoder_within_append.
Print Assumptions memory_started_pointer_root_range.
