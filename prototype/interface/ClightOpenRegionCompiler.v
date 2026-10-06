From Stdlib Require Import List.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Clight Csyntax Csem.
From compcert.x86 Require Import Asm.
From Guard Require Import ClightTempFootprint ClightTempScope ClightPrivatePool
  ClightGuard ClightRegionProgress ClightOpenRegionContract ClightOpenRegion ClightOpenRegionProof.
From GuardInterface Require Import ClightReadonlyTestCompiler.
Set Implicit Arguments.

Section USER_REGIONS.
Variable select : list ident -> list (ident * Ctypes.type) -> Clight.statement -> option Clight.statement.
Hypothesis SELECT_SOUND : forall live pool source target,
  select live pool source = Some target -> open_region_contract live source target.

Definition transform_open_regions pool p :=
  let live := program_temps p in
  if private_pool_check live pool then
    OpenRegion.transform_program pool label_free (select live pool) p else p.

Theorem transform_open_regions_correct pool p :
  forward_simulation (Clight.semantics2 p) (Clight.semantics2 (transform_open_regions pool p)).
Proof.
  unfold transform_open_regions; destruct (private_pool_check (program_temps p) pool) eqn:FRESH.
  - apply OpenRegionProof.transform_program_correct2 with (live := program_temps p).
    + intros; eapply SELECT_SOUND; eauto.
    + apply program_scope_computed.
    + eapply private_pool_check_sound; exact FRESH.
  - apply identical_clight_forward.
Qed.

Variable prior : Clight.program -> Clight.program.
Hypothesis PRIOR_CORRECT : forall p,
  forward_simulation (Clight.semantics2 p) (Clight.semantics2 (prior p)).
Variable pool : Clight.program -> list (ident * type).

Definition open_regions_after p := transform_open_regions (pool (prior p)) (prior p).
Lemma open_regions_after_correct p :
  forward_simulation (Clight.semantics2 p) (Clight.semantics2 (open_regions_after p)).
Proof.
  eapply compose_forward_simulations; [apply PRIOR_CORRECT | apply transform_open_regions_correct].
Qed.

Definition compile_open_regions_after : Csyntax.program -> res Asm.program :=
  compile_readonly_tests_after (fun _ => None) open_regions_after.
Theorem compile_open_regions_after_correct p target :
  compile_open_regions_after p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof.
  apply compile_readonly_tests_after_correct; apply open_regions_after_correct.
Qed.
End USER_REGIONS.

Print Assumptions transform_open_regions_correct.
Print Assumptions compile_open_regions_after_correct.
