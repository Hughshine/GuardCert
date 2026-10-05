From Stdlib Require Import List.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Csyntax Csem Clight ClightBigstep.
From compcert.x86 Require Import Asm.
From Guard Require Import ClightGuard ClightCondition ClightTempFrame ClightSyntaxEquality ClightProgressClassifier.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite
  ClightRegionBoundary ClightPrivateCandidateExample ClightReadonlyProjectedCompiler.
Import ListNotations.
Set Implicit Arguments.

(** A deliberately small user: preserve public=5 and add a fresh private
    assignment. The point is to exercise different raw temporary exits through
    the actual projected context proof, not to claim a profitable optimization. *)
Definition private_candidate_rule live public private (FRESH : ~ In private live) :
  readonly_projected_clight_rule live (public_set public).
Proof.
  refine {| projected_candidate := private_candidate public private;
    projected_guard := Decision true; projected_domain := fun _ => True;
    projected_premise := fun _ => True; projected_source_writes := [public] |}.
  - constructor; cbn; auto.
  - intro temps; exact (private_candidate_check (adapter_entry temps) public private live).
  - intro temps; exact (@private_candidate_equivalent (adapter_entry temps) public private live FRESH).
  - intros; constructor.
Defined.

Definition choose_private_candidate live (pool : list (ident * Ctypes.type)) source :
  option (readonly_projected_clight_rule live source).
Proof.
  destruct pool as [|[private ty] pool]; [exact None|].
  destruct (in_dec peq private live) as [USED|FRESH]; [exact None|].
  refine (match source as s return option (readonly_projected_clight_rule live s) with
    | Sset public a => _
    | _ => None end).
  destruct (statement_eq (Sset public a) (public_set public)) as [SAME|]; [|exact None].
  rewrite SAME; exact (Some (@private_candidate_rule live public private FRESH)).
Defined.

Definition compile_private_candidate :=
  compile_projected_readonly choose_private_candidate progress_supported 1.

Theorem compile_private_candidate_correct p target :
  compile_private_candidate p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof. apply compile_projected_readonly_correct, progress_supported_sound. Qed.

Print Assumptions private_candidate_rule.
Print Assumptions choose_private_candidate.
Print Assumptions compile_private_candidate_correct.
