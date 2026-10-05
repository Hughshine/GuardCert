From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Clight Csem.
From compcert.x86 Require Import Asm.
From Guard Require Import AbstractGuard ClightDecisionRule ClightCondition ClightRegionProgress ClightStructuredProgress ClightSyntaxEquality ClightCountedProtocol.
From GuardInterface Require Import ClightReadonlyRewrite ClightReadonlyCompiler ClightReadonlyLoopRule
  ClightCounterProgress ClightCircularCounter ClightEqualityLoop.
Set Implicit Arguments.

Definition propose_equality_loop source :=
  match source with
  | Sloop (Ssequence (Ssequence Sskip (Sifthenelse
      (Ebinop One (Ecast (Etempvar iterator _) _) (Ecast (Etempvar bound _) _) _) Sskip Sbreak)) body) _ =>
      Some (iterator, bound, body)
  | _ => None end.
Definition equality_loop_supported source :=
  match propose_equality_loop source with
  | Some (iterator, bound, body) =>
    if peq iterator bound then false else
    if statement_eq source (unsigned_equality_loop iterator bound body) then memory_body body else false
  | None => false end.
Theorem equality_loop_supported_sound source : equality_loop_supported source = true ->
  exists MODEL : region_progress source, True.
Proof.
  unfold equality_loop_supported; destruct (propose_equality_loop source) as [[[iterator bound] body]|]; try discriminate.
  destruct (peq iterator bound) as [|DISTINCT]; try discriminate.
  destruct (statement_eq source (unsigned_equality_loop iterator bound body)) as [EQ|]; try discriminate.
  intro BODY; subst source; exists (@unsigned_equality_progress iterator bound body DISTINCT BODY); exact I.
Qed.
Definition equality_progress_supported source := equality_loop_supported source || structured_progress_supported source.
Theorem equality_progress_supported_sound source : equality_progress_supported source = true ->
  exists MODEL : region_progress source, True.
Proof.
  unfold equality_progress_supported; rewrite orb_true_iff; intros [EQUALITY|STRUCTURED].
  - apply equality_loop_supported_sound; exact EQUALITY.
  - apply structured_progress_supported_sound; exact STRUCTURED.
Qed.
Definition equality_loop_rule iterator bound body (DISTINCT : iterator <> bound) (BODY : memory_body body = true) :
  readonly_clight_rule (unsigned_equality_loop iterator bound body).
Proof.
  apply readonly_forward_loop_rule with (candidate := unsigned_order_loop iterator bound body)
    (guard := synthesize_decision_tree (equality_primitives iterator bound) (Fact tt))
    (domain := equality_domain iterator bound) (premise := equality_property iterator bound tt).
  - exact (proj1 (@equality_loop_quiet iterator bound body BODY)).
  - exact (proj2 (@equality_loop_quiet iterator bound body BODY)).
  - intro temps; apply equality_condition.
  - intros temps entry observed DOMAIN PREMISE RUN; eapply equality_loop_forward; eassumption.
  - intros temps p e le m le' m' RUN; eapply equality_domain_from_source; exact RUN.
Defined.
Definition choose_equality_loop source : option (readonly_clight_rule source).
Proof.
  destruct (propose_equality_loop source) as [[[iterator bound] body]|]; [|exact None].
  destruct (peq iterator bound) as [|DISTINCT]; [exact None|].
  destruct (statement_eq source (unsigned_equality_loop iterator bound body)) as [EQ|]; [|exact None].
  destruct (memory_body body) eqn:BODY; [|exact None].
  rewrite EQ; exact (Some (@equality_loop_rule iterator bound body DISTINCT BODY)).
Defined.
Definition compile_equality_loops := compile_readonly_rewrites choose_equality_loop equality_progress_supported.
Theorem compile_equality_loops_correct p target : compile_equality_loops p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof. apply compile_readonly_rewrites_correct, equality_progress_supported_sound. Qed.
Print Assumptions equality_loop_supported_sound.
Print Assumptions equality_progress_supported_sound.
Print Assumptions equality_loop_rule.
Print Assumptions choose_equality_loop.
Print Assumptions compile_equality_loops_correct.
