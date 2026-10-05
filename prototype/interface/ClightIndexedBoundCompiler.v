From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Csyntax Csem Clight ClightBigstep.
From compcert.x86 Require Import Asm.
From Guard Require Import AbstractGuard SemanticFacts ClightGuard ClightCondition ClightDecisionRule ClightSyntaxEquality
  ClightStraightLine ClightCountedLoop ClightCountedProtocol ClightFrontendRegion ClightFrontendLoopProtocol ClightLoopSyntax ClightRegionProgress.
From GuardInterface Require Import ClightReadonlyRewrite ClightReadonlyProjectedCompiler ClightReadonlyProjectedLoopRule
  ClightStrictLoopProgress ClightLoadedBoundCompiler ClightIndexedLoadCompiler ClightIndexedBoundSyntax
  ClightIndexedBoundGuard ClightIndexedBoundLoop.
Import ListNotations.
Set Implicit Arguments.

Definition propose_indexed_bound source :=
  match source with
  | Sloop (Ssequence (Ssequence Sskip (Sifthenelse
      (Ebinop Olt (Etempvar iterator _) (Ecast (Ederef (Etempvar bound _) _) _) _) Sskip Sbreak)) body) _ =>
    Some (iterator, bound, body)
  | _ => None end.
Definition indexed_bound_supported source :=
  match propose_indexed_bound source with
  | Some (iterator, bound, body) =>
    if statement_eq source (indexed_bound_loop iterator bound body) then memory_body body else false
  | None => false end.
Theorem indexed_bound_supported_sound source : indexed_bound_supported source = true ->
  exists MODEL : region_progress source, True.
Proof.
  unfold indexed_bound_supported; destruct (propose_indexed_bound source) as [[[iterator bound] body]|]; try discriminate.
  destruct (statement_eq source (indexed_bound_loop iterator bound body)) as [EQ|]; try discriminate.
  intro BODY; subst source; exists (@strict_frontend_progress iterator (indexed_bound_test iterator bound) body BODY
    (fun ge locals le memory => @indexed_bound_test_strict ge locals le memory iterator bound)); exact I.
Qed.
Definition indexed_bound_progress_supported source := loaded_progress_supported source || indexed_bound_supported source.
Theorem indexed_bound_progress_supported_sound source : indexed_bound_progress_supported source = true ->
  exists MODEL : region_progress source, True.
Proof.
  unfold indexed_bound_progress_supported; rewrite orb_true_iff; intros [EXISTING|INDEXED].
  - apply loaded_progress_supported_sound; exact EXISTING.
  - apply indexed_bound_supported_sound; exact INDEXED.
Qed.

Definition indexed_bound_rule live iterator out bound cache body cap (CAP : (Z.of_nat cap <= Int.max_signed)%Z)
  (IO : iterator <> out) (IQ : iterator <> bound) (CI : cache <> iterator) (CQ : cache <> bound) (CP : cache <> out)
  (FRESH : ~ In cache live) (FLAT : flatten_region body = [indexed_bound_body out iterator]) :
  readonly_projected_clight_rule live (indexed_bound_loop iterator bound body).
Proof.
  apply readonly_projected_forward_loop_rule with
    (candidate := indexed_bound_candidate iterator bound cache body)
    (guard := synthesize_decision_tree (@indexed_bound_primitives iterator out bound body cap IO IQ FLAT CAP) (Fact tt))
    (domain := indexed_bound_domain iterator bound body)
    (premise := indexed_bound_guard_property iterator out bound cap tt) (writes := [iterator]).
  - exact (@indexed_bound_source_writes iterator bound out body FLAT).
  - exact (@indexed_bound_source_quiet iterator bound out body FLAT).
  - cbn [indexed_bound_candidate frontend_counted_loop quiet_statement counter_increment].
    rewrite (@ClightIndexedBoundPrefix.indexed_bound_body_quiet out iterator body FLAT); reflexivity.
  - intro temps; apply indexed_bound_condition.
  - intros temps entry observed DOMAIN PREMISE SOURCE.
    exact (@indexed_bound_forward (adapter_entry temps) live iterator out bound cache body cap entry observed
      IO IQ CI CQ CP FRESH FLAT DOMAIN PREMISE SOURCE).
  - intros temps p e le m le' m' SOURCE.
    exact (@indexed_bound_domain_from_source (adapter_entry temps) (Clight.globalenv p) e le m
      iterator bound out body le' m' FLAT SOURCE).
Defined.
Definition choose_indexed_bound cap (CAP : (Z.of_nat cap <= Int.max_signed)%Z)
  live (pool : list (ident * type)) source : option (readonly_projected_clight_rule live source).
Proof.
  destruct pool as [|[cache ty] pool]; [exact None|].
  destruct (in_dec peq cache live) as [|FRESH]; [exact None|].
  destruct (propose_indexed_bound source) as [[[iterator bound] body]|]; [|exact None].
  destruct (statement_eq source (indexed_bound_loop iterator bound body)) as [SOURCE|]; [|exact None].
  rewrite SOURCE.
  refine (match flatten_region body as atoms return flatten_region body = atoms ->
    option (readonly_projected_clight_rule live (indexed_bound_loop iterator bound body)) with
    | [Sassign (Ederef (Ebinop _ (Etempvar out _) _ _) _) _] => _
    | _ => fun _ => None end eq_refl).
  intro PROPOSAL.
  destruct (list_eq_dec statement_eq (flatten_region body) [indexed_bound_body out iterator]) as [FLAT|]; [|exact None].
  destruct (peq iterator out) as [|IO]; [exact None|].
  destruct (peq iterator bound) as [|IQ]; [exact None|].
  destruct (peq cache iterator) as [|CI]; [exact None|].
  destruct (peq cache bound) as [|CQ]; [exact None|].
  destruct (peq cache out) as [|CP]; [exact None|].
  exact (Some (@indexed_bound_rule live iterator out bound cache body cap CAP IO IQ CI CQ CP FRESH FLAT)).
Defined.
Definition choose_indexed_bound_default := @choose_indexed_bound indexed_default_cap indexed_default_cap_bound.
Definition compile_indexed_bounds := compile_projected_readonly choose_indexed_bound_default indexed_bound_progress_supported 1.
Theorem compile_indexed_bounds_correct p target : compile_indexed_bounds p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof. apply compile_projected_readonly_correct, indexed_bound_progress_supported_sound. Qed.
Print Assumptions indexed_bound_supported_sound.
Print Assumptions indexed_bound_progress_supported_sound.
Print Assumptions indexed_bound_rule.
Print Assumptions choose_indexed_bound.
Print Assumptions compile_indexed_bounds_correct.
