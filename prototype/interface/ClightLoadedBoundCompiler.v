From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Csyntax Csem Clight ClightBigstep.
From compcert.x86 Require Import Asm.
From Guard Require Import AbstractGuard SemanticFacts ClightGuard ClightCondition ClightPureExpr ClightDecisionRule
  ClightSyntaxEquality ClightStraightLine ClightCountedLoop ClightCountedProtocol ClightFrontendRegion ClightRegionProgress ClightTempFrame
  ClightLoopSyntax ClightFrontendLoopProtocol.
From GuardInterface Require Import ClightReadonlyRewrite ClightReadonlyProjectedCompiler
  ClightReadonlyProjectedLoopRule ClightStrictLoopProgress ClightLoadedBoundSyntax ClightLoadedBoundGuard
  ClightLoadedBoundLoop.
Import ListNotations.
Set Implicit Arguments.

Definition propose_loaded_bound source :=
  match source with
  | Sloop (Ssequence (Ssequence Sskip (Sifthenelse
      (Ebinop Olt (Etempvar iterator _) (Ederef (Etempvar bound _) _) _) Sskip Sbreak)) body) _ =>
    Some (iterator, bound, body)
  | _ => None end.
Definition loaded_bound_supported source :=
  match propose_loaded_bound source with
  | Some (iterator, bound, body) =>
    if statement_eq source (loaded_bound_loop iterator bound body) then memory_body body else false
  | None => false end.
Theorem loaded_bound_supported_sound source : loaded_bound_supported source = true ->
  exists MODEL : region_progress source, True.
Proof.
  unfold loaded_bound_supported; destruct (propose_loaded_bound source) as [[[iterator bound] body]|];
    try discriminate.
  destruct (statement_eq source (loaded_bound_loop iterator bound body)) as [EQ|]; try discriminate.
  intro BODY; subst source; exists (@strict_frontend_progress iterator (loaded_bound_test iterator bound) body BODY
    (fun ge locals le memory => @loaded_bound_test_strict ge locals le memory iterator bound)); exact I.
Qed.
Definition loaded_progress_supported source := frontend_progress_supported source || loaded_bound_supported source.
Theorem loaded_progress_supported_sound source : loaded_progress_supported source = true ->
  exists MODEL : region_progress source, True.
Proof.
  unfold loaded_progress_supported; rewrite orb_true_iff; intros [BASIC|LOADED].
  - apply frontend_progress_supported_sound; exact BASIC.
  - apply loaded_bound_supported_sound; exact LOADED.
Qed.

Definition loaded_bound_rule live iterator parameter out cache body
  (IQ : iterator <> parameter) (IO : iterator <> out)
  (CI : cache <> iterator) (CQ : cache <> parameter) (CP : cache <> out) (FRESH : ~ In cache live)
  (FLAT : flatten_region body = [loaded_bound_body out iterator]) :
  readonly_projected_clight_rule live (loaded_bound_loop iterator parameter body).
Proof.
  assert (QUIET : quiet_statement body = true) by
    (apply flatten_quiet_certificate; rewrite FLAT; constructor; [reflexivity|constructor]).
  apply readonly_projected_forward_loop_rule with
    (candidate := loaded_bound_candidate iterator parameter cache body)
    (guard := synthesize_decision_tree (loaded_bound_primitives iterator out parameter) (Fact tt))
    (domain := loaded_bound_domain iterator out parameter)
    (premise := loaded_bound_property iterator out parameter tt) (writes := [iterator]).
  - exact (@loaded_source_writes iterator parameter out body FLAT).
  - exact (@loaded_source_quiet iterator parameter out body FLAT).
  - cbn [loaded_bound_candidate frontend_counted_loop quiet_statement counter_increment].
    rewrite QUIET; reflexivity.
  - intro temps; apply loaded_bound_condition.
  - intros temps entry observed DOMAIN PREMISE SOURCE.
    exact (@loaded_bound_forward (adapter_entry temps) live iterator parameter out cache body entry observed
      IQ IO CI CQ CP FRESH FLAT DOMAIN PREMISE SOURCE).
  - intros temps p e le m le' m' SOURCE.
    exact (@loaded_bound_domain_from_source (adapter_entry temps) (Clight.globalenv p) e le m
      iterator out parameter body le' m' FLAT SOURCE).
Defined.
Definition choose_loaded_bound live (pool : list (ident * type)) source :
  option (readonly_projected_clight_rule live source).
Proof.
  destruct pool as [|[cache ty] pool]; [exact None|].
  destruct (in_dec peq cache live) as [|FRESH]; [exact None|].
  destruct (propose_loaded_bound source) as [[[iterator parameter] body]|]; [|exact None].
  destruct (statement_eq source (loaded_bound_loop iterator parameter body)) as [SOURCE|]; [|exact None].
  rewrite SOURCE.
  refine (match flatten_region body as atoms return flatten_region body = atoms ->
    option (readonly_projected_clight_rule live (loaded_bound_loop iterator parameter body)) with
    | [Sassign (Ederef (Etempvar out _) _) _] => _
    | _ => fun _ => None end eq_refl).
  intro PROPOSAL.
  destruct (list_eq_dec statement_eq (flatten_region body) [loaded_bound_body out iterator]) as [FLAT|]; [|exact None].
  destruct (peq iterator parameter) as [|IQ]; [exact None|].
  destruct (peq iterator out) as [|IO]; [exact None|].
  destruct (peq cache iterator) as [|CI]; [exact None|].
  destruct (peq cache parameter) as [|CQ]; [exact None|].
  destruct (peq cache out) as [|CP]; [exact None|].
  exact (Some (@loaded_bound_rule live iterator parameter out cache body IQ IO CI CQ CP FRESH FLAT)).
Defined.
Definition compile_loaded_bounds := compile_projected_readonly choose_loaded_bound loaded_progress_supported 1.
Theorem compile_loaded_bounds_correct p target : compile_loaded_bounds p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof. apply compile_projected_readonly_correct, loaded_progress_supported_sound. Qed.
Print Assumptions loaded_bound_supported_sound.
Print Assumptions loaded_bound_rule.
Print Assumptions choose_loaded_bound.
Print Assumptions compile_loaded_bounds_correct.
