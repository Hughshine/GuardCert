From Stdlib Require Import List.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Csyntax Csem Clight ClightBigstep.
From compcert.x86 Require Import Asm.
From Guard Require Import SemanticFacts ClightGuard ClightCondition ClightDecisionRule ClightTempFrame
  ClightSyntaxEquality ClightStraightLine ClightCountedLoop ClightFrontendLoopProtocol
  ClightFrontendRegion ClightLoopSyntax ClightSameAddress.
From GuardInterface Require Import ClightReadonlyRewrite ClightReadonlyProjectedCompiler
  ClightReadonlyProjectedLoopRule ClightStableLoadBody ClightStableLoadGuard ClightStableLoadLoop.
Import ListNotations.
Set Implicit Arguments.

Definition stable_load_rule live iterator bound out parameter cache body
  (DISTINCT : iterator <> bound) (IO : iterator <> out) (IQ : iterator <> parameter)
  (CI : cache <> iterator) (CN : cache <> bound) (CP : cache <> out)
  (FRESH : ~ In cache live)
  (FLAT : flatten_region body = [stable_load_body out parameter iterator]) :
  readonly_projected_clight_rule live (frontend_counted_loop iterator bound body).
Proof.
  apply readonly_projected_forward_loop_rule with
    (candidate := stable_load_candidate iterator bound out parameter cache)
    (guard := synthesize_decision_tree (stable_load_guard_primitives out parameter DISTINCT) (AbstractGuard.Fact tt))
    (domain := stable_load_guard_domain iterator bound out parameter)
    (premise := stable_load_guard_property iterator bound out parameter tt)
    (writes := [iterator]).
  - unfold frontend_counted_loop, counter_increment.
    constructor.
    + constructor; [repeat constructor|].
      eapply writes_only_weaken with (small := []);
        [intros id BAD; contradiction|exact (@stable_source_body_writes out parameter iterator body FLAT)].
    + repeat constructor; cbn; auto.
  - exact (@stable_source_loop_quiet iterator bound out parameter body FLAT).
  - reflexivity.
  - intro temps; apply stable_load_condition.
  - intros temps entry observed DOMAIN PREMISE SOURCE.
    exact (@stable_load_forward (adapter_entry temps) live iterator bound out parameter cache body entry observed
      DISTINCT IO IQ CI CN CP FRESH FLAT DOMAIN PREMISE SOURCE).
  - intros temps p e le m le' m' SOURCE.
    exact (@stable_load_domain_from_source (adapter_entry temps) (Clight.globalenv p) e le m
      iterator bound out parameter body le' m' FLAT SOURCE).
Defined.

(** Proposal and complete checks belong to this user pass. The new framework
    only accepts the resulting typed rule, including its actual source body. *)
Definition choose_stable_load live (pool : list (ident * Ctypes.type)) source :
  option (readonly_projected_clight_rule live source).
Proof.
  destruct pool as [|[cache ty] pool]; [exact None|].
  destruct (in_dec peq cache live) as [USED|FRESH]; [exact None|].
  destruct (propose_frontend_shape source) as [[[iterator bound] body]|]; [|exact None].
  destruct (statement_eq source (frontend_counted_loop iterator bound body)) as [SOURCE|]; [|exact None].
  rewrite SOURCE.
  refine (match flatten_region body as atoms return
    flatten_region body = atoms -> option (readonly_projected_clight_rule live (frontend_counted_loop iterator bound body)) with
    | [Sassign (Ederef (Etempvar out _) _)
        (Ebinop _ (Ebinop _ (Ederef (Etempvar parameter _) _) _ _) _ _)] => _
    | _ => fun _ => None end eq_refl).
  intro PROPOSAL.
  destruct (list_eq_dec statement_eq (flatten_region body) [stable_load_body out parameter iterator]) as [FLAT|];
    [|exact None].
  destruct (peq iterator bound) as [|DISTINCT]; [exact None|].
  destruct (peq iterator out) as [|IO]; [exact None|].
  destruct (peq iterator parameter) as [|IQ]; [exact None|].
  destruct (peq cache iterator) as [|CI]; [exact None|].
  destruct (peq cache bound) as [|CN]; [exact None|].
  destruct (peq cache out) as [|CP]; [exact None|].
  exact (Some (@stable_load_rule live iterator bound out parameter cache body DISTINCT IO IQ CI CN CP FRESH FLAT)).
Defined.

Definition compile_stable_loads :=
  compile_projected_readonly choose_stable_load frontend_progress_supported 1.
Theorem compile_stable_loads_correct p target : compile_stable_loads p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof. apply compile_projected_readonly_correct, frontend_progress_supported_sound. Qed.

Print Assumptions stable_load_rule.
Print Assumptions choose_stable_load.
Print Assumptions compile_stable_loads_correct.
