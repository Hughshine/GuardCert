From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Csyntax Csem Clight ClightBigstep.
From compcert.x86 Require Import Asm.
From Guard Require Import AbstractGuard SemanticFacts ClightGuard ClightCondition ClightDecisionRule ClightTempFrame
  ClightSyntaxEquality ClightStraightLine ClightCountedLoop ClightFrontendLoopProtocol
  ClightFrontendRegion ClightLoopSyntax ClightSameAddress.
From GuardInterface Require Import ClightReadonlyRewrite ClightReadonlyProjectedCompiler
  ClightReadonlyProjectedLoopRule ClightIndexedLoadBody ClightIndexedLoadDomain ClightIndexedAliasGuard ClightIndexedLoadLoop.
Import ListNotations.
Set Implicit Arguments.

Definition indexed_load_rule live iterator bound out parameter cache body cap
  (CAP : (Z.of_nat cap <= Int.max_signed)%Z)
  (DISTINCT : iterator <> bound) (IO : iterator <> out) (IQ : iterator <> parameter)
  (CI : cache <> iterator) (CN : cache <> bound) (CP : cache <> out)
  (FRESH : ~ In cache live)
  (FLAT : flatten_region body = [indexed_load_body out parameter iterator]) :
  readonly_projected_clight_rule live (frontend_counted_loop iterator bound body).
Proof.
  apply readonly_projected_forward_loop_rule with
    (candidate := indexed_load_candidate iterator bound out parameter cache)
    (guard := synthesize_decision_tree (@indexed_guard_primitives iterator bound out parameter cap CAP) (Fact tt))
    (domain := indexed_load_domain iterator bound out parameter)
    (premise := indexed_guard_property iterator bound out parameter cap tt)
    (writes := [iterator]).
  - unfold frontend_counted_loop, counter_increment; constructor.
    + constructor; [repeat constructor|].
      eapply writes_only_weaken with (small := []);
        [intros id BAD; contradiction|exact (@indexed_source_writes out parameter iterator body FLAT)].
    + repeat constructor; cbn; auto.
  - exact (@indexed_loop_quiet out parameter iterator bound body FLAT).
  - reflexivity.
  - intro temps; apply indexed_guard_condition.
  - intros temps entry observed DOMAIN PREMISE SOURCE.
    exact (@indexed_load_forward (adapter_entry temps) live iterator bound out parameter cache body cap entry observed
      DISTINCT IO IQ CI CN CP FRESH FLAT DOMAIN PREMISE SOURCE).
  - intros temps p e le m le' m' SOURCE.
    exact (@indexed_load_domain_from_source (adapter_entry temps) (Clight.globalenv p) e le m
      iterator bound out parameter body le' m' DISTINCT IO IQ FLAT SOURCE).
Defined.

Definition choose_indexed_load cap (CAP : (Z.of_nat cap <= Int.max_signed)%Z)
  live (pool : list (ident * Ctypes.type)) source : option (readonly_projected_clight_rule live source).
Proof.
  destruct pool as [|[cache ty] pool]; [exact None|].
  destruct (in_dec peq cache live) as [USED|FRESH]; [exact None|].
  destruct (propose_frontend_shape source) as [[[iterator bound] body]|]; [|exact None].
  destruct (statement_eq source (frontend_counted_loop iterator bound body)) as [SOURCE|]; [|exact None].
  rewrite SOURCE.
  refine (match flatten_region body as atoms return flatten_region body = atoms ->
    option (readonly_projected_clight_rule live (frontend_counted_loop iterator bound body)) with
    | [Sassign (Ederef (Ebinop _ (Etempvar out _) _ _) _)
        (Ebinop _ (Ebinop _ (Ederef (Etempvar parameter _) _) _ _) _ _)] => _
    | _ => fun _ => None end eq_refl).
  intro PROPOSAL.
  destruct (list_eq_dec statement_eq (flatten_region body) [indexed_load_body out parameter iterator]) as [FLAT|]; [|exact None].
  destruct (peq iterator bound) as [|DISTINCT]; [exact None|].
  destruct (peq iterator out) as [|IO]; [exact None|].
  destruct (peq iterator parameter) as [|IQ]; [exact None|].
  destruct (peq cache iterator) as [|CI]; [exact None|].
  destruct (peq cache bound) as [|CN]; [exact None|].
  destruct (peq cache out) as [|CP]; [exact None|].
  exact (Some (@indexed_load_rule live iterator bound out parameter cache body cap CAP DISTINCT IO IQ CI CN CP FRESH FLAT)).
Defined.

Definition indexed_default_cap := 16%nat.
Definition indexed_default_cap_bound : (Z.of_nat indexed_default_cap <= Int.max_signed)%Z.
Proof. change (16 <= 2147483647)%Z; lia. Qed.
Definition choose_indexed_default := @choose_indexed_load indexed_default_cap indexed_default_cap_bound.
Definition compile_indexed_loads := compile_projected_readonly choose_indexed_default frontend_progress_supported 1.
Theorem compile_indexed_loads_correct p target : compile_indexed_loads p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof. apply compile_projected_readonly_correct, frontend_progress_supported_sound. Qed.
Print Assumptions indexed_load_rule.
Print Assumptions choose_indexed_load.
Print Assumptions compile_indexed_loads_correct.
