From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST Errors Smallstep Events.
From compcert.cfrontend Require Import Ctypes Csyntax Csem Clight ClightBigstep.
From compcert.x86 Require Import Asm.
From Guard Require Import AbstractGuard SemanticFacts ClightGuard ClightCondition ClightSyntaxEquality
  ClightStraightLine ClightRegionProgress.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyCompiler ClightLoopBridge
  ClightLoadedBoundSyntax ClightLoadedBoundCompiler ClightMixedLoadedProgress
  ClightDualRepeatedSyntax ClightDualRepeatedGuard ClightDualRepeatedForward.
Import ListNotations.
Set Implicit Arguments.

Definition dual_repeat_rule row rows column columns out body outer
  (RC : row <> column) (RN : row <> rows) (RM : row <> columns) (RP : row <> out)
  (CN : column <> rows) (CM : column <> columns) (CP : column <> out)
  (BODY : flatten_region body = [dual_repeat_store out])
  (OUTER : flatten_region outer = [dual_repeat_reset column; loaded_bound_loop column columns body]) :
  readonly_clight_rule (dual_repeat_source row rows outer).
Proof.
  refine {| readonly_candidate := dual_repeat_candidate row rows column columns out;
    readonly_guard := dual_repeat_guard row rows columns out;
    readonly_domain := dual_repeat_domain row rows outer;
    readonly_premise := dual_repeat_premise row rows columns out |}.
  - intro temps; exact (@dual_repeat_condition (adapter_entry temps) fragment_observation (@eq fragment_observation)
      row rows column columns out body outer CM CP BODY OUTER).
  - intro temps; apply quiet_forward_loop_equivalent.
    + intros entry [after [final RUN]] _; exists (FragmentObservation E0 after final Out_normal); exact RUN.
    + reflexivity.
    + intros entry observed DOMAIN PREMISE SOURCE.
      exact (@dual_repeat_forward row rows column columns out body outer RC RN RM RP CN CM CP BODY OUTER
        (adapter_entry temps) entry observed DOMAIN PREMISE SOURCE).
  - intros temps p e le m after final SOURCE; exists after,final; intro fe.
    eapply (@quiet_execution_preserved (adapter_entry temps) fe (Clight.globalenv p) (Clight.globalenv p));
      [split; [reflexivity|intros; reflexivity]|exact SOURCE|].
    exact (@dual_repeat_source_quiet row rows out column columns body outer BODY OUTER).
Defined.

Record dual_repeat_description := DualRepeatDescription {
  repeat_row : ident; repeat_rows : ident; repeat_column : ident; repeat_columns : ident;
  repeat_out : ident; repeat_body : statement; repeat_outer : statement
}.
(** Proposal is untrusted; the chooser rechecks the whole source and both
    flattened bodies, including types, volatility and the increment form. *)
Definition propose_dual_repeat source :=
  match propose_loaded_bound source with
  | Some (row,rows,outer) => match flatten_region outer with
    | [Sset column _; inner] => match propose_loaded_bound inner with
      | Some (inner_column,columns,body) => if peq column inner_column then
        match flatten_region body with
        | [Sassign (Ederef (Etempvar out _) _) _] => Some (DualRepeatDescription row rows column columns out body outer)
        | _ => None end else None
      | None => None end
    | _ => None end
  | None => None end.
Definition choose_dual_repeat source : option (readonly_clight_rule source).
Proof.
  destruct (propose_dual_repeat source) as [[row rows column columns out body outer]|]; [|exact None].
  destruct (statement_eq source (dual_repeat_source row rows outer)) as [SAME|]; [|exact None].
  rewrite SAME.
  destruct (list_eq_dec statement_eq (flatten_region body) [dual_repeat_store out]) as [BODY|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region outer)
    [dual_repeat_reset column; loaded_bound_loop column columns body]) as [OUTER|]; [|exact None].
  destruct (peq row column) as [|RC]; [exact None|].
  destruct (peq row rows) as [|RN]; [exact None|].
  destruct (peq row columns) as [|RM]; [exact None|].
  destruct (peq row out) as [|RP]; [exact None|].
  destruct (peq column rows) as [|CN]; [exact None|].
  destruct (peq column columns) as [|CM]; [exact None|].
  destruct (peq column out) as [|CP]; [exact None|].
  exact (Some (@dual_repeat_rule row rows column columns out body outer RC RN RM RP CN CM CP BODY OUTER)).
Defined.
Definition compile_dual_repeats := compile_readonly_rewrites choose_dual_repeat mixed_loaded_progress_supported.
Theorem compile_dual_repeats_correct p target : compile_dual_repeats p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof. apply compile_readonly_rewrites_correct, mixed_loaded_progress_supported_sound. Qed.

Print Assumptions dual_repeat_rule.
Print Assumptions choose_dual_repeat.
Print Assumptions compile_dual_repeats_correct.
