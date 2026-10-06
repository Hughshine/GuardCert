From Stdlib Require Import List Bool.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightSharedRegion
  ClightTempFrame ClightTempFootprint CompCertMemoryEquivalence ClightPrivateRegion.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite
  ClightPrivateScanHost ClightPrivateScanPreservation ClightPrivateScanShortcut.
Set Implicit Arguments.

(** This language service shares a normal fallback without adding scratch.
    It preserves actual execution, not merely the meaning of the condition.
    Abnormal exits and divergence are outside this finite-region service. *)
Definition readonly_shortcut_statement (shared : bool) tree candidate fallback :=
  if shared then shared_guarded_statement tree candidate fallback
  else tree_statement tree candidate fallback.

Theorem readonly_shortcut_normal_execution shared fe ge locals entry memory tree yes no after final :
  exec_stmt fe ge locals entry memory (tree_statement tree yes no) E0 after final Out_normal ->
  exec_stmt fe ge locals entry memory (readonly_shortcut_statement shared tree yes no)
    E0 after final Out_normal.
Proof.
  intro RUN; unfold readonly_shortcut_statement; destruct shared; [|exact RUN].
  change (clight_fragment_run fe (tree_statement tree yes no)
    (Entry ge locals entry memory) (FragmentObservation E0 after final Out_normal)) in RUN.
  apply readonly_tree_execution_exact in RUN.
  destruct RUN as [accepted [CHECK RUN]].
  eapply shared_guarded_statement_execution; eassumption.
Qed.

Definition realized_private_scan_shortcut shared live source
  (rule : private_scan_preserving_rule live source) tree :=
  readonly_shortcut_statement shared tree (scan_candidate rule)
    (select (private_scan_host (adapter_entry false) (scan_public_observe live))
      (scan_condition rule) (scan_candidate rule) source).

Lemma realized_private_scan_shortcut_direct live source
  (rule : private_scan_preserving_rule live source) tree :
  realized_private_scan_shortcut false rule tree = private_scan_readonly_shortcut rule tree.
Proof. reflexivity. Qed.

Theorem realized_private_scan_shortcut_preservation shared live source (rule : private_scan_preserving_rule live source)
  receipt tree
  (CHECK : forall temps, readonly_condition
    (readonly_clight_host (adapter_entry temps) (scan_public_observe live))
    (fun entry => scan_domain rule entry /\ receipt entry) (scan_premise rule) tree)
  temps (p : Clight.program) locals entry memory after final :
  statement_scope live source -> receipt (Entry (globalenv p) locals entry memory) ->
  exec_stmt (adapter_entry temps) (globalenv p) locals entry memory source E0 after final Out_normal ->
  exists exit result,
    exec_stmt (adapter_entry temps) (globalenv p) locals entry memory
      (realized_private_scan_shortcut shared rule tree) E0 exit result Out_normal /\
    temp_agree live after exit /\ memory_equivalent final result.
Proof.
  intros SCOPE RECEIPT SOURCE.
  destruct (@private_scan_shortcut_preservation live source rule receipt tree CHECK
    temps p locals entry memory after final SCOPE RECEIPT SOURCE)
    as [exit [result [RUN [PUBLIC MEMORY]]]].
  exists exit,result; split; [|split; assumption].
  unfold realized_private_scan_shortcut.
  apply readonly_shortcut_normal_execution; exact RUN.
Qed.

Print Assumptions readonly_shortcut_normal_execution.
Print Assumptions realized_private_scan_shortcut_direct.
Print Assumptions realized_private_scan_shortcut_preservation.
