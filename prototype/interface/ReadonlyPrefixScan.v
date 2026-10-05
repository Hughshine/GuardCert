From Stdlib Require Import Bool.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyConditionComposition ReadonlyBranching.
Set Implicit Arguments.

(** The cursor indexes proof obligations. It can denote source iterations,
    memory accesses, or arithmetic sites; the framework knows none of those
    semantics. The runtime probes always operate on the same entry state.
    Advancing the ghost invariant is not executing the source in the guard. *)
Record readonly_prefix_spec {S} (H : guard_host S) (Cursor : Type) := ReadonlyPrefixSpec {
  prefix_next : Cursor -> Cursor;
  prefix_active_probe : Cursor -> check H;
  prefix_point_probe : Cursor -> check H;
  prefix_invariant : Cursor -> S -> Prop;
  prefix_active : Cursor -> S -> Prop;
  prefix_point_property : Cursor -> S -> Prop;
  prefix_activity_certificate : forall cursor,
    readonly_classifier H (prefix_invariant cursor) (prefix_active cursor)
      (fun entry => ~ prefix_active cursor entry) (prefix_active_probe cursor);
  prefix_point_certificate : forall cursor,
    readonly_condition H (fun entry => prefix_invariant cursor entry /\ prefix_active cursor entry)
      (fun entry => prefix_point_property cursor entry /\ prefix_invariant (prefix_next cursor) entry)
      (prefix_point_probe cursor)
}.

Fixpoint synthesize_prefix_scan {S} {H : guard_host S} {Cursor}
  (A : readonly_check_algebra H) (B : readonly_branch_algebra H)
  (SPEC : readonly_prefix_spec H Cursor) fuel cursor : check H :=
  match fuel with
  | O => constant_check A true
  | S rest => branch_check B (prefix_active_probe SPEC cursor)
      (branch_check B (prefix_point_probe SPEC cursor)
        (synthesize_prefix_scan A B SPEC rest (prefix_next SPEC cursor)) (constant_check A false))
      (constant_check A true)
  end.

Fixpoint prefix_scan_property {S} {H : guard_host S} {Cursor}
  (SPEC : readonly_prefix_spec H Cursor) fuel cursor entry : Prop :=
  match fuel with
  | O => True
  | S rest => prefix_active SPEC cursor entry ->
      prefix_point_property SPEC cursor entry /\
      prefix_scan_property SPEC rest (prefix_next SPEC cursor) entry
  end.

Definition synthesized_prefix_scan_condition S (H : guard_host S) Cursor
  (A : readonly_check_algebra H) (B : readonly_branch_algebra H)
  (SPEC : readonly_prefix_spec H Cursor) fuel cursor :
  readonly_condition H (prefix_invariant SPEC cursor) (prefix_scan_property SPEC fuel cursor)
    (synthesize_prefix_scan A B SPEC fuel cursor).
Proof.
  revert cursor; induction fuel as [|fuel IH]; intro cursor; cbn [synthesize_prefix_scan prefix_scan_property].
  - apply readonly_true_condition; intros; exact I.
  - eapply branch_readonly_conditions; [apply prefix_activity_certificate| |].
    + eapply branch_readonly_conditions.
      * apply condition_classifier, prefix_point_certificate.
      * eapply readonly_condition_entails.
        -- eapply readonly_condition_restrict; [apply IH|].
           intros entry [[INV ACTIVE] [POINT NEXT]]; exact NEXT.
        -- intros entry [[INV ACTIVE] [POINT NEXT]] REST _; split; assumption.
      * apply readonly_false_condition.
    + apply readonly_true_condition; intros entry [INV INACTIVE] ACTIVE; contradiction.
Defined.

Print Assumptions synthesized_prefix_scan_condition.
