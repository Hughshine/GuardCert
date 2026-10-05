From Stdlib Require Import List.
From compcert.common Require Import Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From GuardInterface Require Import GuardInterface ClightReadonlyRewrite.
Set Implicit Arguments.

Definition join_statements left right :=
  match left with
  | Sskip => right
  | _ => match right with Sskip => left | _ => Ssequence left right end
  end.

(** SimplExpr inserts empty sequences around translated conditions. This
    normalization changes only administrative skips and if/sequence children.
    It preserves all terminating traces, outcomes, temps and memories. *)
Fixpoint trim_skips body :=
  match body with
  | Ssequence lhs rhs => join_statements (trim_skips lhs) (trim_skips rhs)
  | Sifthenelse test yes no => Sifthenelse test (trim_skips yes) (trim_skips no)
  | _ => body
  end.

Definition stmt_equivalent fe first second := forall ge e le m trace le' m' out,
  exec_stmt fe ge e le m first trace le' m' out <-> exec_stmt fe ge e le m second trace le' m' out.

Lemma left_skip_equivalent fe body : stmt_equivalent fe (Ssequence Sskip body) body.
Proof.
  intros ge e le m trace le' m' out; split.
  - intro RUN; inversion RUN; subst;
      match goal with SKIP : exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ => inversion SKIP; subst end.
    + assumption.
    + contradiction.
  - intro RUN; change trace with (E0 ** trace); eapply exec_Sseq_1; [constructor|exact RUN].
Qed.

Lemma right_skip_equivalent fe body : stmt_equivalent fe (Ssequence body Sskip) body.
Proof.
  intros ge e le m trace le' m' out; split.
  - intro RUN; inversion RUN; subst.
    + match goal with SKIP : exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ => inversion SKIP; subst end.
      rewrite E0_right; assumption.
    + assumption.
  - intro RUN; destruct out; try (eapply exec_Sseq_2; [exact RUN|discriminate]).
    replace trace with (trace ** E0) by apply E0_right.
    eapply exec_Sseq_1; [exact RUN|constructor].
Qed.

Lemma join_statements_equivalent fe left right :
  stmt_equivalent fe (join_statements left right) (Ssequence left right).
Proof.
  unfold stmt_equivalent.
  destruct left; cbn [join_statements]; try (intros; apply iff_sym, left_skip_equivalent).
  all: destruct right; cbn [join_statements]; intros;
    try apply iff_refl; apply iff_sym, right_skip_equivalent.
Qed.

Lemma sequence_equivalent fe first second first' second' :
  stmt_equivalent fe first first' -> stmt_equivalent fe second second' ->
  stmt_equivalent fe (Ssequence first second) (Ssequence first' second').
Proof.
  intros LEFT RIGHT ge e le m trace le' m' out; split; intro RUN; inversion RUN; subst.
  - eapply exec_Sseq_1; [apply (proj1 (LEFT _ _ _ _ _ _ _ _)); eassumption|
                       apply (proj1 (RIGHT _ _ _ _ _ _ _ _)); eassumption].
  - eapply exec_Sseq_2; [apply (proj1 (LEFT _ _ _ _ _ _ _ _)); eassumption|assumption].
  - eapply exec_Sseq_1; [apply (proj2 (LEFT _ _ _ _ _ _ _ _)); eassumption|
                       apply (proj2 (RIGHT _ _ _ _ _ _ _ _)); eassumption].
  - eapply exec_Sseq_2; [apply (proj2 (LEFT _ _ _ _ _ _ _ _)); eassumption|assumption].
Qed.

Theorem trim_skips_equivalent fe body : stmt_equivalent fe (trim_skips body) body.
Proof.
  induction body; unfold stmt_equivalent in *; cbn [trim_skips]; try (intros; apply iff_refl).
  - exact (iff_trans (join_statements_equivalent fe _ _ _ _ _ _ _ _ _ _)
      (sequence_equivalent IHbody1 IHbody2 ge e le m trace le' m' out)).
  - split; intro RUN; inversion RUN; subst.
    + eapply exec_Sifthenelse; [eassumption|eassumption|].
      destruct b; [apply (proj1 (IHbody1 _ _ _ _ _ _ _ _))|apply (proj1 (IHbody2 _ _ _ _ _ _ _ _))]; assumption.
    + eapply exec_Sifthenelse; [eassumption|eassumption|].
      destruct b; [apply (proj2 (IHbody1 _ _ _ _ _ _ _ _))|apply (proj2 (IHbody2 _ _ _ _ _ _ _ _))]; assumption.
Qed.

Lemma trim_skips_runs fe O (observe : ClightCondition.fragment_observation -> O -> Prop)
  body entry observed :
  runs (readonly_clight_host fe observe) (trim_skips body) entry observed <->
  runs (readonly_clight_host fe observe) body entry observed.
Proof.
  split; intros [raw [RUN OBSERVE]]; exists raw; split; [|exact OBSERVE| |exact OBSERVE].
  - apply (proj1 (trim_skips_equivalent fe body _ _ _ _ _ _ _ _)); exact RUN.
  - apply (proj2 (trim_skips_equivalent fe body _ _ _ _ _ _ _ _)); exact RUN.
Qed.

Print Assumptions left_skip_equivalent.
Print Assumptions right_skip_equivalent.
Print Assumptions trim_skips_equivalent.
Print Assumptions trim_skips_runs.
