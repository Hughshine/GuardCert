From Stdlib Require Import List Bool Arith ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightSyntaxEquality ClightLoopSyntax ClightRegionProgress ClightTempFrame.
From GuardMemory Require Import GuardMemoryDoubleAssignmentFactory GuardMemoryDoubleSourceInstruction
  GuardMemoryDoubleInitializedReductionData GuardMemoryDoubleMatmulLoops GuardMemoryLongLoopControl.
Import ListNotations.
Set Implicit Arguments.

(** A checked family of canonical nests around initialization/reduction.
    The shared loaded bound is read at every actual source loop test. *)
Fixpoint double_initialized_nest_code outers description : statement :=
  match outers with
  | [] => double_initialized_reduction_code description
  | iterator::rest => memory_long_initialized_loop iterator
      (double_matmul_long_condition iterator (initialized_reduction_header description))
      (double_initialized_nest_code rest description) end.
Fixpoint double_initialized_nest_fresh (controls outers : list ident) : Prop :=
  match outers with
  | [] => True
  | iterator::rest => ~ In iterator controls /\ double_initialized_nest_fresh (controls++[iterator]) rest end.
Definition double_initialized_outer_shape source := match source with
  | Ssequence (Sset iterator _) (Sloop (Ssequence _ body) _) => Some (iterator,body)
  | _ => None end.
Fixpoint double_initialized_nest_fuel source : nat := match source with
  | Ssequence (Sset _ _) (Sloop (Ssequence _ body) _) => S (double_initialized_nest_fuel body)
  | _ => 1 end.
Fixpoint checked_double_initialized_nest_with_fuel fuel p controls source : option (list ident*double_initialized_reduction) :=
  match fuel with
  | O => None
  | S rest => match checked_double_initialized_reduction p controls source with
    | Some description => Some ([],description)
    | None => match double_initialized_outer_shape source with
      | Some (iterator,body) =>
        if negb (existsb (Pos.eqb iterator) controls) then
          match checked_double_initialized_nest_with_fuel rest p (controls++[iterator]) body with
          | Some (outers,description) =>
            if statement_eq source (double_initialized_nest_code (iterator::outers) description)
            then Some (iterator::outers,description) else None
          | None => None end
        else None
      | None => None end end end.
Definition checked_double_initialized_nest p controls source :=
  checked_double_initialized_nest_with_fuel (double_initialized_nest_fuel source) p controls source.

Lemma double_initialized_nest_with_fuel_sound fuel : forall p controls source outers description,
  checked_double_initialized_nest_with_fuel fuel p controls source=Some (outers,description) ->
  source=double_initialized_nest_code outers description /\
  checked_double_initialized_reduction p (controls++outers) (double_initialized_reduction_code description)=Some description /\
  double_initialized_nest_fresh controls outers.
Proof.
  induction fuel as [|fuel IH]; intros p controls source outers description; cbn [checked_double_initialized_nest_with_fuel];
    [discriminate|].
  destruct (checked_double_initialized_reduction p controls source) as [leaf|] eqn:LEAF.
  - intro CHECK; inversion CHECK; subst outers description.
    destruct (@checked_double_initialized_reduction_sound p controls source leaf LEAF) as [CODE REST].
    split; [exact CODE|]; split; [rewrite app_nil_r, <- CODE; exact LEAF|exact I].
  - destruct (double_initialized_outer_shape source) as [[iterator body]|]; [|discriminate].
    destruct (negb (existsb (Pos.eqb iterator) controls)) eqn:FRESH; [|discriminate].
    destruct (checked_double_initialized_nest_with_fuel fuel p (controls++[iterator]) body)
      as [[tail leaf]|] eqn:CHILD; [|discriminate].
    destruct (statement_eq source (double_initialized_nest_code (iterator::tail) leaf)) as [CODE|]; [|discriminate].
    intro CHECK; inversion CHECK; subst outers description.
    destruct (@IH p (controls++[iterator]) body tail leaf CHILD) as [BODY [CHECKED REST]].
    split; [exact CODE|]; split.
    + replace (controls++iterator::tail) with ((controls++[iterator])++tail) by (rewrite <- app_assoc; reflexivity).
      exact CHECKED.
    + cbn [double_initialized_nest_fresh]; split; [|exact REST].
      apply negb_true_iff in FRESH; intro MEMBER.
      assert (FOUND : existsb (Pos.eqb iterator) controls=true).
      { apply existsb_exists; exists iterator; split; [exact MEMBER|apply Pos.eqb_refl]. }
      congruence.
Qed.
Theorem checked_double_initialized_nest_sound p controls source outers description :
  checked_double_initialized_nest p controls source=Some (outers,description) ->
  source=double_initialized_nest_code outers description /\
  checked_double_initialized_reduction p (controls++outers) (double_initialized_reduction_code description)=Some description /\
  double_initialized_nest_fresh controls outers.
Proof. apply double_initialized_nest_with_fuel_sound. Qed.

Lemma double_initialized_nest_fresh_disjoint controls outers :
  double_initialized_nest_fresh controls outers -> forall identifier, In identifier outers -> ~ In identifier controls.
Proof.
  revert controls; induction outers as [|iterator rest IH]; intros controls FRESH identifier MEMBER; [contradiction|].
  destruct FRESH as [HEAD TAIL]; cbn in MEMBER; destruct MEMBER as [SAME|MEMBER]; [subst; exact HEAD|].
  intro OLD; apply (@IH (controls++[iterator]) TAIL identifier MEMBER); apply in_or_app; auto.
Qed.
Lemma double_initialized_nest_fresh_nodup controls outers :
  double_initialized_nest_fresh controls outers -> NoDup outers.
Proof.
  revert controls; induction outers as [|iterator rest IH]; intros controls FRESH; [constructor|].
  destruct FRESH as [HEAD TAIL]; constructor.
  - intro MEMBER; apply (@double_initialized_nest_fresh_disjoint (controls++[iterator]) rest TAIL iterator MEMBER).
    apply in_or_app; right; cbn; auto.
  - exact (@IH (controls++[iterator]) TAIL).
Qed.
Lemma double_initialized_nest_quiet outers description :
  quiet_statement (initialized_reduction_initializer description)=true ->
  quiet_statement (initialized_reduction_body description)=true ->
  quiet_statement (double_initialized_nest_code outers description)=true.
Proof.
  intros INITIAL BODY; induction outers as [|iterator rest IH];
    cbn [double_initialized_nest_code]; unfold double_initialized_reduction_code,memory_long_initialized_loop,
      memory_long_frontend_loop; cbn [quiet_statement]; rewrite ?INITIAL,?BODY,?IH; reflexivity.
Qed.
Lemma checked_double_initialized_nest_normal p controls source outers description :
  checked_double_initialized_nest p controls source=Some (outers,description) -> normal_statement source=true.
Proof.
  intro CHECK; destruct (@checked_double_initialized_nest_sound p controls source outers description CHECK)
    as [CODE [LEAF FRESH]]; rewrite CODE.
  destruct (@checked_double_initialized_reduction_sound p (controls++outers)
    (double_initialized_reduction_code description) description LEAF) as [_ [IC [BC STATIC]]].
  destruct (@checked_double_source_instruction_sound p (controls++outers) (initialized_reduction_initializer description)
    (initialized_reduction_initial_instruction description) IC) as [IDEC _].
  destruct (@checked_double_source_instruction_sound p ((controls++outers)++[initialized_reduction_iterator description])
    (initialized_reduction_body description) (initialized_reduction_body_instruction description) BC) as [BDEC _].
  destruct (@decoded_double_assignment_shape (initialized_reduction_initializer description)
    (double_source_assignment (initialized_reduction_initial_instruction description)) IDEC) as [rhs [INITIAL TYPE]].
  destruct (@decoded_double_assignment_shape (initialized_reduction_body description)
    (double_source_assignment (initialized_reduction_body_instruction description)) BDEC) as [rhs' [BODY TYPE']].
  destruct outers as [|iterator rest].
  - cbn [double_initialized_nest_code]; unfold double_initialized_reduction_code,memory_long_initialized_loop,
      memory_long_frontend_loop; rewrite INITIAL,BODY; reflexivity.
  - cbn [double_initialized_nest_code]; unfold memory_long_initialized_loop,memory_long_frontend_loop;
      cbn [normal_statement quiet_statement].
    rewrite (@double_initialized_nest_quiet rest description ltac:(rewrite INITIAL; reflexivity)
      ltac:(rewrite BODY; reflexivity)); reflexivity.
Qed.
Lemma checked_double_initialized_nest_writes p controls source outers description :
  checked_double_initialized_nest p controls source=Some (outers,description) ->
  writes_only (outers++[initialized_reduction_iterator description]) source.
Proof.
  intro CHECK; destruct (@checked_double_initialized_nest_sound p controls source outers description CHECK)
    as [CODE [LEAF FRESH]]; rewrite CODE.
  destruct (@checked_double_initialized_reduction_sound p (controls++outers)
    (double_initialized_reduction_code description) description LEAF) as [_ [IC [BC STATIC]]].
  destruct (@checked_double_source_instruction_sound p (controls++outers) (initialized_reduction_initializer description)
    (initialized_reduction_initial_instruction description) IC) as [IDEC _].
  destruct (@checked_double_source_instruction_sound p ((controls++outers)++[initialized_reduction_iterator description])
    (initialized_reduction_body description) (initialized_reduction_body_instruction description) BC) as [BDEC _].
  destruct (@decoded_double_assignment_shape (initialized_reduction_initializer description)
    (double_source_assignment (initialized_reduction_initial_instruction description)) IDEC) as [rhs [INITIAL TYPE]].
  destruct (@decoded_double_assignment_shape (initialized_reduction_body description)
    (double_source_assignment (initialized_reduction_body_instruction description)) BDEC) as [rhs' [BODY TYPE']].
  clear CHECK CODE LEAF FRESH IC BC STATIC IDEC BDEC.
  induction outers as [|iterator rest IH]; cbn [double_initialized_nest_code app].
  - unfold double_initialized_reduction_code,memory_long_initialized_loop,memory_long_frontend_loop,memory_long_increment.
    rewrite INITIAL,BODY; repeat first [apply writes_sequence|apply writes_loop|apply writes_if|
      apply writes_assign|apply writes_skip|apply writes_break|apply writes_set]; cbn; auto.
  - unfold memory_long_initialized_loop,memory_long_frontend_loop,memory_long_increment.
    repeat first [apply writes_sequence|apply writes_loop|apply writes_if|apply writes_skip|apply writes_break|apply writes_set];
      try solve [cbn; auto].
    eapply writes_only_weaken; [|exact IH]; intros identifier MEMBER; cbn; auto.
Qed.

Print Assumptions checked_double_initialized_nest_sound.
Print Assumptions double_initialized_nest_fresh_disjoint.
Print Assumptions double_initialized_nest_fresh_nodup.
Print Assumptions checked_double_initialized_nest_normal.
Print Assumptions checked_double_initialized_nest_writes.
