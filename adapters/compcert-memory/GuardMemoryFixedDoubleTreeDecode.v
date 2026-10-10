From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Integers.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightSyntaxEquality.
From GuardMemory Require Import GuardMemoryFixedDoubleTreeData GuardMemoryDoubleSourceTreeData
  GuardMemoryDoubleSourceTreeDecode GuardMemoryDoubleSourceInstruction GuardMemoryLongSourceAffine.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Record fixed_double_range_proposal := FixedDoubleRangeProposal {
  fixed_range_raw : bool; fixed_range_iterator : AST.ident; fixed_range_start : int;
  fixed_range_bound : expr; fixed_range_body : statement
}.
Definition propose_fixed_double_range source := match source with
  | Ssequence (Sset iterator (Ecast (Econst_int start _) _))
      (Sloop (Ssequence (Sifthenelse (Ebinop Cop.Olt _ bound _) Sskip Sbreak) body) _) =>
      Some (FixedDoubleRangeProposal false iterator start bound body)
  | Ssequence (Ssequence Sskip (Sset iterator (Ecast (Econst_int start _) _)))
      (Sloop (Ssequence (Ssequence Sskip (Sifthenelse (Ebinop Cop.Olt _ bound _) Sskip Sbreak)) body)
        (Ssequence Sskip _)) =>
      Some (FixedDoubleRangeProposal true iterator start bound body)
  | _ => None end.
Definition fixed_double_source_tree_decode_step p
  (recurse : list AST.ident -> statement -> option fixed_double_source_tree) controls source :=
  if statement_eq source Sskip then Some FixedDoubleSkip else
  match checked_double_source_instruction p controls source with
  | Some instruction => Some (FixedDoublePoint source instruction)
  | None => match propose_fixed_double_range source with
    | Some proposal =>
      if in_dec peq (fixed_range_iterator proposal) controls then None else
      match decode_long_source_index [] (fixed_range_bound proposal) with
      | Some ([],upper) =>
        if (Int.min_signed <=? upper) && (upper <=? Int.max_signed) then
          match recurse (controls++[fixed_range_iterator proposal]) (fixed_range_body proposal) with
          | Some child => let tree := FixedDoubleRange (fixed_range_raw proposal) (fixed_range_iterator proposal)
              (fixed_range_start proposal) (fixed_range_bound proposal) upper child in
              if statement_eq source (fixed_double_source_tree_code tree) then Some tree else None
          | None => None end else None
      | _ => None end
    | None => match source with
      | Ssequence first second => match recurse controls first,recurse controls second with
        | Some left_tree,Some right_tree => Some (FixedDoubleSequence left_tree right_tree)
        | _,_ => None end
      | _ => None end end end.

Theorem fixed_double_source_tree_decode_step_sound p recurse :
  (forall controls source tree, recurse controls source=Some tree ->
    source=fixed_double_source_tree_code tree /\ fixed_double_source_tree_checked p controls tree) ->
  forall controls source tree, fixed_double_source_tree_decode_step p recurse controls source=Some tree ->
    source=fixed_double_source_tree_code tree /\ fixed_double_source_tree_checked p controls tree.
Proof.
  intros CHILD controls source tree; unfold fixed_double_source_tree_decode_step.
  destruct (statement_eq source Sskip) as [SKIP|NOT_SKIP].
  - intro RESULT; inversion RESULT; subst tree; split; [exact SKIP|exact I].
  - destruct (checked_double_source_instruction p controls source) as [instruction|] eqn:POINT.
    + intro RESULT; inversion RESULT; subst tree; split; [reflexivity|exact POINT].
    + destruct (propose_fixed_double_range source) as [proposal|] eqn:RANGE.
      * destruct (in_dec peq (fixed_range_iterator proposal) controls) as [BOUND|FRESH]; try discriminate.
        destruct (decode_long_source_index [] (fixed_range_bound proposal)) as [[coefficients upper]|] eqn:DECODE;
          try discriminate; destruct coefficients; try discriminate.
        destruct ((Int.min_signed <=? upper) && (upper <=? Int.max_signed)) eqn:LIMIT; try discriminate.
        destruct (recurse (controls++[fixed_range_iterator proposal]) (fixed_range_body proposal)) as [child|] eqn:RECURSE;
          try discriminate.
        destruct (statement_eq source (fixed_double_source_tree_code
          (FixedDoubleRange (fixed_range_raw proposal) (fixed_range_iterator proposal) (fixed_range_start proposal)
            (fixed_range_bound proposal) upper child))) as [SHAPE|]; try discriminate.
        intro RESULT; inversion RESULT; subst tree; split; [exact SHAPE|].
        destruct (CHILD _ _ _ RECURSE) as [_ CHECK].
        apply andb_true_iff in LIMIT as [LOWER UPPER]; apply Z.leb_le in LOWER,UPPER.
        cbn [fixed_double_source_tree_checked]; repeat split; assumption.
      * destruct source; try discriminate.
        destruct (recurse controls source1) as [first|] eqn:FIRST; try discriminate.
        destruct (recurse controls source2) as [second|] eqn:SECOND; try discriminate.
        intro RESULT; inversion RESULT; subst tree.
        destruct (CHILD _ _ _ FIRST) as [SHAPE1 CHECK1], (CHILD _ _ _ SECOND) as [SHAPE2 CHECK2].
        split; [cbn; congruence|split; assumption].
Qed.
Fixpoint fixed_double_source_tree_decode_fuel p fuel controls source := match fuel with
  | O => None
  | S remaining => fixed_double_source_tree_decode_step p (fixed_double_source_tree_decode_fuel p remaining) controls source end.
Theorem fixed_double_source_tree_decode_fuel_sound p fuel controls source tree :
  fixed_double_source_tree_decode_fuel p fuel controls source=Some tree ->
  source=fixed_double_source_tree_code tree /\ fixed_double_source_tree_checked p controls tree.
Proof.
  revert controls source tree; induction fuel; intros controls source tree DECODE; [discriminate|].
  eapply fixed_double_source_tree_decode_step_sound; [exact IHfuel|exact DECODE].
Qed.
Definition checked_fixed_double_source_tree p source :=
  match fixed_double_source_tree_decode_fuel p (double_source_tree_statement_depth source) [] source with
  | Some tree => if double_source_tree_layout_check (fixed_double_tree_skeleton tree) then Some tree else None
  | None => None end.
Theorem checked_fixed_double_source_tree_sound p source tree :
  checked_fixed_double_source_tree p source=Some tree ->
  source=fixed_double_source_tree_code tree /\ fixed_double_source_tree_checked p [] tree /\
  double_source_tree_layout_check (fixed_double_tree_skeleton tree)=true.
Proof.
  unfold checked_fixed_double_source_tree.
  destruct (fixed_double_source_tree_decode_fuel p (double_source_tree_statement_depth source) [] source)
    as [decoded|] eqn:DECODE; [|discriminate].
  destruct (double_source_tree_layout_check (fixed_double_tree_skeleton decoded)) eqn:LAYOUT; [|discriminate].
  intro RESULT; inversion RESULT; subst decoded.
  destruct (@fixed_double_source_tree_decode_fuel_sound p (double_source_tree_statement_depth source) [] source tree DECODE)
    as [SHAPE CHECK]; auto.
Qed.

Print Assumptions fixed_double_source_tree_decode_step_sound.
Print Assumptions fixed_double_source_tree_decode_fuel_sound.
Print Assumptions checked_fixed_double_source_tree_sound.
