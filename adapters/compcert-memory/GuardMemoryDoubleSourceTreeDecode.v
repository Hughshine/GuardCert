From Stdlib Require Import List Bool Arith.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightSyntaxEquality.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleSourceInstruction GuardMemoryDoubleProgramBindings
  GuardMemoryDoubleSourceTreeData.
Import ListNotations.
Set Implicit Arguments.

Definition propose_double_tree_bound source := match source with
  | Evar header _=>Some (DoubleTreeBound header None)
  | Ebinop Osub (Evar header _) (Econst_int offset _) _=>Some (DoubleTreeBound header (Some offset))
  | _=>None end.
Record double_tree_range_proposal := DoubleTreeRangeProposal {
  tree_range_raw : bool; tree_range_iterator : ident; tree_range_start : int;
  tree_range_bound : double_tree_bound; tree_range_body : statement
}.
Definition propose_double_tree_range source := match source with
  | Ssequence (Sset iterator (Ecast (Econst_int start _) _))
      (Sloop (Ssequence (Sifthenelse (Ebinop Olt _ bound _) Sskip Sbreak) body) _) =>
      option_map (fun bound=>DoubleTreeRangeProposal false iterator start bound body) (propose_double_tree_bound bound)
  | Ssequence (Ssequence Sskip (Sset iterator (Ecast (Econst_int start _) _)))
      (Sloop (Ssequence (Ssequence Sskip (Sifthenelse (Ebinop Olt _ bound _) Sskip Sbreak)) body)
        (Ssequence Sskip _)) =>
      option_map (fun bound=>DoubleTreeRangeProposal true iterator start bound body) (propose_double_tree_bound bound)
  | _=>None end.

(** Proposals may ignore fields; the complete statement reconstruction gate is
    authoritative, including comparison, initializer, increment and types. *)
Definition double_source_tree_decode_step p
  (recurse : list ident -> statement -> option double_source_tree) controls source :=
  if statement_eq source Sskip then Some DoubleTreeSkip else
  match checked_double_source_instruction p controls source with
  | Some instruction=>Some (DoubleTreePoint source instruction)
  | None=>match propose_double_tree_range source with
    | Some proposal=>
        if in_dec peq (tree_range_iterator proposal) controls then None else
        if global_declaration_check p (tree_bound_header (tree_range_bound proposal),memory_long_type) then
          match recurse (controls++[tree_range_iterator proposal]) (tree_range_body proposal) with
          | Some child=>let tree := DoubleTreeRange (tree_range_raw proposal) (tree_range_iterator proposal)
              (tree_range_start proposal) (tree_range_bound proposal) child in
              if statement_eq source (double_source_tree_code tree) then Some tree else None
          | None=>None end
        else None
    | None=>match source with
      | Ssequence first second=>match recurse controls first,recurse controls second with
        | Some left_tree,Some right_tree=>Some (DoubleTreeSequence left_tree right_tree) | _,_=>None end
      | _=>None end end end.

Lemma double_source_tree_decode_step_sound p recurse :
  (forall controls source tree, recurse controls source=Some tree ->
    source=double_source_tree_code tree /\ double_source_tree_checked p controls tree) ->
  forall controls source tree, double_source_tree_decode_step p recurse controls source=Some tree ->
    source=double_source_tree_code tree /\ double_source_tree_checked p controls tree.
Proof.
  intros CHILD controls source tree; unfold double_source_tree_decode_step.
  destruct (statement_eq source Sskip) as [SKIP|NOT_SKIP].
  - intro RESULT; inversion RESULT; subst tree; split; [exact SKIP|exact I].
  - destruct (checked_double_source_instruction p controls source) as [instruction|] eqn:POINT.
    + intro RESULT; inversion RESULT; subst tree; split; [reflexivity|exact POINT].
    + destruct (propose_double_tree_range source) as [proposal|] eqn:RANGE.
      * destruct (in_dec peq (tree_range_iterator proposal) controls) as [BOUND|FRESH]; try discriminate.
        destruct (global_declaration_check p (tree_bound_header (tree_range_bound proposal),memory_long_type)) eqn:HEADER;
          try discriminate.
        destruct (recurse (controls++[tree_range_iterator proposal]) (tree_range_body proposal)) as [body|] eqn:BODY;
          try discriminate.
        destruct (statement_eq source (double_source_tree_code (DoubleTreeRange (tree_range_raw proposal)
          (tree_range_iterator proposal) (tree_range_start proposal) (tree_range_bound proposal) body))) as [EXACT|BAD];
          try discriminate.
        intro RESULT; inversion RESULT; subst tree; split; [exact EXACT|].
        cbn [double_source_tree_checked]; split; [exact FRESH|]; split; [exact HEADER|].
        exact (proj2 (CHILD _ _ _ BODY)).
      * destruct source; try discriminate.
        destruct (recurse controls source1) as [first|] eqn:FIRST; try discriminate.
        destruct (recurse controls source2) as [second|] eqn:SECOND; try discriminate.
        intro RESULT; inversion RESULT; subst tree.
        destruct (CHILD _ _ _ FIRST) as [LEFT LEFT_CHECK]; destruct (CHILD _ _ _ SECOND) as [RIGHT RIGHT_CHECK].
        split; [cbn [double_source_tree_code]; rewrite LEFT,RIGHT; reflexivity|split; assumption].
Qed.

Fixpoint double_source_tree_decode_fuel p fuel controls source := match fuel with
  | O=>None
  | S remaining=>double_source_tree_decode_step p (double_source_tree_decode_fuel p remaining) controls source end.
Theorem double_source_tree_decode_fuel_sound p fuel controls source tree :
  double_source_tree_decode_fuel p fuel controls source=Some tree ->
    source=double_source_tree_code tree /\ double_source_tree_checked p controls tree.
Proof.
  revert controls source tree; induction fuel; intros controls source tree DECODE; [discriminate|].
  eapply double_source_tree_decode_step_sound; [exact IHfuel|exact DECODE].
Qed.
Fixpoint double_source_tree_statement_depth source : nat := match source with
  | Ssequence first second | Sloop first second | Sifthenelse _ first second =>
      S (Nat.max (double_source_tree_statement_depth first) (double_source_tree_statement_depth second))
  | _=>1 end.
Definition checked_double_source_tree p source :=
  match double_source_tree_decode_fuel p (double_source_tree_statement_depth source) [] source with
  | Some tree=>if double_source_tree_header_writes_check tree && double_source_tree_layout_check tree
      then Some tree else None
  | None=>None end.
Theorem checked_double_source_tree_sound p source tree :
  checked_double_source_tree p source=Some tree ->
    source=double_source_tree_code tree /\ double_source_tree_checked p [] tree /\
    double_source_tree_header_writes_check tree=true /\ double_source_tree_layout_check tree=true.
Proof.
  unfold checked_double_source_tree; destruct (double_source_tree_decode_fuel p (double_source_tree_statement_depth source) [] source)
    as [decoded|] eqn:DECODE; try discriminate.
  destruct (double_source_tree_header_writes_check decoded && double_source_tree_layout_check decoded) eqn:CHECK;
    try discriminate; intro RESULT; inversion RESULT; subst decoded.
  destruct (@double_source_tree_decode_fuel_sound p (double_source_tree_statement_depth source) [] source tree DECODE)
    as [SOURCE TREE]; apply andb_true_iff in CHECK; tauto.
Qed.

Print Assumptions double_source_tree_decode_step_sound.
Print Assumptions double_source_tree_decode_fuel_sound.
Print Assumptions checked_double_source_tree_sound.
