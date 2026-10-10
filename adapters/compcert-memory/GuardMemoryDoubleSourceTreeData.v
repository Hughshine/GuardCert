From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightRegionProgress ClightTempFrame.
From GuardMemory Require Import GuardMemoryValueInstr GuardMemoryDoubleLocations
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleAssignmentFactory GuardMemoryDoubleProgramBindings
  GuardMemoryLongControl GuardMemoryLongLoopControl GuardMemoryLongRangeSource GuardMemoryLongRangeCaptureSource.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Record double_tree_bound := DoubleTreeBound {
  tree_bound_header : ident;
  tree_bound_offset : option int
}.
Definition double_tree_bound_code bound := match tree_bound_offset bound with
  | None=>Evar (tree_bound_header bound) memory_long_type
  | Some offset=>memory_long_offset_bound (tree_bound_header bound) offset end.
Definition double_tree_bound_value (valuation : ident -> Z) bound :=
  valuation (tree_bound_header bound)-match tree_bound_offset bound with None=>0 | Some offset=>Int.signed offset end.
Lemma double_tree_bound_type bound : typeof (double_tree_bound_code bound)=memory_long_type.
Proof. destruct bound as [header [offset|]]; reflexivity. Qed.

(** Raw/canonical mode preserves the actual frontend control shape. Skip
    nodes and both sides of a sequence remain part of one source region. *)
Inductive double_source_tree :=
| DoubleTreeSkip
| DoubleTreePoint (body : statement) (instruction : double_source_instruction)
| DoubleTreeSequence (first second : double_source_tree)
| DoubleTreeRange (raw : bool) (iterator : ident) (start : int)
    (bound : double_tree_bound) (child : double_source_tree).
Definition double_tree_initial start := Ecast (Econst_int start memory_signed_int_type) memory_long_type.
Fixpoint double_source_tree_code tree := match tree with
  | DoubleTreeSkip=>Sskip
  | DoubleTreePoint body _=>body
  | DoubleTreeSequence first second=>Ssequence (double_source_tree_code first) (double_source_tree_code second)
  | DoubleTreeRange raw iterator start bound child=>
      if raw then long_raw_from_loop iterator (double_tree_initial start) (double_tree_bound_code bound)
        (double_source_tree_code child)
      else memory_long_from_loop iterator (double_tree_initial start)
        (Ebinop Olt (Etempvar iterator memory_long_type) (double_tree_bound_code bound) memory_signed_int_type)
        (double_source_tree_code child)
  end.
Fixpoint double_source_tree_writes tree : list ident := match tree with
  | DoubleTreeSkip | DoubleTreePoint _ _=>[]
  | DoubleTreeSequence first second=>double_source_tree_writes first++double_source_tree_writes second
  | DoubleTreeRange _ iterator _ _ child=>iterator::double_source_tree_writes child end.
Fixpoint double_source_tree_headers tree : list ident := match tree with
  | DoubleTreeSkip | DoubleTreePoint _ _=>[]
  | DoubleTreeSequence first second=>double_source_tree_headers first++double_source_tree_headers second
  | DoubleTreeRange _ _ _ bound child=>tree_bound_header bound::double_source_tree_headers child end.
Fixpoint double_source_tree_instructions tree : list double_source_instruction := match tree with
  | DoubleTreeSkip=>[]
  | DoubleTreePoint _ instruction=>[instruction]
  | DoubleTreeSequence first second=>double_source_tree_instructions first++double_source_tree_instructions second
  | DoubleTreeRange _ _ _ _ child=>double_source_tree_instructions child end.
Definition double_source_tree_accesses tree :=
  flat_map double_source_instruction_accesses (double_source_tree_instructions tree).
Definition double_source_tree_layouts tree := double_source_layouts (double_source_tree_accesses tree).
Definition double_source_tree_parameters tree := nodup peq (double_source_tree_headers tree).

Fixpoint double_source_tree_checked p controls tree : Prop := match tree with
  | DoubleTreeSkip=>True
  | DoubleTreePoint body instruction=>checked_double_source_instruction p controls body=Some instruction
  | DoubleTreeSequence first second=>double_source_tree_checked p controls first /\ double_source_tree_checked p controls second
  | DoubleTreeRange _ iterator _ bound child=>
      ~ In iterator controls /\ global_declaration_check p (tree_bound_header bound,memory_long_type)=true /\
      double_source_tree_checked p (controls++[iterator]) child end.
Definition double_source_tree_header_writes_check tree := forallb
  (fun instruction=>forallb (fun header=>negb (Pos.eqb
    (fst (value_instruction_write (double_source_instruction_model instruction))) header))
    (double_source_tree_parameters tree)) (double_source_tree_instructions tree).
Definition double_source_tree_layout_check tree :=
  double_source_layout_check (double_source_tree_layouts tree) (double_source_tree_accesses tree).
Theorem double_source_tree_header_writes_check_sound tree :
  double_source_tree_header_writes_check tree=true ->
  forall instruction header, In instruction (double_source_tree_instructions tree) ->
    In header (double_source_tree_parameters tree) ->
    fst (value_instruction_write (double_source_instruction_model instruction))<>header.
Proof.
  intros CHECK instruction header POINT HEADER; unfold double_source_tree_header_writes_check in CHECK.
  apply forallb_forall with (x:=instruction) in CHECK; [|exact POINT].
  apply forallb_forall with (x:=header) in CHECK; [|exact HEADER].
  apply negb_true_iff in CHECK; apply Pos.eqb_neq; exact CHECK.
Qed.
Theorem double_source_tree_parameter_membership tree header :
  In header (double_source_tree_parameters tree) <-> In header (double_source_tree_headers tree).
Proof. unfold double_source_tree_parameters; apply nodup_In. Qed.
Theorem double_source_tree_parameter_distinct tree : NoDup (double_source_tree_parameters tree).
Proof. unfold double_source_tree_parameters; apply NoDup_nodup. Qed.
Theorem double_source_tree_writes_avoid p controls tree :
  double_source_tree_checked p controls tree -> forall key, In key controls -> ~ In key (double_source_tree_writes tree).
Proof.
  revert controls; induction tree; intros controls CHECK key MEMBER; cbn [double_source_tree_writes]; try tauto.
  - destruct CHECK as [LEFT RIGHT]; intro WRITE; apply in_app_or in WRITE as [WRITE|WRITE];
      [eapply IHtree1|eapply IHtree2]; eauto.
  - destruct CHECK as [FRESH [HEADER CHILD]]; intros [SAME|WRITE].
    + subst key; contradiction.
    + eapply IHtree; [exact CHILD|apply in_or_app; left; exact MEMBER|exact WRITE].
Qed.

Print Assumptions double_tree_bound_type.
Print Assumptions double_source_tree_header_writes_check_sound.
Print Assumptions double_source_tree_parameter_membership.
Print Assumptions double_source_tree_parameter_distinct.
Print Assumptions double_source_tree_writes_avoid.
