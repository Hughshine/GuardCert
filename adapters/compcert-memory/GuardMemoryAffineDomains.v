From Stdlib Require Import List Bool ZArith Lia Sorting.Sorted.
From polcert.lib Require Import Linalg LinalgExt.
From GuardMemory Require Import GuardMemoryPolyhedral GuardMemoryPolyhedralRectangles
  GuardMemoryTiledRectangles.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Intersect an existing finite affine domain with additional constraints.
    This retains the instruction, schedule and actual point-space witness. *)
Definition restrict_memory_instruction (extra : list (list Z * Z)) (instruction : PL.PolyInstr) :=
  {| PL.pi_depth := PL.pi_depth instruction; PL.pi_instr := PL.pi_instr instruction;
     PL.pi_poly := PL.pi_poly instruction ++ extra;
     PL.pi_schedule := PL.pi_schedule instruction;
     PL.pi_point_witness := PL.pi_point_witness instruction;
     PL.pi_transformation := PL.pi_transformation instruction;
     PL.pi_access_transformation := PL.pi_access_transformation instruction;
     PL.pi_waccess := PL.pi_waccess instruction;
     PL.pi_raccess := PL.pi_raccess instruction |}.
Definition restrict_memory_points extra points :=
  filter (fun point => in_poly (PL.ip_index point) extra) points.

Lemma restrict_memory_belongs extra instruction point :
  PL.belongs_to point (restrict_memory_instruction extra instruction) <->
  PL.belongs_to point instruction /\ in_poly (PL.ip_index point) extra = true.
Proof.
  unfold PL.belongs_to,restrict_memory_instruction; cbn -[in_poly PL.current_transformation_of].
  change ((in_poly (PL.ip_index point) (PL.pi_poly instruction ++ extra) = true /\
    PL.ip_transformation point = PL.current_transformation_of instruction (PL.ip_index point) /\
    PL.ip_time_stamp point = affine_product (PL.pi_schedule instruction) (PL.ip_index point) /\
    PL.ip_instruction point = PL.pi_instr instruction /\ PL.ip_depth point = PL.pi_depth instruction) <->
    (in_poly (PL.ip_index point) (PL.pi_poly instruction) = true /\
    PL.ip_transformation point = PL.current_transformation_of instruction (PL.ip_index point) /\
    PL.ip_time_stamp point = affine_product (PL.pi_schedule instruction) (PL.ip_index point) /\
    PL.ip_instruction point = PL.pi_instr instruction /\ PL.ip_depth point = PL.pi_depth instruction) /\
    in_poly (PL.ip_index point) extra = true).
  rewrite in_poly_app,andb_true_iff; tauto.
Qed.

Theorem flatten_memory_restricted_domains parameters instructions points extra :
  PL.flatten_instrs parameters instructions points ->
  PL.flatten_instrs parameters (map (restrict_memory_instruction extra) instructions)
    (restrict_memory_points extra points).
Proof.
  intros [PREFIX [MEMBERS [UNIQUE ORDER]]]; unfold PL.flatten_instrs,restrict_memory_points; split.
  - intros point MEMBER; apply filter_In in MEMBER as [MEMBER KEEP]; apply PREFIX; exact MEMBER.
  - split.
    + intro point; rewrite filter_In; split.
      * intros [MEMBER KEEP]; apply MEMBERS in MEMBER as [instruction [NTH [ENV [BELONG LENGTH]]]].
        exists (restrict_memory_instruction extra instruction); split.
        -- rewrite nth_error_map,NTH; reflexivity.
        -- split; [exact ENV|]; split; [apply restrict_memory_belongs; auto|exact LENGTH].
      * intros [instruction [NTH [ENV [BELONG LENGTH]]]].
        rewrite nth_error_map in NTH.
        destruct (nth_error instructions (PL.ip_nth point)) as [original|] eqn:ORIGINAL;
          cbn in NTH; try discriminate; inversion NTH; subst instruction.
        apply restrict_memory_belongs in BELONG as [BELONG KEEP]; split; [|exact KEEP].
        apply MEMBERS; exists original; split; [exact ORIGINAL|].
        split; [exact ENV|]; split; [exact BELONG|exact LENGTH].
    + split.
      * apply NoDup_filter; exact UNIQUE.
      * apply StronglySorted_Sorted, memory_strongly_sorted_filter.
        apply Sorted_StronglySorted; [exact PL.np_lt_trans|exact ORDER].
Qed.

Definition affine_cut_constraint (row_coefficient column_coefficient limit : Z) :=
  ([0;0;row_coefficient;column_coefficient],limit).
Definition tiled_affine_cut_constraint (row_coefficient column_coefficient limit : Z) :=
  ([0;0;0;0;row_coefficient;column_coefficient],limit).
Lemma affine_cut_at row_coefficient column_coefficient limit n m i j :
  in_poly [n;m;i;j] [affine_cut_constraint row_coefficient column_coefficient limit] =
  (row_coefficient*i+column_coefficient*j <=? limit).
Proof.
  unfold in_poly,affine_cut_constraint,satisfies_constraint; cbn -[Z.add Z.mul Z.sub Z.leb].
  rewrite andb_true_r; f_equal; ring.
Qed.
Lemma tiled_affine_cut_at row_coefficient column_coefficient limit n m ti tj i j :
  in_poly [n;m;ti;tj;i;j] [tiled_affine_cut_constraint row_coefficient column_coefficient limit] =
  (row_coefficient*i+column_coefficient*j <=? limit).
Proof.
  unfold in_poly,tiled_affine_cut_constraint,satisfies_constraint; cbn -[Z.add Z.mul Z.sub Z.leb].
  rewrite andb_true_r; f_equal; ring.
Qed.

Print Assumptions flatten_memory_restricted_domains.
Print Assumptions affine_cut_at.
