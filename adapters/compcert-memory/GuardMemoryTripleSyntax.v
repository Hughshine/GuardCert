From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightSyntaxEquality ClightFrontendRegion ClightFrontendLoopProtocol
  ClightStraightLine ClightRectangularLoops ClightCountedLoop ClightRectangularStore.
From GuardMemory Require Import GuardMemoryRegistryBackend GuardMemoryLayoutRegistry GuardMemoryNaryAffineAccess
  GuardMemoryNaryCompute GuardMemoryNaryComputeSyntax GuardMemoryNarySequence GuardMemoryNaryBodyModel.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Record memory_triple_description := MemoryTripleDescription {
  triple_row : ident; triple_row_bound : ident;
  triple_column : ident; triple_column_bound : ident;
  triple_depth : ident; triple_depth_bound : ident;
  triple_body : statement; triple_middle_body : statement; triple_outer_body : statement;
  triple_cap : Z
}.
Definition memory_triple_described_source d := frontend_counted_loop (triple_row d) (triple_row_bound d) (triple_outer_body d).
Definition memory_triple_layout d := [triple_row d;triple_column d;triple_depth d].
Definition memory_triple_limits d := [triple_cap d;triple_cap d;triple_cap d].
Record memory_triple_region_certificate source d := MemoryTripleRegionCertificate {
  triple_region_source : source = memory_triple_described_source d;
  triple_region_model : memory_nary_body_model (memory_triple_limits d) (memory_triple_layout d) (triple_body d);
  triple_region_cap : 0 < triple_cap d /\ signed_range (triple_cap d);
  triple_region_middle : flatten_region (triple_middle_body d) =
    [rectangle_reset (triple_depth d);frontend_counted_loop (triple_depth d) (triple_depth_bound d) (triple_body d)];
  triple_region_outer : flatten_region (triple_outer_body d) =
    [rectangle_reset (triple_column d);frontend_counted_loop (triple_column d) (triple_column_bound d) (triple_middle_body d)];
  triple_region_rc : triple_row d <> triple_column d;
  triple_region_rd : triple_row d <> triple_depth d;
  triple_region_rn : triple_row d <> triple_row_bound d;
  triple_region_rm : triple_row d <> triple_column_bound d;
  triple_region_rl : triple_row d <> triple_depth_bound d;
  triple_region_cd : triple_column d <> triple_depth d;
  triple_region_cm : triple_column d <> triple_column_bound d;
  triple_region_cl : triple_column d <> triple_depth_bound d;
  triple_region_cn : triple_column d <> triple_row_bound d;
  triple_region_dl : triple_depth d <> triple_depth_bound d;
  triple_region_dm : triple_depth d <> triple_column_bound d;
  triple_region_dn : triple_depth d <> triple_row_bound d
}.
Record memory_triple_region_package source := MemoryTripleRegionPackage {
  triple_region_description : memory_triple_description;
  triple_region_syntax : memory_triple_region_certificate source triple_region_description
}.
Definition memory_triple_region_model source (package : memory_triple_region_package source) := triple_region_model (triple_region_syntax package).
Definition memory_triple_region_instructions source (package : memory_triple_region_package source) := nary_body_instructions (memory_triple_region_model package).
Definition memory_triple_region_descriptors source (package : memory_triple_region_package source) := nary_body_descriptors (memory_triple_region_model package).

Definition propose_memory_nary_access_cap access :=
  let term := memory_nary_access_index access in
  Z.max 1 ((rectangle_extent (memory_nary_access_shape access)-snd term-1) /
    Z.max 1 (fold_right Z.add 0 (fst term))+1).
Definition propose_memory_triple_cap operations :=
  fold_left Z.min (map propose_memory_nary_access_cap
    (flat_map (fun operation => memory_nary_compute_write operation::memory_nary_compute_reads operation) operations)) Int.max_signed.
Definition propose_memory_triple_region source :=
  match propose_frontend_shape source with
  | Some (row,row_bound,outer_body) => match flatten_region outer_body with
      | [Sset column _;column_loop] => match propose_frontend_shape column_loop with
          | Some (_,column_bound,middle_body) => match flatten_region middle_body with
              | [Sset depth _;depth_loop] => match propose_frontend_shape depth_loop with
                  | Some (_,depth_bound,body) => match propose_memory_nary_computes [row;column;depth] (flatten_region body) with
                      | Some (operation::operations) => let all := operation::operations in
                          Some (MemoryTripleDescription row row_bound column column_bound depth depth_bound
                            body middle_body outer_body (propose_memory_triple_cap all),all)
                      | _ => None end
                  | _ => None end
              | _ => None end
          | _ => None end
      | _ => None end
  | _ => None end.

Definition check_memory_triple_region source (d : memory_triple_description) (operations : list memory_nary_compute) : option (memory_triple_region_package source).
Proof.
  destruct (statement_eq source (memory_triple_described_source d)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (triple_body d)) (map memory_nary_compute_statement operations)) as [BODY|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (triple_middle_body d))
    [rectangle_reset (triple_depth d);frontend_counted_loop (triple_depth d) (triple_depth_bound d) (triple_body d)]) as [MIDDLE|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (triple_outer_body d))
    [rectangle_reset (triple_column d);frontend_counted_loop (triple_column d) (triple_column_bound d) (triple_middle_body d)]) as [OUTER|]; [|exact None].
  destruct (peq (triple_row d) (triple_column d)) as [|RC]; [exact None|].
  destruct (peq (triple_row d) (triple_depth d)) as [|RD]; [exact None|].
  destruct (peq (triple_row d) (triple_row_bound d)) as [|RN]; [exact None|].
  destruct (peq (triple_row d) (triple_column_bound d)) as [|RM]; [exact None|].
  destruct (peq (triple_row d) (triple_depth_bound d)) as [|RL]; [exact None|].
  destruct (peq (triple_column d) (triple_depth d)) as [|CD]; [exact None|].
  destruct (peq (triple_column d) (triple_column_bound d)) as [|CM]; [exact None|].
  destruct (peq (triple_column d) (triple_depth_bound d)) as [|CL]; [exact None|].
  destruct (peq (triple_column d) (triple_row_bound d)) as [|CN]; [exact None|].
  destruct (peq (triple_depth d) (triple_depth_bound d)) as [|DL]; [exact None|].
  destruct (peq (triple_depth d) (triple_column_bound d)) as [|DM]; [exact None|].
  destruct (peq (triple_depth d) (triple_row_bound d)) as [|DN]; [exact None|].
  destruct ((0 <? triple_cap d) && (triple_cap d <=? Int.max_signed)) eqn:CAP; [|exact None].
  destruct (forallb (memory_nary_compute_check (memory_triple_limits d) (memory_triple_layout d)) operations) eqn:REQUESTS; [|exact None].
  destruct (memory_descriptors_cover_check (memory_unique_descriptors (memory_nary_compute_sequence_anchors operations))
    (memory_nary_compute_sequence_requests operations)) eqn:COVER; [|exact None].
  assert (VALID : 0 < triple_cap d /\ signed_range (triple_cap d)).
  { apply andb_true_iff in CAP as [POS LIMIT]; apply Z.ltb_lt in POS; apply Z.leb_le in LIMIT;
    unfold signed_range; change Int.min_signed with (-2147483648); split; lia. }
  assert (CERT : Forall (memory_nary_compute_valid (memory_triple_limits d) (memory_triple_layout d)) operations).
  { apply Forall_forall; intros operation MEMBER; apply memory_nary_compute_check_sound.
    apply forallb_forall with (x := operation) in REQUESTS; assumption. }
  pose proof (@memory_descriptors_cover_check_sound (memory_unique_descriptors (memory_nary_compute_sequence_anchors operations))
    (memory_nary_compute_sequence_requests operations) COVER) as COVERED.
  exact (Some (@MemoryTripleRegionPackage source d
    (@MemoryTripleRegionCertificate source d SOURCE
      (@memory_nary_compute_body_model (memory_triple_limits d) operations (memory_triple_layout d) (triple_body d) CERT COVERED BODY)
      VALID MIDDLE OUTER RC RD RN RM RL CD CM CL CN DL DM DN))).
Defined.
Definition describe_memory_triple_region source := match propose_memory_triple_region source with
  | Some (d,operations) => check_memory_triple_region source d operations | None => None end.
Print Assumptions check_memory_triple_region.
