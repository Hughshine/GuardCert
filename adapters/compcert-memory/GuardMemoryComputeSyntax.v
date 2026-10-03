From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightSyntaxEquality ClightLoopSyntax ClightFrontendLoopProtocol ClightFrontendRegion
  ClightStraightLine ClightRectangularStore ClightRectangularSelector ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRegistryBackend GuardMemoryAffineSourceExpressions
  GuardMemoryAffineSourceReifier GuardMemoryAffineSourceValuation GuardMemoryAffineAccessExpressions
  GuardMemoryAffineAccess GuardMemoryGeneralLayoutSyntax GuardMemoryOffsetAccessRanges GuardMemoryOffsetSyntax
  GuardMemoryCommonLayout GuardMemoryLayoutRegistry GuardMemorySourceValues GuardMemoryAffineCompute
  GuardMemoryComputeSequence GuardMemoryComputeBodyModel GuardMemoryParametricBody
  GuardMemoryParametricSourceClight GuardMemoryParametricRegion.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint propose_memory_source_value row column (next : nat) source : option (list memory_affine_access * value_expression) :=
  match source with
  | Etempvar identifier _ => if peq identifier row then Some ([],ParameterValue 0)
      else if peq identifier column then Some ([],ParameterValue 1) else None
  | Econst_int value _ => Some ([],ConstantValue (Int.signed value))
  | Eunop Oneg (Econst_int value _) _ => Some ([],ConstantValue (-Int.signed value))
  | Ederef _ _ => option_map (fun access => ([access],LoadedValue next))
      (propose_memory_affine_access row column source)
  | Ebinop operation first second _ => match operation with
      | Oadd | Osub | Omul => match propose_memory_source_value row column next first with
          | Some (reads,lhs) => match propose_memory_source_value row column (next+length reads)%nat second with
              | Some (other,rhs) => Some (reads++other,
                  match operation with Oadd => AddValue lhs rhs | Osub => SubValue lhs rhs | _ => MulValue lhs rhs end)
              | None => None end
          | None => None end
      | _ => None end
  | _ => None end.
Definition propose_memory_compute row column source :=
  match source with
  | Sassign lhs rhs => match propose_memory_affine_access row column lhs,
      propose_memory_source_value row column 0 rhs with
      | Some write,Some (reads,value) => Some (MemoryAffineCompute write reads value rhs)
      | _,_ => None end
  | _ => None end.
Fixpoint propose_memory_computes row column sources := match sources with
  | [] => Some []
  | source::sources => match propose_memory_compute row column source,propose_memory_computes row column sources with
      | Some operation,Some operations => Some (operation::operations) | _,_ => None end end.
Definition memory_compute_check base row column operation :=
  memory_offset_access_check base row column (memory_compute_write operation) &&
  forallb (memory_offset_access_check base row column) (memory_compute_reads operation) &&
  match memory_compile_source_value row column (memory_compute_reads operation) (memory_compute_value operation) with
  | Some code => if expression_eq code (memory_compute_source operation)
      then memory_source_value_reads_check (memory_compute_reads operation) (memory_compute_value operation) else false
  | None => false end.
Lemma memory_compute_check_sound base row column operation :
  memory_compute_check base row column operation = true -> memory_affine_compute_valid base row column operation.
Proof.
  unfold memory_compute_check; rewrite !andb_true_iff; intros [[WRITE READS] VALUE].
  destruct (memory_compile_source_value row column (memory_compute_reads operation) (memory_compute_value operation))
    as [code|] eqn:COMPILE; [|discriminate].
  destruct (expression_eq code (memory_compute_source operation)) as [SAME|]; [|discriminate].
  unfold memory_affine_compute_valid; split; [apply memory_offset_access_check_sound; exact WRITE|].
  split.
  - apply Forall_forall; intros access MEMBER; apply memory_offset_access_check_sound.
    apply forallb_forall with (x := access) in READS; assumption.
  - split; [rewrite SAME in COMPILE; exact COMPILE|exact VALUE].
Qed.
Definition propose_memory_compute_base operation :=
  let bases := map propose_memory_offset_access_base (memory_compute_write operation::memory_compute_reads operation) in
  match bases with base::rest => fold_left memory_common_layout rest base | [] => RectangleShape 1 1 0 0 end.
Definition propose_memory_compute_region source :=
  match propose_frontend_shape source with
  | Some (row,bound,outer_body) => match flatten_region outer_body with
      | [Sset inner_bound expression;Sset column _;inner_loop] =>
          match propose_frontend_shape inner_loop,propose_memory_source_affine expression with
          | Some (_,_,inner_body),Some expression =>
              match propose_memory_computes row column (flatten_region inner_body) with
              | Some (operation::operations) =>
                  let all := operation::operations in
                  let base := fold_left memory_common_layout (map propose_memory_compute_base operations) (propose_memory_compute_base operation) in
                  Some (RectangleDescription base (memory_access_array (memory_compute_write operation))
                    row bound column inner_bound inner_body outer_body,expression,all)
              | _ => None end
          | _,_ => None end
      | _ => None end
  | None => None end.

Definition check_memory_compute_region source (d : rectangle_description) (expression : memory_source_affine)
  (operations : list memory_affine_compute) : option (memory_parametric_region_package source).
Proof.
  destruct (statement_eq source (rectangle_described_source d)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (rectangle_inner_body d))
    (map memory_affine_compute_statement operations)) as [BODY|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (rectangle_described_outer_body d))
    [memory_parametric_setup (rectangle_inner_bound d) (memory_source_affine_code expression); rectangle_reset (rectangle_column d);
      frontend_counted_loop (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d)]) as [OUTER|]; [|exact None].
  destruct (peq (rectangle_row d) (rectangle_bound d)) as [|RN]; [exact None|].
  destruct (peq (rectangle_row d) (rectangle_column d)) as [|RC]; [exact None|].
  destruct (peq (rectangle_bound d) (rectangle_column d)) as [|NC]; [exact None|].
  destruct (peq (rectangle_row d) (rectangle_inner_bound d)) as [|RK]; [exact None|].
  destruct (peq (rectangle_bound d) (rectangle_inner_bound d)) as [|NK]; [exact None|].
  destruct (peq (rectangle_column d) (rectangle_inner_bound d)) as [|CK]; [exact None|].
  destruct (in_dec peq (rectangle_column d) (memory_source_affine_parameters (rectangle_row d) expression)) as [|SC]; [exact None|].
  destruct (in_dec peq (rectangle_inner_bound d) (memory_source_affine_parameters (rectangle_row d) expression)) as [|SK]; [exact None|].
  destruct (rectangle_layout_check (described_shape d)) eqn:LAYOUT; [|exact None].
  destruct (forallb (memory_compute_check (described_shape d) (rectangle_row d) (rectangle_column d)) operations) eqn:REQUESTS; [|exact None].
  destruct (memory_descriptors_cover_check (memory_unique_descriptors (memory_compute_sequence_anchors operations))
    (memory_compute_sequence_requests operations)) eqn:COVER; [|exact None].
  assert (VALID : rectangle_layout_valid (described_shape d)) by (apply rectangle_layout_check_sound; exact LAYOUT).
  assert (CERT : Forall (memory_affine_compute_valid (described_shape d) (rectangle_row d) (rectangle_column d)) operations).
  { apply Forall_forall; intros operation MEMBER; apply memory_compute_check_sound.
    apply forallb_forall with (x := operation) in REQUESTS; assumption. }
  pose proof (@memory_descriptors_cover_check_sound (memory_unique_descriptors (memory_compute_sequence_anchors operations))
    (memory_compute_sequence_requests operations) COVER) as COVERED.
  exact (Some (@MemoryParametricRegionPackage source d expression
    (@MemoryParametricRegionCertificate source d expression SOURCE
      (@memory_compute_body_model (described_shape d) operations (rectangle_row d) (rectangle_column d) (rectangle_inner_body d)
        RC CERT COVERED BODY) VALID OUTER RN RC NC RK NK CK SC SK))).
Defined.
Definition describe_memory_compute_region source :=
  match propose_memory_compute_region source with
  | Some (d,expression,operations) => check_memory_compute_region source d expression operations
  | None => None end.
Print Assumptions check_memory_compute_region.
