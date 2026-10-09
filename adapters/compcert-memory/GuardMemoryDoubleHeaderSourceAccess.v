From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Globalenvs.
From compcert.cfrontend Require Import Ctypes Clight.
From polcert.src Require Import PolyBase.
From polcert.lib Require Import Linalg.
From Guard Require Import CompCertMemoryActions ClightGlobalScope ClightRegionProgress.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleLocations GuardMemoryDoubleAssignment
  GuardMemoryDoubleTensorBackend GuardMemoryDynamicTensorLayout GuardMemoryDoubleSourceAccess
  GuardMemoryLongHeaderAffine GuardMemoryDoubleAffineSourceAccess.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition decode_double_header_affine_source_access header controls source : option double_affine_source_access :=
  match describe_double_source_access source with
  | Some access => match decode_long_header_indices header controls (double_source_coordinates access) with
    | Some rows => Some (DoubleAffineSourceAccess (double_source_array access,rows) (double_source_dimensions access))
    | None => None end
  | None => None end.
Definition checked_double_header_affine_source_access p header controls source :=
  match decode_double_header_affine_source_access header controls source with
  | Some access => if double_source_access_static_check p (double_affine_source_metadata access)
      then Some access else None
  | None => None end.
Lemma checked_double_header_affine_source_access_sound p header controls source access :
  checked_double_header_affine_source_access p header controls source=Some access ->
  decode_double_header_affine_source_access header controls source=Some access /\
  double_source_access_static_check p (double_affine_source_metadata access)=true.
Proof.
  unfold checked_double_header_affine_source_access; destruct (decode_double_header_affine_source_access header controls source)
    as [decoded|] eqn:DECODE; try discriminate.
  destruct (double_source_access_static_check p (double_affine_source_metadata decoded)) eqn:STATIC;
    try discriminate; intro RESULT; inversion RESULT; subst; auto.
Qed.

(** Actual declaration/scope facts, an observed global header, I64 temporary
    coordinates and a resolved
    bounded mathematical cell produce the address receipt. Neither metadata
    nor bounds infer a memory load or a successful store. *)
Theorem checked_double_header_affine_source_access_receipt p header controls source access valuation ge locals temps memory layouts location :
  checked_double_header_affine_source_access p header controls source=Some access ->
  preserving_globals (globalenv p) ge ->
  locals_avoid [fst (double_affine_source_function access)] locals ->
  eval_expr ge locals temps memory (Evar header memory_long_type)
    (Vlong (Int64.repr (valuation header))) ->
  (forall identifier, In identifier controls -> identifier<>header -> temps ! identifier=Some (Vlong (Int64.repr (valuation identifier)))) ->
  layouts ! (fst (double_affine_source_function access))=Some (double_affine_source_dimensions access) ->
  global_double_locations ge layouts (exact_cell (double_affine_source_function access) (map valuation controls))=Some location ->
  double_memory_location_receipt ge locals temps memory source location.
Proof.
  intro CHECK; destruct (@checked_double_header_affine_source_access_sound p header controls source access CHECK) as [DECODE STATIC].
  unfold decode_double_header_affine_source_access in DECODE.
  destruct (describe_double_source_access source) as [raw|] eqn:RAW; try discriminate.
  destruct (decode_long_header_indices header controls (double_source_coordinates raw)) as [rows|] eqn:ROWS; try discriminate.
  inversion DECODE; subst access; cbn [double_affine_source_function double_affine_source_dimensions fst] in *.
  intros GLOBAL LOCAL HEADER WORDS LAYOUT RESOLVE.
  change (double_source_access_static_check p raw=true) in STATIC.
  destruct (@double_source_access_static_sound p raw ge locals STATIC GLOBAL LOCAL)
    as [block [[ABSENT SYMBOL] [POSITIVE SPAN]]].
  unfold global_double_locations in RESOLVE; cbn [exact_cell arr_id arr_index fst snd] in RESOLVE.
  rewrite SYMBOL,LAYOUT in RESOLVE.
  destruct (tensor_index (double_source_dimensions raw) (affine_product rows (map valuation controls)))
    as [index|] eqn:INDEX; try discriminate.
  inversion RESOLVE; subst location.
  eapply double_source_access_receipt; [exact RAW|split; eassumption|exact SPAN| |exact INDEX].
  eapply decoded_long_header_indices_execution; eassumption.
Qed.

Fixpoint checked_double_header_affine_source_reads p header controls sources := match sources with
| [] => Some []
| source::rest => match checked_double_header_affine_source_access p header controls source,checked_double_header_affine_source_reads p header controls rest with
    | Some access,Some accesses => Some (access::accesses) | _,_ => None end end.
Theorem checked_double_header_affine_source_reads_receipts p header controls sources accesses valuation ge locals temps memory layouts locations :
  checked_double_header_affine_source_reads p header controls sources=Some accesses ->
  preserving_globals (globalenv p) ge ->
  (forall access, In access accesses -> locals_avoid [fst (double_affine_source_function access)] locals /\
    layouts ! (fst (double_affine_source_function access))=Some (double_affine_source_dimensions access)) ->
  eval_expr ge locals temps memory (Evar header memory_long_type)
    (Vlong (Int64.repr (valuation header))) ->
  (forall identifier, In identifier controls -> identifier<>header -> temps ! identifier=Some (Vlong (Int64.repr (valuation identifier)))) ->
  resolve_cells (map (fun access => exact_cell (double_affine_source_function access) (map valuation controls)) accesses)
    (global_double_locations ge layouts)=Some locations ->
  Forall2 (double_memory_location_receipt ge locals temps memory) sources locations.
Proof.
  intro COMPILE; revert accesses locations COMPILE; induction sources as [|source rest IH];
    intros accesses locations COMPILE GLOBAL STATIC HEADER WORDS RESOLVE; cbn [checked_double_header_affine_source_reads] in COMPILE.
  - inversion COMPILE; subst accesses; cbn in RESOLVE; inversion RESOLVE; constructor.
  - destruct (checked_double_header_affine_source_access p header controls source) as [access|] eqn:ACCESS; try discriminate.
    destruct (checked_double_header_affine_source_reads p header controls rest) as [tail|] eqn:TAIL; try discriminate.
    inversion COMPILE; subst accesses; cbn [map resolve_cells] in RESOLVE.
    destruct (global_double_locations ge layouts (exact_cell (double_affine_source_function access) (map valuation controls)))
      as [location|] eqn:LOCATION; try discriminate.
    destruct (resolve_cells (map (fun access => exact_cell (double_affine_source_function access) (map valuation controls)) tail)
      (global_double_locations ge layouts)) as [remaining|] eqn:REMAINING; try discriminate.
    inversion RESOLVE; subst locations; constructor.
    + destruct (STATIC access ltac:(cbn; auto)) as [LOCAL LAYOUT].
      eapply checked_double_header_affine_source_access_receipt; eassumption.
    + eapply IH; [reflexivity|exact GLOBAL| |exact HEADER|exact WORDS|exact REMAINING].
      intros item MEMBER; apply STATIC; cbn; auto.
Qed.

Print Assumptions checked_double_header_affine_source_access_sound.
Print Assumptions checked_double_header_affine_source_access_receipt.
Print Assumptions checked_double_header_affine_source_reads_receipts.
