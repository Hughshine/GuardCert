From Stdlib Require Import List Bool Arith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Ctypes Clight.
From Guard Require Import ClightTempFootprint.
From GuardInterface Require Import ClightTensorRegionPackage.
Import ListNotations.
Set Implicit Arguments.

Definition multi_tensor_integer_names (pool : list (ident*type)) :=
  map fst (filter (fun declaration => if type_eq (snd declaration) type_int32s then true else false) pool).
Definition multi_tensor_fresh_integer_names source live pool :=
  filter (fun identifier => negb (tensor_member identifier (statement_temps source++live)))
    (multi_tensor_integer_names pool).

Record multi_tensor_scan_allocation source live pool rank := MultiTensorScanAllocation {
  mtas_left : list ident;
  mtas_right : list ident;
  mtas_flag : ident;
  mtas_left_length : length mtas_left = rank;
  mtas_right_length : length mtas_right = rank;
  mtas_unique : NoDup (mtas_left++mtas_right++[mtas_flag]);
  mtas_fresh : tensor_disjoint (statement_temps source++live) (mtas_left++mtas_right++[mtas_flag]) = true;
  mtas_typed : tensor_subset (mtas_left++mtas_right++[mtas_flag]) (multi_tensor_integer_names pool) = true
}.
Definition multi_tensor_scan_private source live pool rank
    (allocation : multi_tensor_scan_allocation source live pool rank) :=
  mtas_left allocation++mtas_right allocation++[mtas_flag allocation].

Definition allocate_multi_tensor_scan source live pool rank : option (multi_tensor_scan_allocation source live pool rank).
Proof.
  destruct rank as [|rank]; [exact None|].
  pose (names := multi_tensor_fresh_integer_names source live pool).
  pose (left := firstn (S rank) names).
  pose (right := firstn (S rank) (skipn (S rank) names)).
  destruct (nth_error names (2*S rank)) as [flag|] eqn:FLAG; [|exact None].
  destruct (Nat.eqb (length left) (S rank)) eqn:LEFT; [|exact None].
  destruct (Nat.eqb (length right) (S rank)) eqn:RIGHT; [|exact None].
  destruct (tensor_unique (left++right++[flag])) eqn:UNIQUE; [|exact None].
  destruct (tensor_disjoint (statement_temps source++live) (left++right++[flag])) eqn:FRESH; [|exact None].
  destruct (tensor_subset (left++right++[flag]) (multi_tensor_integer_names pool)) eqn:TYPED; [|exact None].
  refine (Some {|mtas_left:=left; mtas_right:=right; mtas_flag:=flag;
    mtas_fresh:=FRESH; mtas_typed:=TYPED|}).
  - apply Nat.eqb_eq; exact LEFT.
  - apply Nat.eqb_eq; exact RIGHT.
  - apply tensor_unique_sound; exact UNIQUE.
Defined.

Lemma multi_tensor_integer_names_member identifier pool :
  In identifier (multi_tensor_integer_names pool) -> In (identifier,type_int32s) pool.
Proof.
  unfold multi_tensor_integer_names; intros MEMBER; apply in_map_iff in MEMBER.
  destruct MEMBER as [[actual ty] [SAME MEMBER]]; cbn in SAME; subst actual.
  apply filter_In in MEMBER as [MEMBER CHECK]; cbn in CHECK.
  destruct (type_eq ty type_int32s) as [SAME|]; [subst ty; exact MEMBER|discriminate].
Qed.

Theorem multi_tensor_scan_allocated_int32 source live pool rank
    (allocation : multi_tensor_scan_allocation source live pool rank) identifier :
  In identifier (multi_tensor_scan_private allocation) -> In (identifier,type_int32s) pool.
Proof.
  intros MEMBER; apply multi_tensor_integer_names_member.
  eapply tensor_subset_sound; [exact (mtas_typed allocation)|exact MEMBER].
Qed.
Theorem multi_tensor_scan_allocation_fresh source live pool rank
    (allocation : multi_tensor_scan_allocation source live pool rank) identifier :
  In identifier (statement_temps source++live) -> ~ In identifier (multi_tensor_scan_private allocation).
Proof. apply tensor_disjoint_sound; exact (mtas_fresh allocation). Qed.

Definition multi_tensor_scan_candidate_pool source live pool rank
    (allocation : multi_tensor_scan_allocation source live pool rank) :=
  filter (fun declaration => negb (tensor_member (fst declaration) (multi_tensor_scan_private allocation))) pool.

Theorem multi_tensor_scan_candidate_pool_private source live pool rank
    (allocation : multi_tensor_scan_allocation source live pool rank) identifier ty :
  In (identifier,ty) (multi_tensor_scan_candidate_pool allocation) ->
  ~ In identifier (multi_tensor_scan_private allocation).
Proof.
  unfold multi_tensor_scan_candidate_pool; intros MEMBER; apply filter_In in MEMBER as [_ CHECK].
  intros BAD; apply tensor_member_true in BAD; cbn in CHECK; rewrite BAD in CHECK; discriminate.
Qed.

Print Assumptions multi_tensor_integer_names_member.
Print Assumptions allocate_multi_tensor_scan.
Print Assumptions multi_tensor_scan_allocated_int32.
Print Assumptions multi_tensor_scan_allocation_fresh.
Print Assumptions multi_tensor_scan_candidate_pool_private.
