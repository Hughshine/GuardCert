From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightNoWrap ClightRedundantSet
  ClightPositiveCheck ClightMatrixGuard ClightRectangularGuard ClightPureExpr ClightDecisionRule.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyTreeSynthesis ClightRuntimeStrideEntry.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition stride_wide_type := Tlong Signed noattr.
Definition signed_entry_word id entry := Int.signed (temp_word id (entry_temps entry)).
Definition stride_dimensions_property extent row bound inner_bound stride (_ : unit) entry :=
  register_equals row Int.zero tt entry /\
  0 < signed_entry_word bound entry /\ 0 < signed_entry_word inner_bound entry /\
  0 < signed_entry_word stride entry /\ signed_entry_word inner_bound entry <= signed_entry_word stride entry /\
  signed_entry_word bound entry * signed_entry_word stride entry <= extent.
Definition stride_columns_expr inner_bound stride :=
  Ebinop Ole (Etempvar inner_bound type_int32s) (Etempvar stride type_int32s) type_int32s.
Definition stride_extent_expr extent bound stride :=
  Ebinop Ole
    (Ebinop Omul (Ecast (Etempvar bound type_int32s) stride_wide_type)
      (Ecast (Etempvar stride type_int32s) stride_wide_type) stride_wide_type)
    (Econst_long (Int64.repr extent) stride_wide_type) type_int32s.
Definition stride_dimensions_guard extent row bound inner_bound stride :=
  Test (register_guard row Int.zero)
    (Test (register_positive_expr bound)
      (Test (register_positive_expr inner_bound)
        (Test (register_positive_expr stride)
          (Test (stride_columns_expr inner_bound stride)
            (Test (stride_extent_expr extent bound stride) (Decision true) (Decision false)) (Decision false))
          (Decision false)) (Decision false)) (Decision false)) (Decision false).
Definition stride_columns_flag inner_bound stride entry :=
  negb (Int.lt (temp_word stride (entry_temps entry)) (temp_word inner_bound (entry_temps entry))).
Definition stride_extent_flag extent bound stride entry :=
  (signed_entry_word bound entry * signed_entry_word stride entry <=? extent).
Definition stride_dimensions_accept extent row bound inner_bound stride (_ : unit) entry :=
  register_flag row Int.zero entry && register_positive bound entry && register_positive inner_bound entry &&
  register_positive stride entry && stride_columns_flag inner_bound stride entry && stride_extent_flag extent bound stride entry.

Lemma stride_columns_test inner_bound stride entry : register_domain inner_bound entry -> register_domain stride entry ->
  expression_test (stride_columns_expr inner_bound stride) entry (stride_columns_flag inner_bound stride entry).
Proof.
  intros [m M] [s S]; exists (Val.of_bool (negb (Int.lt s m))); split.
  - eapply eval_Ebinop with (v1 := Vint m) (v2 := Vint s); [constructor; exact M|constructor; exact S|reflexivity].
  - unfold stride_columns_flag, temp_word; rewrite M, S; apply bool_of_bool.
Qed.

Theorem stride_wide_product_exact n s :
  0 < Int.signed n -> 0 < Int.signed s ->
  Int64.signed (Int64.mul (Int64.repr (Int.signed n)) (Int64.repr (Int.signed s))) = Int.signed n * Int.signed s.
Proof.
  intros N S; pose proof (Int.signed_range n) as NR; pose proof (Int.signed_range s) as SR.
  change Int.max_signed with 2147483647 in *.
  change Int.min_signed with (-2147483648) in *.
  assert (NW : Int64.min_signed <= Int.signed n <= Int64.max_signed) by
    (change Int64.min_signed with (-9223372036854775808); change Int64.max_signed with 9223372036854775807; lia).
  assert (SW : Int64.min_signed <= Int.signed s <= Int64.max_signed) by
    (change Int64.min_signed with (-9223372036854775808); change Int64.max_signed with 9223372036854775807; lia).
  assert (PW : Int64.min_signed <= Int.signed n * Int.signed s <= Int64.max_signed) by
    (change Int64.min_signed with (-9223372036854775808); change Int64.max_signed with 9223372036854775807; nia).
  rewrite Int64.mul_signed.
  rewrite (Int64.signed_repr (Int.signed n) NW), (Int64.signed_repr (Int.signed s) SW).
  rewrite Int64.signed_repr by exact PW; reflexivity.
Qed.

Lemma stride_extent_test extent bound stride entry : 0 < extent <= Int.max_signed ->
  register_domain bound entry -> register_domain stride entry ->
  register_positive bound entry = true -> register_positive stride entry = true ->
  expression_test (stride_extent_expr extent bound stride) entry (stride_extent_flag extent bound stride entry).
Proof.
  intros EXTENT [n N] [s S] NP SP.
  assert (NZ : 0 < Int.signed n) by (pose proof (@register_positive_sound bound entry NP) as H; unfold temp_word in H; rewrite N in H; exact H).
  assert (SZ : 0 < Int.signed s) by (pose proof (@register_positive_sound stride entry SP) as H; unfold temp_word in H; rewrite S in H; exact H).
  exists (Val.of_bool (negb (Int64.lt (Int64.repr extent)
    (Int64.mul (Int64.repr (Int.signed n)) (Int64.repr (Int.signed s)))))); split.
  - eapply eval_Ebinop.
    + eapply eval_Ebinop.
      * eapply eval_Ecast; [constructor; exact N|reflexivity].
      * eapply eval_Ecast; [constructor; exact S|reflexivity].
      * reflexivity.
    + constructor.
    + reflexivity.
  - rewrite bool_of_bool; unfold stride_extent_flag, signed_entry_word, temp_word; rewrite N, S.
    unfold Int64.lt; rewrite stride_wide_product_exact by assumption.
    rewrite Int64.signed_repr by
      (change Int64.min_signed with (-9223372036854775808); change Int64.max_signed with 9223372036854775807;
        change Int.max_signed with 2147483647 in EXTENT; lia).
    destruct (zlt extent (Int.signed n * Int.signed s)); cbn;
      f_equal; symmetry; [apply Z.leb_gt|apply Z.leb_le]; lia.
Qed.
Print Assumptions stride_wide_product_exact.

Lemma stride_dimensions_run extent row bound inner_bound stride entry : 0 < extent <= Int.max_signed ->
  runtime_stride_domain row bound inner_bound stride entry ->
  decision_run entry (stride_dimensions_guard extent row bound inner_bound stride)
    (stride_dimensions_accept extent row bound inner_bound stride tt entry).
Proof.
  intros EXTENT [[I [N MD]] SD]; unfold stride_dimensions_guard, stride_dimensions_accept.
  eapply run_test; [apply register_expression_test; exact I|].
  destruct (register_flag row Int.zero entry) eqn:ZERO; cbn; [|constructor].
  pose proof (register_flag_evidence Int.zero I ZERO) as ITER.
  eapply run_test; [apply register_positive_test; exact N|].
  destruct (register_positive bound entry) eqn:NP; cbn; [|constructor].
  assert (M : register_domain inner_bound entry) by (apply MD; [exact ITER|apply register_positive_sound; exact NP]).
  eapply run_test; [apply register_positive_test; exact M|].
  destruct (register_positive inner_bound entry) eqn:MP; cbn; [|constructor].
  assert (S : register_domain stride entry) by
    (apply SD; [exact ITER|apply register_positive_sound; exact NP|apply register_positive_sound; exact MP]).
  eapply run_test; [apply register_positive_test; exact S|].
  destruct (register_positive stride entry) eqn:SP; cbn; [|constructor].
  eapply run_test; [apply stride_columns_test; assumption|].
  destruct (stride_columns_flag inner_bound stride entry) eqn:COL; cbn; [|constructor].
  eapply run_test; [apply stride_extent_test; assumption|].
  destruct (stride_extent_flag extent bound stride entry); constructor.
Qed.

Lemma stride_dimensions_sound extent row bound inner_bound stride : forall a entry,
  runtime_stride_domain row bound inner_bound stride entry ->
  stride_dimensions_accept extent row bound inner_bound stride a entry = true ->
  stride_dimensions_property extent row bound inner_bound stride a entry.
Proof.
  intros [] entry [[I [N MD]] SD] ACCEPT; unfold stride_dimensions_accept in ACCEPT.
  repeat rewrite andb_true_iff in ACCEPT.
  destruct ACCEPT as [[[[[ZERO NP] MP] SP] COL] EXTENT].
  unfold stride_dimensions_property, signed_entry_word; split; [apply register_flag_evidence; assumption|].
  split; [apply register_positive_sound; exact NP|split; [apply register_positive_sound; exact MP|]].
  split; [apply register_positive_sound; exact SP|split].
  - unfold stride_columns_flag, Int.lt in COL.
    destruct (zlt (Int.signed (temp_word stride (entry_temps entry)))
      (Int.signed (temp_word inner_bound (entry_temps entry)))); cbn in COL; [discriminate|lia].
  - unfold stride_extent_flag, signed_entry_word in EXTENT; apply Z.leb_le in EXTENT; exact EXTENT.
Qed.
Definition stride_dimensions_primitives extent row bound inner_bound stride (EXTENT : 0 < extent <= Int.max_signed) :=
  @positive_tree_primitives unit (runtime_stride_domain row bound inner_bound stride)
    (stride_dimensions_property extent row bound inner_bound stride)
    (stride_dimensions_accept extent row bound inner_bound stride)
    (@stride_dimensions_sound extent row bound inner_bound stride)
    (fun _ => stride_dimensions_guard extent row bound inner_bound stride)
    (fun _ => ltac:(repeat constructor))
    (fun a entry DOMAIN => match a with tt => stride_dimensions_run EXTENT DOMAIN end).
Definition stride_dimensions_condition fe O (observe : fragment_observation -> O -> Prop)
  extent row bound inner_bound stride (EXTENT : 0 < extent <= Int.max_signed) :
  readonly_condition (readonly_clight_host fe observe) (runtime_stride_domain row bound inner_bound stride)
    (stride_dimensions_property extent row bound inner_bound stride tt)
    (synthesize_decision_tree (stride_dimensions_primitives row bound inner_bound stride EXTENT) (Fact tt)).
Proof.
  apply synthesized_scalar_tree_condition with
    (D := @positive_dimension clight_entry unit (runtime_stride_domain row bound inner_bound stride)
      (stride_dimensions_property extent row bound inner_bound stride) (stride_dimensions_accept extent row bound inner_bound stride)
      (@stride_dimensions_sound extent row bound inner_bound stride)) (premise := Fact tt).
  - intros []; repeat constructor.
  - intros []; constructor.
Defined.
Print Assumptions stride_dimensions_condition.
Print Assumptions stride_dimensions_sound.
