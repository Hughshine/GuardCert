From Stdlib Require Import ZArith.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightNoWrap ClightExprRewrite CommonRewrites.
Open Scope Z_scope.

Example division_selected : select_common (divisor_source false 1%positive 2%positive) =
  Some (divisor_guard 2%positive, divisor_candidate false 1%positive).
Proof. reflexivity. Qed.
Example modulus_selected : select_common (divisor_source true 1%positive 2%positive) =
  Some (divisor_guard 2%positive, divisor_candidate true 1%positive).
Proof. reflexivity. Qed.
Example cancellation_selected : select_common (cancel_source 1%positive) =
  Some (cancel_guard 1%positive, uint_temp 1%positive).
Proof. reflexivity. Qed.
Example identity_selected : select_common (self_sub_source 1%positive) =
  Some (Econst_int Int.one type_int32s, uint_const 0).
Proof. reflexivity. Qed.
Example nested_division_selected :
  select_common (Ecast
    (Ebinop Oadd (uint_const 3) (divisor_source false 1%positive 2%positive) type_int32u)
    type_int32s) = Some (divisor_guard 2%positive,
      Ecast (Ebinop Oadd (uint_const 3) (divisor_candidate false 1%positive) type_int32u)
        type_int32s).
Proof. reflexivity. Qed.
Example return_versioned :
  ClightExprRewrite.transform_statement select_common
    (Sreturn (Some (cancel_source 1%positive))) =
  Sifthenelse (cancel_guard 1%positive) (Sreturn (Some (uint_temp 1%positive)))
    (Sreturn (Some (cancel_source 1%positive))).
Proof. reflexivity. Qed.
Example store_versioned :
  ClightExprRewrite.transform_statement select_common
    (Sassign (Evar 3%positive type_int32u) (cancel_source 1%positive)) =
  Sifthenelse (cancel_guard 1%positive)
    (Sassign (Evar 3%positive type_int32u) (uint_temp 1%positive))
    (Sassign (Evar 3%positive type_int32u) (cancel_source 1%positive)).
Proof. reflexivity. Qed.
Example label_body_versioned :
  ClightExprRewrite.transform_statement select_common
    (Slabel 9%positive (Sreturn (Some (cancel_source 1%positive)))) =
  Slabel 9%positive (Sifthenelse (cancel_guard 1%positive)
    (Sreturn (Some (uint_temp 1%positive))) (Sreturn (Some (cancel_source 1%positive)))).
Proof. reflexivity. Qed.

(** These reject the unsound unconditional rewrite at its first wrapping input. *)
Example cancellation_accepts_boundary : cancel_flag (Int.repr 2147483647) = true.
Proof. reflexivity. Qed.
Example cancellation_rejects_wrap : cancel_flag (Int.repr 2147483648) = false.
Proof. reflexivity. Qed.
Example unconditional_cancellation_is_wrong :
  Int.divu (Int.add (Int.repr 2147483648) (Int.repr 2147483648)) (Int.repr 2) = Int.zero /\
  Int.zero <> Int.repr 2147483648.
Proof. split; [reflexivity|intro H; discriminate H]. Qed.
Example divisor_rejects_fallback : Int.eq (Int.repr 3) (Int.repr 2) = false.
Proof. reflexivity. Qed.
Example signed_division_not_selected : select_common
  (Ebinop Odiv (Etempvar 1%positive type_int32s) (Etempvar 2%positive type_int32s) type_int32s) = None.
Proof. reflexivity. Qed.
Example volatile_temp_not_selected : select_common
  (Ebinop Odiv (Etempvar 1%positive (Tint I32 Unsigned {| attr_volatile := true; attr_alignas := None |}))
    (uint_temp 2%positive) type_int32u) = None.
Proof. reflexivity. Qed.
