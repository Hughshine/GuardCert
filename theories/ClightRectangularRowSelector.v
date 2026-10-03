From Stdlib Require Import List ZArith.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightSyntaxEquality ClightRegionRewrite ClightRegionRule
  ClightStraightLine ClightFrontendLoopProtocol ClightFrontendRegion
  ClightRectangularStore ClightRectangularLoops ClightRectangularGuard ClightRectangularRegion ClightSharedRegion.
Import ListNotations.
Set Implicit Arguments.

From Guard Require Import ClightRectangularSelector ClightRectangularRowUpdate ClightRectangularRowRegion.

Definition rectangle_row_update_described_target d :=
  rectangle_interchanged (rectangle_row d) (rectangle_bound d) (rectangle_column d) (rectangle_inner_bound d)
    (rect_row_update (described_shape d) (described_array d) (rectangle_row d) (rectangle_column d)).

(** Extract only a proposal. The checker below binds the read address, arithmetic,
    write address, types, and loop protocol by complete AST equality. *)
Definition propose_rectangle_row_update_description source : option rectangle_description :=
  match propose_frontend_shape source with
  | Some (row,bound,outer_body) => match flatten_region outer_body with
    | [Sset column _; inner_loop] => match propose_frontend_shape inner_loop with
      | Some (_,inner_bound,inner_body) => match flatten_region inner_body with
        | [Sassign (Ederef (Ebinop _ (Evar array (Ctypes.Tarray _ extent _))
            (Ebinop _ (Ebinop _ _ stride_expr _) _ _) _) _)
            (Ebinop _ _ (Ebinop _ (Ebinop _ (Ebinop _ _ coefficient_expr _) _ _) bias_expr _) _)] =>
            match propose_rectangle_constant stride_expr, propose_rectangle_constant coefficient_expr,
              propose_rectangle_constant bias_expr with
            | Some stride, Some coefficient, Some bias =>
              Some (RectangleDescription (RectangleShape extent stride coefficient bias)
                array row bound column inner_bound inner_body outer_body)
            | _, _, _ => None end
        | _ => None end
      | None => None end
    | _ => None end
  | None => None end.

Record rectangle_row_update_certificate source d := RectangleRowUpdateCertificate {
  rectangle_row_update_source_bound : source = rectangle_described_source d;
  rectangle_row_update_body_bound : flatten_region (rectangle_inner_body d) =
    [rect_row_update (described_shape d) (described_array d) (rectangle_row d) (rectangle_column d)];
  rectangle_row_update_outer_bound : flatten_region (rectangle_described_outer_body d) =
    [rectangle_reset (rectangle_column d);
      frontend_counted_loop (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d)];
  rectangle_row_update_distinct_row_bound : rectangle_row d <> rectangle_bound d;
  rectangle_row_update_distinct_row_column : rectangle_row d <> rectangle_column d;
  rectangle_row_update_distinct_bound_column : rectangle_bound d <> rectangle_column d;
  rectangle_row_update_distinct_row_inner_bound : rectangle_row d <> rectangle_inner_bound d;
  rectangle_row_update_distinct_column_inner_bound : rectangle_column d <> rectangle_inner_bound d;
  rectangle_row_update_layout_bound : rectangle_layout_valid (described_shape d)
}.

Definition check_rectangle_row_update_description source d : option (rectangle_row_update_certificate source d).
Proof.
  destruct (statement_eq source (rectangle_described_source d)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (rectangle_inner_body d))
    [rect_row_update (described_shape d) (described_array d) (rectangle_row d) (rectangle_column d)]) as [BODY|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (rectangle_described_outer_body d))
    [rectangle_reset (rectangle_column d);
      frontend_counted_loop (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d)]) as [OUTER|]; [|exact None].
  destruct (peq (rectangle_row d) (rectangle_bound d)) as [|RN]; [exact None|].
  destruct (peq (rectangle_row d) (rectangle_column d)) as [|RC]; [exact None|].
  destruct (peq (rectangle_bound d) (rectangle_column d)) as [|NC]; [exact None|].
  destruct (peq (rectangle_row d) (rectangle_inner_bound d)) as [|RM]; [exact None|].
  destruct (peq (rectangle_column d) (rectangle_inner_bound d)) as [|CM]; [exact None|].
  destruct (rectangle_layout_check (described_shape d)) eqn:LAYOUT; [|exact None].
  exact (Some (@RectangleRowUpdateCertificate source d SOURCE BODY OUTER RN RC NC RM CM (@rectangle_layout_check_sound (described_shape d) LAYOUT))).
Defined.

Definition checked_rectangle_row_update_rule {source d} (CERT : rectangle_row_update_certificate source d) :
  encoded_region_rule source (rectangle_row_update_described_target d).
Proof.
  rewrite (rectangle_row_update_source_bound CERT); unfold rectangle_described_source, rectangle_row_update_described_target.
  exact (@rectangle_row_update_region_rule (described_shape d) (rectangle_row_update_layout_bound CERT) (described_array d) (rectangle_row d) (rectangle_bound d) (rectangle_column d)
    (rectangle_inner_bound d) (rectangle_inner_body d) (rectangle_described_outer_body d)
    (rectangle_row_update_distinct_row_bound CERT) (rectangle_row_update_distinct_row_column CERT) (rectangle_row_update_distinct_bound_column CERT)
    (rectangle_row_update_distinct_row_inner_bound CERT) (rectangle_row_update_distinct_column_inner_bound CERT)
    (rectangle_row_update_body_bound CERT) (rectangle_row_update_outer_bound CERT)).
Defined.

Definition select_rectangle_row_update_interchange source : option statement :=
  match propose_rectangle_row_update_description source with
  | Some d => match check_rectangle_row_update_description source d with
    | Some CERT => Some (shared_generated_region (checked_rectangle_row_update_rule CERT))
    | None => None end
  | None => None end.

Theorem select_rectangle_row_update_interchange_sound source target :
  select_rectangle_row_update_interchange source = Some target -> region_contract source target.
Proof.
  unfold select_rectangle_row_update_interchange; destruct (propose_rectangle_row_update_description source) as [d|]; try discriminate.
  destruct (check_rectangle_row_update_description source d) as [CERT|]; try discriminate.
  intro SELECT; inversion SELECT; subst; apply shared_encoded_region_rule_sound.
Qed.

Definition example_rectangle_row_body := rect_row_update example_rectangle_shape 5%positive 1%positive 3%positive.
Definition example_rectangle_row_source := frontend_counted_loop 1%positive 2%positive
  (ClightRectangularLoops.rectangle_outer_body 3%positive 4%positive example_rectangle_row_body).
Example rectangle_row_update_proposed :
  option_map described_shape (propose_rectangle_row_update_description example_rectangle_row_source) = Some example_rectangle_shape.
Proof. vm_compute; reflexivity. Qed.
Example rectangle_row_update_neighbor_read_refused :
  select_rectangle_row_update_interchange (frontend_counted_loop 1%positive 2%positive
    (ClightRectangularLoops.rectangle_outer_body 3%positive 4%positive (Sassign
      (rect_lvalue example_rectangle_shape 5%positive 1%positive 3%positive)
      (Clight.Ebinop Cop.Oadd
        (Clight.Ederef (Clight.Ebinop Cop.Oadd (Clight.Evar 5%positive (rect_array_type example_rectangle_shape))
          (rect_constant 0) (Ctypes.Tpointer Ctypes.type_int32s Ctypes.noattr)) Ctypes.type_int32s)
        (rect_value example_rectangle_shape 1%positive 3%positive) Ctypes.type_int32s)))) = None.
Proof. vm_compute; reflexivity. Qed.
Print Assumptions select_rectangle_row_update_interchange_sound.
