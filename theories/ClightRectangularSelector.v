From Stdlib Require Import List ZArith.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightSyntaxEquality ClightRegionRewrite ClightRegionRule
  ClightStraightLine ClightFrontendLoopProtocol ClightFrontendRegion
  ClightRectangularStore ClightRectangularLoops ClightRectangularGuard ClightRectangularRegion ClightSharedRegion.
Import ListNotations.
Set Implicit Arguments.

Record rectangle_description := RectangleDescription {
  described_shape : rectangle_shape;
  described_array : ident;
  rectangle_row : ident;
  rectangle_bound : ident;
  rectangle_column : ident;
  rectangle_inner_bound : ident;
  rectangle_inner_body : statement;
  rectangle_described_outer_body : statement
}.
Definition rectangle_described_source d := frontend_counted_loop (rectangle_row d) (rectangle_bound d) (rectangle_described_outer_body d).
Definition rectangle_described_target d :=
  rectangle_interchanged (rectangle_row d) (rectangle_bound d) (rectangle_column d) (rectangle_inner_bound d) (rect_store (described_shape d) (described_array d) (rectangle_row d) (rectangle_column d)).

Definition propose_rectangle_constant expression : option Z :=
  match expression with
  | Econst_int value _ => Some (Int.signed value)
  | Eunop Cop.Oneg (Econst_int value _) _ => Some (- Int.signed value)%Z
  | _ => None
  end.

(** A proposal is untrusted. Full AST equality and identifier/frame checks
    below bind every expression and every control component to the proof. *)
Definition propose_rectangle_description source : option rectangle_description :=
  match propose_frontend_shape source with
  | Some (row,bound,outer_body) => match flatten_region outer_body with
    | [Sset column _; inner_loop] => match propose_frontend_shape inner_loop with
      | Some (_,inner_bound,inner_body) => match flatten_region inner_body with
        | [Sassign (Ederef (Ebinop _ (Evar array (Ctypes.Tarray _ extent _))
            (Ebinop _ (Ebinop _ _ stride_expr _) _ _) _) _)
            (Ebinop _ (Ebinop _ (Ebinop _ _ coefficient_expr _) _ _) bias_expr _)] =>
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

Record rectangle_certificate source d := RectangleCertificate {
  rectangle_source_bound : source = rectangle_described_source d;
  rectangle_body_bound : flatten_region (rectangle_inner_body d) =
    [rect_store (described_shape d) (described_array d) (rectangle_row d) (rectangle_column d)];
  rectangle_outer_bound : flatten_region (rectangle_described_outer_body d) =
    [rectangle_reset (rectangle_column d);
      frontend_counted_loop (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d)];
  rectangle_distinct_row_bound : rectangle_row d <> rectangle_bound d;
  rectangle_distinct_row_column : rectangle_row d <> rectangle_column d;
  rectangle_distinct_bound_column : rectangle_bound d <> rectangle_column d;
  rectangle_distinct_row_inner_bound : rectangle_row d <> rectangle_inner_bound d;
  rectangle_distinct_column_inner_bound : rectangle_column d <> rectangle_inner_bound d;
  rectangle_layout_bound : rectangle_layout_valid (described_shape d)
}.

Definition check_rectangle_description source d : option (rectangle_certificate source d).
Proof.
  destruct (statement_eq source (rectangle_described_source d)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (rectangle_inner_body d))
    [rect_store (described_shape d) (described_array d) (rectangle_row d) (rectangle_column d)]) as [BODY|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (rectangle_described_outer_body d))
    [rectangle_reset (rectangle_column d);
      frontend_counted_loop (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d)]) as [OUTER|]; [|exact None].
  destruct (peq (rectangle_row d) (rectangle_bound d)) as [|RN]; [exact None|].
  destruct (peq (rectangle_row d) (rectangle_column d)) as [|RC]; [exact None|].
  destruct (peq (rectangle_bound d) (rectangle_column d)) as [|NC]; [exact None|].
  destruct (peq (rectangle_row d) (rectangle_inner_bound d)) as [|RM]; [exact None|].
  destruct (peq (rectangle_column d) (rectangle_inner_bound d)) as [|CM]; [exact None|].
  destruct (rectangle_layout_check (described_shape d)) eqn:LAYOUT; [|exact None].
  exact (Some (@RectangleCertificate source d SOURCE BODY OUTER RN RC NC RM CM (@rectangle_layout_check_sound (described_shape d) LAYOUT))).
Defined.

Definition checked_rectangle_rule {source d} (CERT : rectangle_certificate source d) :
  encoded_region_rule source (rectangle_described_target d).
Proof.
  rewrite (rectangle_source_bound CERT); unfold rectangle_described_source, rectangle_described_target.
  exact (@rectangle_region_rule (described_shape d) (rectangle_layout_bound CERT) (described_array d) (rectangle_row d) (rectangle_bound d) (rectangle_column d)
    (rectangle_inner_bound d) (rectangle_inner_body d) (rectangle_described_outer_body d)
    (rectangle_distinct_row_bound CERT) (rectangle_distinct_row_column CERT) (rectangle_distinct_bound_column CERT)
    (rectangle_distinct_row_inner_bound CERT) (rectangle_distinct_column_inner_bound CERT)
    (rectangle_body_bound CERT) (rectangle_outer_bound CERT)).
Defined.

Definition select_rectangle_interchange source : option statement :=
  match propose_rectangle_description source with
  | Some d => match check_rectangle_description source d with
    | Some CERT => Some (shared_generated_region (checked_rectangle_rule CERT))
    | None => None end
  | None => None end.

Theorem select_rectangle_interchange_sound source target :
  select_rectangle_interchange source = Some target -> region_contract source target.
Proof.
  unfold select_rectangle_interchange; destruct (propose_rectangle_description source) as [d|]; try discriminate.
  destruct (check_rectangle_description source d) as [CERT|]; try discriminate.
  intro SELECT; inversion SELECT; subst; apply shared_encoded_region_rule_sound.
Qed.


Definition example_rectangle_shape := RectangleShape 120 10 37 7.
Definition example_rectangle_body := rect_store example_rectangle_shape 5%positive 1%positive 3%positive.
Definition example_rectangle_outer := ClightRectangularLoops.rectangle_outer_body 3%positive 4%positive example_rectangle_body.
Definition example_rectangle_source := frontend_counted_loop 1%positive 2%positive example_rectangle_outer.
Example rectangle_shape_proposed :
  option_map described_shape (propose_rectangle_description example_rectangle_source) = Some example_rectangle_shape.
Proof. vm_compute; reflexivity. Qed.
Example rectangle_interchange_overlap_layout_refused :
  select_rectangle_interchange (frontend_counted_loop 1%positive 2%positive
    (ClightRectangularLoops.rectangle_outer_body 3%positive 4%positive (rect_store (RectangleShape 120 0 37 7) 5%positive 1%positive 3%positive))) = None.
Proof. vm_compute; reflexivity. Qed.
Example rectangle_interchange_memory_payload_refused :
  select_rectangle_interchange (frontend_counted_loop 1%positive 2%positive
    (ClightRectangularLoops.rectangle_outer_body 3%positive 4%positive (Sassign
      (rect_lvalue example_rectangle_shape 5%positive 1%positive 3%positive)
      (Etempvar 6%positive Ctypes.type_int32s)))) = None.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions select_rectangle_interchange_sound.
