From Stdlib Require Import List ZArith.
From compcert.lib Require Import Coqlib Integers Floats.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Ctypes Cop Clight.

(** Syntax binding for manually supplied or generated local certificates.
    This equality includes types, attributes, and external-call descriptors. *)
Definition expression_eq : forall first second : expr, {first = second} + {first <> second}.
Proof.
  decide equality; try apply type_eq; try apply Int.eq_dec; try apply Int64.eq_dec;
    try apply Float.eq_dec; try apply Float32.eq_dec; try apply peq; decide equality.
Defined.

Fixpoint statement_eq (first second : statement) : {first = second} + {first <> second}
with cases_eq (first second : labeled_statements) : {first = second} + {first <> second}.
Proof.
  - decide equality; try apply expression_eq; try apply external_function_eq;
      try apply cases_eq; try apply peq; try (apply list_eq_dec; apply expression_eq);
      try (apply list_eq_dec; apply type_eq); decide equality; try apply peq; apply expression_eq.
  - decide equality; try apply statement_eq; decide equality; apply zeq.
Defined.

Print Assumptions statement_eq.
