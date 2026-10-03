From Stdlib Require Import List ZArith.
From GuardMemory Require Import GuardMemoryLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Clearing positive integer division in comparisons avoids asking the affine
    extractor or the signed backend to execute a possibly negative quotient.
    Any changed domain still has to pass the independent integer-domain check. *)
Definition memory_generated_le first second :=
  match first,second with
  | L.Div value divisor,_ =>
    if 0 <? divisor then
      L.LE value (L.Sum (L.Mult divisor second) (L.Constant (divisor-1)))
    else L.LE first second
  | _,L.Div value divisor =>
    if 0 <? divisor then L.LE (L.Mult divisor first) value else L.LE first second
  | _,_ => L.LE first second end.
Fixpoint memory_generated_affine_test test :=
  match test with
  | L.LE first second => memory_generated_le first second
  | L.And first second => L.And (memory_generated_affine_test first) (memory_generated_affine_test second)
  | L.Or first second => L.Or (memory_generated_affine_test first) (memory_generated_affine_test second)
  | L.Not value => L.Not (memory_generated_affine_test value)
  | _ => test end.

(** This is a proposal normalizer. Its result is re-extracted and validated
    against the actual source; no code-generation or normalization assumption
    is used by the guarded fragment contract. *)
Fixpoint memory_generated_lift expression :=
  match expression with
  | L.Constant value => L.Constant value
  | L.Var index => L.Var (S index)
  | L.Sum first second => L.Sum (memory_generated_lift first) (memory_generated_lift second)
  | L.Mult factor value => L.Mult factor (memory_generated_lift value)
  | L.Div value divisor => L.Div (memory_generated_lift value) divisor
  | L.Mod value divisor => L.Mod (memory_generated_lift value) divisor
  | L.Min first second => L.Min (memory_generated_lift first) (memory_generated_lift second)
  | L.Max first second => L.Max (memory_generated_lift first) (memory_generated_lift second) end.
Fixpoint memory_generated_lower expression : L.expr * list L.expr :=
  match expression with
  | L.Max first second =>
    let '(bound,checks) := memory_generated_lower first in
    let '(other,remaining) := memory_generated_lower second in
    (bound,checks++other::remaining)
  | _ => (expression,[]) end.
Fixpoint memory_generated_upper expression : L.expr * list L.expr :=
  match expression with
  | L.Min first second =>
    let '(bound,checks) := memory_generated_upper first in
    let '(other,remaining) := memory_generated_upper second in
    (bound,checks++other::remaining)
  | _ => (expression,[]) end.
Fixpoint memory_generated_lower_guards bounds body :=
  match bounds with
  | [] => body
  | bound::rest => L.Guard (memory_generated_le (memory_generated_lift bound) (L.Var 0))
    (memory_generated_lower_guards rest body) end.
Fixpoint memory_generated_upper_guards bounds body :=
  match bounds with
  | [] => body
  | bound::rest => L.Guard (memory_generated_le (L.Var 0) (L.Sum (memory_generated_lift bound) (L.Constant (-1))))
    (memory_generated_upper_guards rest body) end.
Definition memory_generated_expr_eq : forall first second : L.expr, {first = second}+{first <> second}.
Proof. decide equality; try apply Nat.eq_dec; apply Z.eq_dec. Defined.
Definition memory_generated_test_eq : forall first second : L.test, {first = second}+{first <> second}.
Proof. decide equality; try apply Bool.bool_dec; apply memory_generated_expr_eq. Defined.
Fixpoint memory_generated_substitute_expr position replacement expression :=
  match expression with
  | L.Constant value => L.Constant value
  | L.Var index => match Nat.compare index position with
    | Eq => replacement | Lt => L.Var index | Gt => L.Var (Nat.pred index) end
  | L.Sum first second => L.Sum (memory_generated_substitute_expr position replacement first)
      (memory_generated_substitute_expr position replacement second)
  | L.Mult factor value => L.Mult factor (memory_generated_substitute_expr position replacement value)
  | L.Div value divisor => L.Div (memory_generated_substitute_expr position replacement value) divisor
  | L.Mod value divisor => L.Mod (memory_generated_substitute_expr position replacement value) divisor
  | L.Min first second => L.Min (memory_generated_substitute_expr position replacement first)
      (memory_generated_substitute_expr position replacement second)
  | L.Max first second => L.Max (memory_generated_substitute_expr position replacement first)
      (memory_generated_substitute_expr position replacement second) end.
Fixpoint memory_generated_substitute_test position replacement test :=
  match test with
  | L.TConstantTest value => L.TConstantTest value
  | L.LE first second => L.LE (memory_generated_substitute_expr position replacement first)
      (memory_generated_substitute_expr position replacement second)
  | L.EQ first second => L.EQ (memory_generated_substitute_expr position replacement first)
      (memory_generated_substitute_expr position replacement second)
  | L.And first second => L.And (memory_generated_substitute_test position replacement first)
      (memory_generated_substitute_test position replacement second)
  | L.Or first second => L.Or (memory_generated_substitute_test position replacement first)
      (memory_generated_substitute_test position replacement second)
  | L.Not value => L.Not (memory_generated_substitute_test position replacement value) end.
Fixpoint memory_generated_substitute_stmt position replacement statement :=
  match statement with
  | L.Instr instruction arguments => L.Instr instruction (map (memory_generated_substitute_expr position replacement) arguments)
  | L.Guard test body => L.Guard (memory_generated_substitute_test position replacement test)
      (memory_generated_substitute_stmt position replacement body)
  | L.Loop lower upper body => L.Loop (memory_generated_substitute_expr position replacement lower)
      (memory_generated_substitute_expr position replacement upper)
      (memory_generated_substitute_stmt (S position) (memory_generated_lift replacement) body)
  | L.Seq statements => L.Seq (memory_generated_substitute_list position replacement statements) end
with memory_generated_substitute_list position replacement statements :=
  match statements with
  | L.SNil => L.SNil
  | L.SCons statement rest => L.SCons (memory_generated_substitute_stmt position replacement statement)
      (memory_generated_substitute_list position replacement rest) end.
Definition memory_generated_singleton lower upper :=
  match upper with
  | L.Sum first (L.Constant 1) => if memory_generated_expr_eq lower first then true else false
  | L.Constant finish => match lower with
    | L.Constant start => Z.eqb finish (start+1) | _ => false end
  | _ => false end.
Fixpoint memory_generated_append first second :=
  match first with
  | L.SNil => second
  | L.SCons statement rest => L.SCons statement (memory_generated_append rest second) end.
Fixpoint memory_generated_affine_bounds statement :=
  match statement with
  | L.Instr instruction arguments => L.Instr instruction arguments
  | L.Guard test body => L.Guard (memory_generated_affine_test test) (memory_generated_affine_bounds body)
  | L.Seq statements =>
    match memory_generated_affine_bounds_list statements with
    | L.SCons statement L.SNil => statement
    | remaining => L.Seq remaining end
  | L.Loop lower upper body =>
    if memory_generated_singleton lower upper then
      memory_generated_substitute_stmt 0 lower (memory_generated_affine_bounds body)
    else
    let '(lower,lower_checks) := memory_generated_lower lower in
    let '(upper,upper_checks) := memory_generated_upper upper in
    L.Loop lower upper (memory_generated_lower_guards lower_checks
      (memory_generated_upper_guards upper_checks (memory_generated_affine_bounds body)))
  end
with memory_generated_affine_bounds_list statements :=
  match statements with
  | L.SNil => L.SNil
  | L.SCons statement rest =>
    let rest := memory_generated_affine_bounds_list rest in
    match memory_generated_affine_bounds statement with
    | L.Seq nested => memory_generated_append nested rest
    | statement => L.SCons statement rest end end.

(** Fuse only the dynamic schedule prefix shared by all instructions. In
    particular, an ordinal-first schedule keeps separate loop nests. This is
    also a proposal: the final extractor and dependence checker decide whether
    the resulting execution is a valid replacement. *)
Definition memory_generated_sequence first second :=
  L.Seq (L.SCons first (L.SCons second L.SNil)).
Fixpoint memory_generated_fuse depth first second {struct first} :=
  match depth with
  | O => memory_generated_sequence first second
  | S remaining =>
    match first,second with
    | L.Guard test body,L.Guard other tail =>
      if memory_generated_test_eq test other then
        L.Guard test (memory_generated_fuse depth body tail)
      else memory_generated_sequence first second
    | L.Loop lower upper body,L.Loop other_lower other_upper tail =>
      if memory_generated_expr_eq lower other_lower then
        if memory_generated_expr_eq upper other_upper then
          L.Loop lower upper (memory_generated_fuse remaining body tail)
        else memory_generated_sequence first second
      else memory_generated_sequence first second
    | _,_ => memory_generated_sequence first second end
  end.
Fixpoint memory_generated_fuse_list depth statements :=
  match statements with
  | [] => L.Seq L.SNil
  | [statement] => statement
  | statement::rest => memory_generated_fuse depth statement
      (memory_generated_fuse_list depth rest) end.
