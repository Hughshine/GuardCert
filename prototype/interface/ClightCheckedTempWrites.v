From Stdlib Require Import List Bool PArith.
From compcert.lib Require Import Maps.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightTempFrame.
Set Implicit Arguments.

(* Check assignment targets, separately from the expression read footprint.
   This service proves a temp frame; it makes no claim about memory effects. *)
Fixpoint check_temp_writes allowed code := match code with
  | Sskip | Sassign _ _ | Sbreak | Scontinue=>true
  | Sset identifier _=>existsb(Pos.eqb identifier) allowed
  | Ssequence first second | Sifthenelse _ first second | Sloop first second=>
      check_temp_writes allowed first && check_temp_writes allowed second
  | _=>false end.
Lemma check_temp_writes_sound allowed code : check_temp_writes allowed code=true -> writes_only allowed code.
Proof.
  induction code; cbn [check_temp_writes]; intros CHECK; try discriminate; try solve [constructor].
  all: try solve [apply andb_true_iff in CHECK as [FIRST SECOND]; constructor; auto].
  apply existsb_exists in CHECK as [identifier [MEMBER SAME]]; apply Pos.eqb_eq in SAME; subst; constructor; exact MEMBER.
Qed.
Print Assumptions check_temp_writes_sound.
