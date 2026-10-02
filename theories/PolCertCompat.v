(** Proof-only compatibility for the isolated PolCert port to Rocq 9.2.
    The removed elimtype tactic applies an inductive eliminator to a fresh
    proof obligation. No semantic assumption or executable definition is added. *)
Tactic Notation "elimtype" constr(T) :=
  cut T; [let H := fresh "elimtype_proof" in intro H; case H; clear H | idtac].

(** Old automation used the zero-argument instantiate command between other
    tactics. Leaving that convenience step empty still requires all resulting
    proof terms to be checked by the current kernel. *)
Tactic Notation "instantiate" := idtac.

Tactic Notation "cutrewrite" constr(E) :=
  cut E; [let H := fresh "cutrewrite_proof" in intro H; rewrite H; clear H | idtac].
Tactic Notation "cutrewrite" "<-" constr(E) :=
  cut E; [let H := fresh "cutrewrite_proof" in intro H; rewrite <- H; clear H | idtac].

Declare Scope vector_scope.

(** This obsolete evar-inspection utility is defined by sflib but unused by the
    selected proof closure. Fail explicitly if a later closure actually uses it. *)
Tactic Notation "hget_evar" int_or_var(n) :=
  fail 1 "hget_evar is not supported by this proof port".
