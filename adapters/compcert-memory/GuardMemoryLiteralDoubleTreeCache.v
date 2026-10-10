From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFrame.
From GuardMemory Require Import GuardMemoryLongControl GuardMemoryLiteralDoubleTreeData
  GuardMemoryDoubleTreeCacheEnvironment GuardMemoryDoubleTreeCacheParameters.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Materialize fixed model parameters as private I32 words. All expressions
    are constants; no source header load or input-memory license is required. *)
Fixpoint literal_double_cache_code (headers : list ident) (cache : ident -> ident) := match headers with
  | [] => Sskip
  | header::rest => Ssequence
      (Sset (cache header) (Econst_int (Int.repr (literal_double_parameter_value header)) memory_signed_int_type))
      (literal_double_cache_code rest cache) end.
Fixpoint literal_double_cache_temps (headers : list ident) (cache : ident -> ident) (temps : temp_env) := match headers with
  | [] => temps
  | header::rest => literal_double_cache_temps rest cache
      (PTree.set (cache header) (Vint (Int.repr (literal_double_parameter_value header))) temps) end.
Theorem literal_double_cache_execution headers cache fe ge locals temps memory :
  exec_stmt fe ge locals temps memory (literal_double_cache_code headers cache) E0
    (literal_double_cache_temps headers cache temps) memory Out_normal.
Proof.
  revert temps; induction headers; intro temps; cbn [literal_double_cache_code literal_double_cache_temps].
  - constructor.
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [constructor; constructor|apply IHheaders].
Qed.
Lemma literal_double_cache_frame headers cache temps key :
  ~ In key (map cache headers) -> (literal_double_cache_temps headers cache temps) ! key=temps ! key.
Proof.
  revert temps; induction headers as [|header rest IH]; intros temps FRESH; [reflexivity|].
  cbn [literal_double_cache_temps].
  rewrite IH by (intro MEMBER; apply FRESH; right; exact MEMBER).
  rewrite PTree.gso; [reflexivity|intro SAME; apply FRESH; left; symmetry; exact SAME].
Qed.
Theorem literal_double_cache_words headers cache temps :
  NoDup (map cache headers) -> forall header, In header headers ->
  (literal_double_cache_temps headers cache temps) ! (cache header)=
    Some (Vint (Int.repr (literal_double_parameter_value header))).
Proof.
  revert temps; induction headers as [|head rest IH]; intros temps DISTINCT header MEMBER; [contradiction|].
  inversion DISTINCT as [|key keys FRESH TAIL]; subst key keys.
  destruct MEMBER as [SAME|MEMBER].
  - subst header; cbn [literal_double_cache_temps]; rewrite literal_double_cache_frame by exact FRESH; apply PTree.gss.
  - cbn [literal_double_cache_temps]; apply IH; assumption.
Qed.
Theorem literal_double_cache_environment headers cache temps :
  NoDup (map cache headers) ->
  (forall header, In header headers -> Int.min_signed<=literal_double_parameter_value header<=Int.max_signed) ->
  double_tree_cache_environment headers cache literal_double_parameter_value literal_double_parameter_value
    (literal_double_cache_temps headers cache temps).
Proof.
  intros DISTINCT RANGES header MEMBER.
  exists (Int.repr (literal_double_parameter_value header)); split.
  - apply literal_double_cache_words; assumption.
  - rewrite Int.signed_repr by (apply RANGES; exact MEMBER).
    split; [apply Z.le_min_r|apply Z.le_max_r].
Qed.
Theorem literal_double_cache_values headers cache temps :
  NoDup (map cache headers) ->
  (forall header, In header headers -> Int.min_signed<=literal_double_parameter_value header<=Int.max_signed) ->
  forall header, In header headers -> double_tree_cached_value cache
    (literal_double_cache_temps headers cache temps) header=literal_double_parameter_value header.
Proof.
  intros DISTINCT RANGES header MEMBER; unfold double_tree_cached_value.
  rewrite literal_double_cache_words by assumption; apply Int.signed_repr; apply RANGES; exact MEMBER.
Qed.

Print Assumptions literal_double_cache_execution.
Print Assumptions literal_double_cache_frame.
Print Assumptions literal_double_cache_words.
Print Assumptions literal_double_cache_environment.
Print Assumptions literal_double_cache_values.
