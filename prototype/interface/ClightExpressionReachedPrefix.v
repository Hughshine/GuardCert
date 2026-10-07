From Stdlib Require Import List ZArith.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap ClightRedundantSet
  ClightLoopSyntax CompCertMemoryActions.
From GuardInterface Require Import ClightExpressionBodyPrefix ClightObservedHeaderPrefix
  ClightStorePermissions ClightSignedExpressionProgress ClightStrictLoopProgress.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The guard entry is the observation and permission anchor. The source
    witness remains in the memory actually reached by earlier source bodies;
    moving it back to the guard-entry memory could lose initialized values. *)
Theorem expression_body_prefix_reached fe row cache bound body stable ready observations
  entry i current memory after final :
  ready entry -> register_domain cache entry ->
  0<=i<=Int.signed(temp_word cache (entry_temps entry)) ->
  header_observations_match (observations entry) (entry_memory entry) ->
  current!row=Some(Vint(Int.repr i)) -> temp_agree stable (entry_temps entry) current ->
  header_observations_match (observations entry) memory ->
  memory_accesses_back (entry_memory entry) memory ->
  exec_stmt fe (entry_ge entry) (entry_env entry) current memory
    (strict_frontend_loop row (signed_expression_test row bound) body) E0 after final Out_normal ->
  expression_body_prefix fe row cache bound body stable ready observations i entry.
Proof.
  intros READY CACHE RANGE INITIAL ROW FRAME OBSERVED BACK SOURCE.
  split; [exact READY|split; [exact CACHE|split; [exact RANGE|split; [exact INITIAL|]]]].
  exists current,memory,after,final.
  split; [exact ROW|split; [exact FRAME|split; [exact OBSERVED|split; [exact BACK|exact SOURCE]]]].
Qed.

Print Assumptions expression_body_prefix_reached.
