From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import Values.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightTempFrame.
From GuardInterface Require Import ClightNestedExpressionPrefix.
Import ListNotations.
Set Implicit Arguments.

Lemma joint_inner_row_frame row column index entry stable current :
  ~In row stable -> ~In column stable -> row<>column ->
  current!row=Some(Vint(Int.repr index)) -> temp_agree stable(entry_temps entry) current ->
  temp_agree(row::stable)(entry_temps(nested_expression_inner_entry row column index entry)) current.
Proof.
  intros ROW_PRIVATE COLUMN_PRIVATE DISTINCT ROW FRAME identifier [SAME|MEMBER].
  - subst identifier; cbn [nested_expression_inner_entry entry_temps];
      rewrite PTree.gso by exact DISTINCT; rewrite PTree.gss; exact ROW.
  - cbn [nested_expression_inner_entry entry_temps]; rewrite !PTree.gso;
      try(intro SAME; subst identifier; contradiction); apply FRAME; exact MEMBER.
Qed.

Lemma joint_inner_cache_frame row column index entry stable cache :
  ~In row stable -> ~In column stable -> In cache stable ->
  (entry_temps(nested_expression_inner_entry row column index entry))!cache=(entry_temps entry)!cache.
Proof.
  intros ROW COLUMN CACHE; cbn [nested_expression_inner_entry entry_temps]; rewrite !PTree.gso;
    try reflexivity; intro SAME; subst cache; contradiction.
Qed.

Print Assumptions joint_inner_row_frame.
Print Assumptions joint_inner_cache_frame.
