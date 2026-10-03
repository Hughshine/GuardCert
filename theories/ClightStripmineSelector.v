From Stdlib Require Import List ZArith.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight Ctypes.
From Guard Require Import ClightGuard ClightSyntaxEquality ClightTempFootprint ClightPrivateRegion ClightPrivateRule
  ClightFrontendLoopProtocol ClightFrontendRegion ClightCountedProtocol ClightStripmineLoops ClightStripmineRegion.
Import ListNotations PrivateRegion.
Set Implicit Arguments.

Definition select_stripmine (width : nat) (live : list ident) (pool : list (ident * type)) (source : statement) : option statement.
Proof.
  destruct pool as [|[limit ty] rest]; [exact None|].
  destruct (type_eq ty type_int32s); [|exact None].
  destruct (in_dec peq limit live) as [|FRESH]; [exact None|].
  destruct (Z_lt_dec 0 (Z.of_nat width)) as [POS|]; [|exact None].
  destruct (Z_le_dec (Z.of_nat width) Int.max_signed) as [MAX|]; [|exact None].
  destruct (propose_frontend_shape source) as [[[iterator bound] body]|]; [|exact None].
  destruct (statement_eq source (frontend_counted_loop iterator bound body)) as [SOURCE|]; [|exact None].
  destruct (peq iterator bound) as [|DISTINCT]; [exact None|].
  destruct (Bool.bool_dec (memory_body body) true) as [BODY|]; [|exact None].
  exact (Some (generated_private_region (@stripmine_region_rule live iterator bound limit width body DISTINCT FRESH (conj POS MAX) BODY))).
Defined.

Theorem select_stripmine_sound width live pool source target : select_stripmine width live pool source = Some target ->
  projected_region_contract live source target.
Proof.
  unfold select_stripmine; destruct pool as [|[limit ty] rest]; try discriminate.
  destruct (type_eq ty type_int32s); try discriminate.
  destruct (in_dec peq limit live); try discriminate.
  destruct (Z_lt_dec 0 (Z.of_nat width)); try discriminate.
  destruct (Z_le_dec (Z.of_nat width) Int.max_signed); try discriminate.
  destruct (propose_frontend_shape source) as [[[iterator bound] body]|]; try discriminate.
  destruct (statement_eq source (frontend_counted_loop iterator bound body)) as [SOURCE|]; try discriminate.
  destruct (peq iterator bound); try discriminate.
  destruct (Bool.bool_dec (memory_body body) true); try discriminate.
  intro SELECT; inversion SELECT; subst; apply encoded_private_rule_sound.
Qed.
Print Assumptions select_stripmine_sound.
