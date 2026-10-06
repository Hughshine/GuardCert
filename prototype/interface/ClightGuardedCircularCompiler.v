From Stdlib Require Import List.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Clight Csem.
From compcert.x86 Require Import Asm.
From Guard Require Import ClightNoWrap ClightSyntaxEquality ClightTempFootprint
  ClightPrivatePool ClightOpenRegionContract.
From GuardInterface Require Import ClightCircularMachine ClightCircularGuard ClightCircularSimulation
  ClightOpenRegionCompiler ClightCommonRewriteCompiler.
Import ListNotations.
Set Implicit Arguments.

Definition propose_guarded_circular source :=
  match source with
  | Sloop (Ssequence (Ssequence Sskip (Sifthenelse
      (Ebinop One (Etempvar iterator _) (Ederef (Etempvar bound _) _) _) Sskip Sbreak))
      (Ssequence Sskip (Sassign (Ederef (Etempvar out _) _) _))) _ => Some (iterator,out,bound)
  | _ => None end.
Definition choose_guarded_circular live (pool : list (ident * type)) source : option statement :=
  match pool, propose_guarded_circular source with
  | (cache,_)::_, Some (iterator,out,bound) =>
    if in_dec peq cache live then None else
    if peq iterator bound then None else if peq iterator out then None else
    if statement_eq source (circular_memory_loop iterator out (circular_loaded_test iterator bound))
    then Some (guarded_circular_region iterator out bound cache) else None
  | _, _ => None end.
Theorem choose_guarded_circular_sound live pool source target :
  choose_guarded_circular live pool source = Some target -> open_region_contract live source target.
Proof.
  unfold choose_guarded_circular; destruct pool as [|[cache ty] pool]; [discriminate |].
  destruct (propose_guarded_circular source) as [[[iterator out] bound]|]; [|discriminate].
  destruct (in_dec peq cache live) as [|FRESH]; [discriminate |].
  destruct (peq iterator bound) as [|ITER_BOUND]; [discriminate |].
  destruct (peq iterator out) as [|ITER_OUT]; [discriminate |].
  destruct (statement_eq source (circular_memory_loop iterator out (circular_loaded_test iterator bound)))
    as [SOURCE|]; [|discriminate].
  intro SAME; injection SAME as SAME; subst source target; apply guarded_circular_contract; assumption.
Qed.
Definition circular_private_pool p :=
  map (fun declaration => (fst declaration,type_int32u)) (propose_private_names (program_temps p) 1).
Definition compile_guarded_circular :=
  compile_open_regions_after choose_guarded_circular transform_common_regions circular_private_pool.
Theorem compile_guarded_circular_correct p target : compile_guarded_circular p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof.
  apply compile_open_regions_after_correct.
  - exact choose_guarded_circular_sound.
  - exact transform_common_regions_correct.
Qed.

Print Assumptions choose_guarded_circular_sound.
Print Assumptions compile_guarded_circular_correct.
