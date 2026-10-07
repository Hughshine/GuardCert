From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers Coqlib.
From compcert.common Require Import AST.
From polcert.lib Require Import Linalg.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryAffineSourceLoop GuardMemoryIntervalBox
  GuardMemoryDynamicTensorBackend GuardMemoryTensorSourceRegion.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Count domains are [0,count); scalar domains are singletons.  The symbolic
    upper endpoint of a singleton is the scalar itself, so MAX_SIGNED+1 is never
    materialized in generated code. *)
Fixpoint tensor_box_bounds layout (axes:bool) identifiers : option(list(L.expr*L.expr)) :=
  match identifiers with
  | []=>Some []
  | identifier::rest=>match memory_source_position identifier layout,tensor_box_bounds layout axes rest with
    | Some index,Some bounds=>Some((if axes then
        (L.Constant 0,L.Sum(L.Var index)(L.Constant(-1)))else(L.Var index,L.Var index))::bounds)
    | _,_=>None end end.
Definition tensor_box_ranges (axes scalars:list ident)(valuation:ident->Z) :=
  map(fun identifier=>(0,valuation identifier))axes++
  map(fun identifier=>(valuation identifier,valuation identifier+1))scalars.
Definition tensor_box_endpoints_view values codes bounds :=
  Forall2(fun code bound=>L.eval_expr values(fst code)=fst bound /\
    L.eval_expr values(snd code)=snd bound-1)codes bounds.
Lemma tensor_box_bounds_value layout axes identifiers codes valuation :
  tensor_box_bounds layout axes identifiers=Some codes ->
  tensor_box_endpoints_view(map valuation layout)codes
    (map(fun identifier=>if axes then(0,valuation identifier)else(valuation identifier,valuation identifier+1))identifiers).
Proof.
  revert codes; induction identifiers as [|identifier identifiers IH]; intros codes ENCODE; cbn in ENCODE.
  - inversion ENCODE; constructor.
  - destruct(memory_source_position identifier layout)as [index|]eqn:POSITION; [|discriminate].
    destruct(tensor_box_bounds layout axes identifiers)as [tail|]eqn:TAIL; [|discriminate].
    inversion ENCODE; subst; constructor; [|apply IH; reflexivity].
    destruct axes; cbn [fst snd L.eval_expr]; rewrite(@memory_source_position_value identifier layout index valuation POSITION); split; ring.
Qed.

Fixpoint tensor_box_dot (maximum:bool) coefficients bounds : L.expr := match coefficients,bounds with
  | coefficient::rest,(lower,upper)::tail=>
      if coefficient =? 0 then tensor_box_dot maximum rest tail else
      L.Sum(L.Mult coefficient(if (0 <=? coefficient)then(if maximum then upper else lower)
          else(if maximum then lower else upper)))(tensor_box_dot maximum rest tail)
  | _,_=>L.Constant 0 end.
Lemma tensor_box_dot_value values codes bounds coefficients maximum :
  tensor_box_endpoints_view values codes bounds -> Forall(fun bound=>fst bound<snd bound)bounds ->
  length coefficients=length bounds ->
  L.eval_expr values(tensor_box_dot maximum coefficients codes)=
    if maximum then interval_dot_upper coefficients bounds else interval_dot_lower coefficients bounds.
Proof.
  intros VIEW; revert coefficients; induction VIEW as [|[lower upper] [first last] codes bounds [LOW HIGH] VIEW IH];
    intros [|coefficient coefficients] VALID LENGTH; cbn in LENGTH; try discriminate.
  - destruct maximum; reflexivity.
  - inversion VALID; subst; cbn [fst snd] in *.
    specialize(IH coefficients ltac:(assumption)ltac:(lia)).
    cbn [tensor_box_dot]; destruct(coefficient =? 0)eqn:ZERO.
    + apply Z.eqb_eq in ZERO; subst coefficient; rewrite IH; destruct maximum; cbn; ring.
    + destruct(0 <=? coefficient)eqn:SIGN; destruct maximum; cbn [L.eval_expr]; rewrite IH,?LOW,?HIGH;
        cbn [interval_dot_upper interval_dot_lower fst snd];
        [apply Z.leb_le in SIGN; rewrite Z.max_r by nia|
         apply Z.leb_le in SIGN; rewrite Z.min_l by nia|
         apply Z.leb_gt in SIGN; rewrite Z.max_l by nia|
         apply Z.leb_gt in SIGN; rewrite Z.min_r by nia]; reflexivity.
Qed.
Definition tensor_box_term maximum term bounds := L.Sum(tensor_box_dot maximum(fst term)bounds)(L.Constant(snd term)).
Definition tensor_box_test extent term bounds :=
  if Nat.eqb(length(fst term))(length bounds)then
    L.And(L.LE(L.Constant 0)(tensor_box_term false term bounds))
      (L.Not(L.LE extent(tensor_box_term true term bounds)))else L.TConstantTest false.
Theorem tensor_box_test_value values codes bounds term extent size :
  tensor_box_endpoints_view values codes bounds -> Forall(fun bound=>fst bound<snd bound)bounds ->
  L.eval_expr values extent=size ->
  L.eval_test values(tensor_box_test extent term codes)=interval_box_check bounds size term.
Proof.
  intros VIEW VALID EXTENT; unfold tensor_box_test,interval_box_check.
  pose proof(Forall2_length VIEW)as LENGTH; rewrite LENGTH.
  destruct(Nat.eqb(length(fst term))(length bounds))eqn:ARITY; [|reflexivity].
  apply Nat.eqb_eq in ARITY; cbn [L.eval_test L.eval_expr]; unfold tensor_box_term; cbn [L.eval_expr].
  rewrite(@tensor_box_dot_value values codes bounds(fst term)false VIEW VALID ARITY),
    (@tensor_box_dot_value values codes bounds(fst term)true VIEW VALID ARITY),EXTENT.
  cbn; rewrite(Z.leb_antisym(interval_dot_upper(fst term)bounds+snd term)size),negb_involutive; reflexivity.
Qed.

Definition tensor_box_dimension layout source := match source with
  | TensorDimensionConstant value=>Some(L.Constant(Int.signed(Int.repr value)))
  | TensorDimensionTemp identifier=>option_map L.Var(memory_source_position identifier layout)end.
Definition tensor_box_dimension_value valuation source := match source with
  | TensorDimensionConstant value=>Int.signed(Int.repr value)
  | TensorDimensionTemp identifier=>valuation identifier end.
Lemma tensor_box_dimension_exact layout source code valuation : tensor_box_dimension layout source=Some code ->
  L.eval_expr(map valuation layout)code=tensor_box_dimension_value valuation source.
Proof.
  destruct source; cbn; [intro SAME; inversion SAME; reflexivity|].
  destruct(memory_source_position i layout)as [index|]eqn:POSITION; cbn; [|discriminate].
  intro SAME; inversion SAME; subst; apply memory_source_position_value; exact POSITION.
Qed.
Fixpoint tensor_box_access_test layout codes dimensions terms : option L.test := match dimensions,terms with
  | [],[]=>Some(L.TConstantTest true)
  | dimension::rest,term::tail=>match tensor_box_dimension layout dimension,tensor_box_access_test layout codes rest tail with
      | Some extent,Some next=>Some(L.And(tensor_box_test extent term codes)next)|_,_=>None end
  | _,_=>None end.
Theorem tensor_box_access_value layout codes bounds dimensions terms test valuation :
  tensor_box_endpoints_view(map valuation layout)codes bounds -> Forall(fun bound=>fst bound<snd bound)bounds ->
  tensor_box_access_test layout codes dimensions terms=Some test ->
  L.eval_test(map valuation layout)test=
    tensor_coordinate_box_check bounds(map(tensor_box_dimension_value valuation)dimensions)terms.
Proof.
  intros VIEW VALID; revert terms test; induction dimensions as [|dimension dimensions IH];
    intros [|term terms] test ENCODE; cbn in ENCODE; try discriminate.
  - inversion ENCODE; reflexivity.
  - destruct(tensor_box_dimension layout dimension)as [extent|]eqn:EXTENT; [|discriminate].
    destruct(tensor_box_access_test layout codes dimensions terms)as [next|]eqn:NEXT; [|discriminate].
    inversion ENCODE; subst; cbn [L.eval_test map tensor_coordinate_box_check].
    rewrite(@tensor_box_test_value(map valuation layout)codes bounds term extent
      (tensor_box_dimension_value valuation dimension)VIEW VALID(@tensor_box_dimension_exact layout dimension extent valuation EXTENT)),
      (IH terms next NEXT); reflexivity.
Qed.
Fixpoint tensor_box_accesses_test layout codes dimensions accesses : option L.test := match accesses with
  | []=>Some(L.TConstantTest true)
  | terms::rest=>match tensor_box_access_test layout codes dimensions terms,tensor_box_accesses_test layout codes dimensions rest with
      | Some first,Some next=>Some(L.And first next)|_,_=>None end end.
Theorem tensor_box_accesses_value layout codes bounds dimensions accesses test valuation :
  tensor_box_endpoints_view(map valuation layout)codes bounds -> Forall(fun bound=>fst bound<snd bound)bounds ->
  tensor_box_accesses_test layout codes dimensions accesses=Some test ->
  L.eval_test(map valuation layout)test=forallb(fun terms=>
    tensor_coordinate_box_check bounds(map(tensor_box_dimension_value valuation)dimensions)terms)accesses.
Proof.
  intros VIEW VALID; revert test; induction accesses; intros test ENCODE; cbn in ENCODE.
  - inversion ENCODE; reflexivity.
  - destruct(tensor_box_access_test layout codes dimensions a)as [first|]eqn:FIRST; [|discriminate].
    destruct(tensor_box_accesses_test layout codes dimensions accesses)as [next|]eqn:NEXT; [|discriminate].
    inversion ENCODE; subst; cbn [L.eval_test forallb];
      rewrite(@tensor_box_access_value layout codes bounds dimensions a first valuation VIEW VALID FIRST),(IHaccesses next eq_refl); reflexivity.
Qed.
Definition tensor_box_entry_test layout axes scalars dimensions accesses :=
  match tensor_box_bounds layout true axes,tensor_box_bounds layout false scalars with
  | Some first,Some second=>tensor_box_accesses_test layout(first++second)dimensions accesses|_,_=>None end.
Theorem tensor_box_entry_value layout axes scalars dimensions accesses test valuation :
  Forall(fun identifier=>0<valuation identifier)axes ->
  tensor_box_entry_test layout axes scalars dimensions accesses=Some test ->
  L.eval_test(map valuation layout)test=forallb(fun terms=>
    tensor_coordinate_box_check(tensor_box_ranges axes scalars valuation)
      (map(tensor_box_dimension_value valuation)dimensions)terms)accesses.
Proof.
  intros POSITIVE ENCODE; unfold tensor_box_entry_test in ENCODE.
  destruct(tensor_box_bounds layout true axes)as [first|]eqn:FIRST; [|discriminate].
  destruct(tensor_box_bounds layout false scalars)as [second|]eqn:SECOND; [|discriminate].
  eapply tensor_box_accesses_value; [unfold tensor_box_endpoints_view,tensor_box_ranges; apply Forall2_app;
    [exact(@tensor_box_bounds_value layout true axes first valuation FIRST)|exact(@tensor_box_bounds_value layout false scalars second valuation SECOND)]| |exact ENCODE].
  unfold tensor_box_ranges; apply Forall_app; split; apply Forall_map,Forall_forall; intros identifier MEMBER; cbn.
  - apply Forall_forall with(x:=identifier)in POSITIVE; assumption.
  - lia.
Qed.
Print Assumptions tensor_box_bounds_value.
Print Assumptions tensor_box_dot_value.
Print Assumptions tensor_box_test_value.
Print Assumptions tensor_box_dimension_exact.
Print Assumptions tensor_box_access_value.
Print Assumptions tensor_box_entry_value.
