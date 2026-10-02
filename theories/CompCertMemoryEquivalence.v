From Stdlib Require Import Bool List ZArith.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST Values Memdata Memory Events.
From Guard Require Import BilateralTransport.

(** This is a concrete language-instance relation. The generic transport
    theorem only consumes simulation and determinacy properties. *)
Definition memory_equivalent := @mutually_extends mem Mem.extends.

Lemma value_lessdef_antisymmetric a b :
  Val.lessdef a b -> Val.lessdef b a -> a = b.
Proof. intros AB BA; inversion AB; inversion BA; subst; auto. Qed.

Lemma memory_equivalent_refl m : memory_equivalent m m.
Proof. split; apply Mem.extends_refl. Qed.
Lemma memory_equivalent_sym a b : memory_equivalent a b -> memory_equivalent b a.
Proof. intros [AB BA]; split; assumption. Qed.
Lemma memory_equivalent_trans a b c :
  memory_equivalent a b -> memory_equivalent b c -> memory_equivalent a c.
Proof. intros [AB BA] [BC CB]; split; eapply Mem.extends_extends_compose; eauto. Qed.

Lemma memory_equivalent_load chunk b ofs first second value :
  memory_equivalent first second -> Mem.load chunk first b ofs = Some value ->
  Mem.load chunk second b ofs = Some value.
Proof.
  intros EQ LOAD.
  set (action := fun (m : mem) (v : val) (m' : mem) => Mem.load chunk m b ofs = Some v /\ m' = m).
  assert (DETERMINATE : forall m a m' v m'', action m a m' -> action m v m'' ->
    a = v /\ m' = m'') by (intros m a m' v m'' [A S] [B T]; split; congruence).
  assert (EXTEND : forall m v m' target, action m v m' -> Mem.extends m target ->
    exists value target', action target value target' /\ Val.lessdef v value /\ Mem.extends m' target').
  { intros m v m' target [READ SAME] EXT; subst m'.
    destruct (Mem.load_extends _ _ _ _ _ _ EXT READ) as [v' [READ' LESS]].
    exists v', target; split; [split; [exact READ' | reflexivity] | split; assumption]. }
  destruct (@action_mutual_transport mem val Mem.extends Val.lessdef action
    value_lessdef_antisymmetric DETERMINATE EXTEND first value first second
    (conj LOAD eq_refl) EQ) as [final [[READ SAME] NEXT]]. exact READ.
Qed.

Lemma memory_equivalent_store chunk b ofs value first second first' :
  memory_equivalent first second -> Mem.store chunk first b ofs value = Some first' ->
  exists second', Mem.store chunk second b ofs value = Some second' /\ memory_equivalent first' second'.
Proof.
  intros EQ STORE.
  set (action := fun (m : mem) (_ : unit) (m' : mem) => Mem.store chunk m b ofs value = Some m').
  assert (DETERMINATE : forall m a m' v m'', action m a m' -> action m v m'' ->
    a = v /\ m' = m'') by (intros m [] m' [] m'' A B; split; congruence).
  assert (EXTEND : forall m a m' target, action m a m' -> Mem.extends m target ->
    exists value target', action target value target' /\ a = value /\ Mem.extends m' target').
  { intros m [] m' target WRITE EXT.
    destruct (Mem.store_within_extends chunk m target b ofs value m' value EXT WRITE (Val.lessdef_refl value))
      as [target' [WRITE' NEXT]]. exists tt, target'; split; [exact WRITE' | split; [reflexivity | exact NEXT]]. }
  exact (@action_mutual_transport mem unit Mem.extends (@eq unit) action
    (fun a b AB _ => AB) DETERMINATE EXTEND first tt first' second STORE EQ).
Qed.

Lemma memory_equivalent_valid_pointer first second b ofs :
  memory_equivalent first second ->
  Mem.valid_pointer first b ofs = Mem.valid_pointer second b ofs.
Proof.
  intros [AB BA]; apply Bool.eq_true_iff_eq; split;
    intro VALID; eapply Mem.valid_pointer_extends; eauto.
Qed.

Lemma memory_equivalent_weak_valid_pointer first second b ofs :
  memory_equivalent first second ->
  Mem.weak_valid_pointer first b ofs = Mem.weak_valid_pointer second b ofs.
Proof.
  intros [AB BA]; apply Bool.eq_true_iff_eq; split;
    intro VALID; eapply Mem.weak_valid_pointer_extends; eauto.
Qed.

Lemma memory_equivalent_external_call ef ge args trace value first second first' :
  memory_equivalent first second -> external_call ef ge args first trace value first' ->
  exists second', external_call ef ge args second trace value second' /\ memory_equivalent first' second'.
Proof.
  intros EQ CALL.
  assert (ARGS : Val.lessdef_list args args) by (clear CALL; induction args; constructor; auto).
  set (action := fun (m : mem) (v : val) (m' : mem) => external_call ef ge args m trace v m').
  assert (DETERMINATE : forall m a m' v m'', action m a m' -> action m v m'' ->
    a = v /\ m' = m'').
  { intros m a m' v m'' A B.
    destruct (@external_call_determ ef ge args m trace a m' trace v m'' A B) as [_ SAME]. apply SAME; reflexivity. }
  assert (EXTEND : forall m v m' target, action m v m' -> Mem.extends m target ->
    exists value target', action target value target' /\ Val.lessdef v value /\ Mem.extends m' target').
  { intros m v m' target RUN EXT.
    destruct (@external_call_mem_extends ef ge args m trace v m' target args RUN EXT ARGS)
      as [value' [target' [RUN' [LESS [NEXT FRAME]]]]].
    exists value', target'; split; [exact RUN' | split; assumption]. }
  exact (@action_mutual_transport mem val Mem.extends Val.lessdef action
    value_lessdef_antisymmetric DETERMINATE EXTEND first value first' second CALL EQ).
Qed.

Lemma memory_equivalent_loadv chunk address first second value :
  memory_equivalent first second -> Mem.loadv chunk first address = Some value ->
  Mem.loadv chunk second address = Some value.
Proof.
  intros EQ LOAD; destruct address; cbn [Mem.loadv] in *; try discriminate.
  destruct (zle _ _); try discriminate. eapply memory_equivalent_load; eauto.
Qed.

Lemma memory_equivalent_storev chunk address value first second first' :
  memory_equivalent first second -> Mem.storev chunk first address value = Some first' ->
  exists second', Mem.storev chunk second address value = Some second' /\ memory_equivalent first' second'.
Proof.
  intros EQ STORE; destruct address; cbn [Mem.storev] in *; try discriminate.
  destruct (zle _ _); try discriminate. eapply memory_equivalent_store; eauto.
Qed.

Lemma memory_value_lessdef_antisymmetric a b :
  memval_lessdef a b -> memval_lessdef b a -> a = b.
Proof.
  intros AB BA; unfold memval_lessdef in *; inversion AB; subst; inversion BA; subst;
    try discriminate; auto.
  f_equal; eapply value_lessdef_antisymmetric; apply val_inject_id; assumption.
Qed.

Lemma memory_values_lessdef_antisymmetric a b :
  list_forall2 memval_lessdef a b -> list_forall2 memval_lessdef b a -> a = b.
Proof.
  intro AB; induction AB; intro BA; inversion BA; subst; auto.
  f_equal; [eapply memory_value_lessdef_antisymmetric; eauto | auto].
Qed.

Lemma memory_equivalent_loadbytes first second b ofs count : memory_equivalent first second ->
  Mem.loadbytes first b ofs count = Mem.loadbytes second b ofs count.
Proof.
  intro EQ. eapply (@observation_mutual_transport mem (list memval) Mem.extends
    (list_forall2 memval_lessdef) (fun m => Mem.loadbytes m b ofs count)
    memory_values_lessdef_antisymmetric); [|exact EQ].
  intros m result target RUN EXT. eapply Mem.loadbytes_extends; eauto.
Qed.

Lemma memory_equivalent_storebytes b ofs bytes first second first' :
  memory_equivalent first second -> Mem.storebytes first b ofs bytes = Some first' ->
  exists second', Mem.storebytes second b ofs bytes = Some second' /\ memory_equivalent first' second'.
Proof.
  intros EQ STORE.
  assert (BYTES : list_forall2 memval_lessdef bytes bytes).
  { clear STORE; induction bytes; constructor; auto using memval_lessdef_refl. }
  set (action := fun (m : mem) (_ : unit) (m' : mem) => Mem.storebytes m b ofs bytes = Some m').
  assert (DETERMINATE : forall m a m' v m'', action m a m' -> action m v m'' ->
    a = v /\ m' = m'') by (intros m [] m' [] m'' A B; split; congruence).
  assert (EXTEND : forall m a m' target, action m a m' -> Mem.extends m target ->
    exists value target', action target value target' /\ a = value /\ Mem.extends m' target').
  { intros m [] m' target WRITE EXT.
    destruct (Mem.storebytes_within_extends m target b ofs bytes m' bytes EXT WRITE BYTES)
      as [target' [WRITE' NEXT]]. exists tt, target'; split; [exact WRITE' | split; [reflexivity | exact NEXT]]. }
  exact (@action_mutual_transport mem unit Mem.extends (@eq unit) action
    (fun a b AB _ => AB) DETERMINATE EXTEND first tt first' second STORE EQ).
Qed.

Lemma memory_equivalent_alloc lo hi first second first' b :
  memory_equivalent first second -> Mem.alloc first lo hi = (first', b) ->
  exists second', Mem.alloc second lo hi = (second', b) /\ memory_equivalent first' second'.
Proof.
  intros EQ ALLOC.
  set (action := fun (m : mem) (b : block) (m' : mem) => Mem.alloc m lo hi = (m', b)).
  assert (DETERMINATE : forall m a m' v m'', action m a m' -> action m v m'' ->
    a = v /\ m' = m'') by (intros m a m' v m'' A B; split; congruence).
  assert (EXTEND : forall m a m' target, action m a m' -> Mem.extends m target ->
    exists value target', action target value target' /\ a = value /\ Mem.extends m' target').
  { intros m a m' target RUN EXT.
    destruct (Mem.alloc_extends m target lo hi a m' lo hi EXT RUN (Z.le_refl _) (Z.le_refl _))
      as [target' [RUN' NEXT]]. exists a, target'; split; [exact RUN' | split; [reflexivity | exact NEXT]]. }
  exact (@action_mutual_transport mem block Mem.extends (@eq block) action
    (fun a b AB _ => AB) DETERMINATE EXTEND first b first' second ALLOC EQ).
Qed.

Lemma memory_equivalent_free b lo hi first second first' :
  memory_equivalent first second -> Mem.free first b lo hi = Some first' ->
  exists second', Mem.free second b lo hi = Some second' /\ memory_equivalent first' second'.
Proof.
  intros EQ FREE.
  set (action := fun (m : mem) (_ : unit) (m' : mem) => Mem.free m b lo hi = Some m').
  assert (DETERMINATE : forall m a m' v m'', action m a m' -> action m v m'' ->
    a = v /\ m' = m'') by (intros m [] m' [] m'' A B; split; congruence).
  assert (EXTEND : forall m a m' target, action m a m' -> Mem.extends m target ->
    exists value target', action target value target' /\ a = value /\ Mem.extends m' target').
  { intros m [] m' target RUN EXT.
    destruct (Mem.free_parallel_extends m target b lo hi m' EXT RUN)
      as [target' [RUN' NEXT]]. exists tt, target'; split; [exact RUN' | split; [reflexivity | exact NEXT]]. }
  exact (@action_mutual_transport mem unit Mem.extends (@eq unit) action
    (fun a b AB _ => AB) DETERMINATE EXTEND first tt first' second FREE EQ).
Qed.

Lemma memory_equivalent_free_list regions first second first' :
  memory_equivalent first second -> Mem.free_list first regions = Some first' ->
  exists second', Mem.free_list second regions = Some second' /\ memory_equivalent first' second'.
Proof.
  revert first second first'; induction regions as [|[[b lo] hi] rest IH];
    intros first second first' EQ FREE; simpl in FREE |- *.
  - inversion FREE; subst first'; exists second; split; auto.
  - destruct (Mem.free first b lo hi) as [middle|] eqn:STEP; try discriminate.
    destruct (memory_equivalent_free _ _ _ _ _ _ EQ STEP) as [target [STEP' NEXT]].
    rewrite STEP'. eapply IH; eauto.
Qed.

Print Assumptions memory_equivalent_load.
Print Assumptions memory_equivalent_external_call.
