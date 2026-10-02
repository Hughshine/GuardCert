From Stdlib Require Import Relations.

(** A language can obtain exact observation transport from two one-sided
    simulations. The kernel knows neither memory nor the observation type. *)
Section TRANSPORT.
Context {S O : Type}.
Variable extends : S -> S -> Prop.
Variable improves : O -> O -> Prop.
Variable action : S -> O -> S -> Prop.
Hypothesis OBSERVATION_ANTISYMMETRIC :
  forall a b, improves a b -> improves b a -> a = b.
Hypothesis ACTION_DETERMINATE : forall s a s' b s'',
  action s a s' -> action s b s'' -> a = b /\ s' = s''.
Hypothesis ACTION_EXTENDS : forall s a s' target,
  action s a s' -> extends s target ->
  exists b target', action target b target' /\ improves a b /\ extends s' target'.

Definition mutually_extends (first second : S) := extends first second /\ extends second first.

Theorem action_mutual_transport s a s' target :
  action s a s' -> mutually_extends s target ->
  exists target', action target a target' /\ mutually_extends s' target'.
Proof.
  intros SOURCE [FORWARD BACKWARD].
  destruct (ACTION_EXTENDS _ _ _ _ SOURCE FORWARD) as [b [target' [TARGET [AB NEXT]]]].
  destruct (ACTION_EXTENDS _ _ _ _ TARGET BACKWARD) as [a' [s'' [SOURCE' [BA BACK]]]].
  destruct (ACTION_DETERMINATE _ _ _ _ _ SOURCE SOURCE') as [VALUE STATE]. subst a' s''.
  assert (a = b) by (apply OBSERVATION_ANTISYMMETRIC; assumption). subst b.
  exists target'; split; [exact TARGET | split; assumption].
Qed.
End TRANSPORT.

Section OBSERVE.
Context {S O : Type}.
Variable extends : S -> S -> Prop.
Variable improves : O -> O -> Prop.
Variable observe : S -> option O.
Hypothesis OBSERVATION_ANTISYMMETRIC :
  forall a b, improves a b -> improves b a -> a = b.
Hypothesis OBSERVATION_EXTENDS : forall source a target,
  observe source = Some a -> extends source target ->
  exists b, observe target = Some b /\ improves a b.

Theorem observation_mutual_transport source target :
  mutually_extends extends source target -> observe source = observe target.
Proof.
  intros [FORWARD BACKWARD]. destruct (observe source) as [a|] eqn:SOURCE.
  - destruct (OBSERVATION_EXTENDS _ _ _ SOURCE FORWARD) as [b [TARGET AB]].
    destruct (OBSERVATION_EXTENDS _ _ _ TARGET BACKWARD) as [a' [SOURCE' BA]].
    rewrite SOURCE in SOURCE'; inversion SOURCE'; subst a'.
    assert (a = b) by (apply OBSERVATION_ANTISYMMETRIC; assumption). subst b; symmetry; exact TARGET.
  - destruct (observe target) as [b|] eqn:TARGET; auto.
    destruct (OBSERVATION_EXTENDS _ _ _ TARGET BACKWARD) as [a [SOURCE' BA]].
    rewrite SOURCE in SOURCE'; discriminate.
Qed.
End OBSERVE.

Print Assumptions action_mutual_transport.
Print Assumptions observation_mutual_transport.
