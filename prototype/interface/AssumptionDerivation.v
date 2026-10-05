From Stdlib Require Import Bool List.
From GuardInterface Require Import GuardInterface GuardedRewrite.
Import ListNotations.
Set Implicit Arguments.

(** Sites describe textual execution domains, not just optimized iterations.
    A site may be a bound initialization, increment, address, or preload.
    The Boolean requirement is a specification, not an executable guard. *)
Record assumption_site (Parameters Point : Type) := AssumptionSite {
  site_occurs : Parameters -> Point -> Prop;
  site_holds : Parameters -> Point -> bool
}.

Definition collected_obligations {Parameters Point}
  (sites : list (assumption_site Parameters Point)) parameters :=
  forall site, In site sites -> forall point,
    site_occurs site parameters point -> site_holds site parameters point = true.

Definition projected_violation {Parameters Point}
  (sites : list (assumption_site Parameters Point)) parameters :=
  exists site point, In site sites /\ site_occurs site parameters point /\
    site_holds site parameters point = false.

Theorem projection_complement_exact Parameters Point
  (sites : list (assumption_site Parameters Point)) parameters :
  collected_obligations sites parameters <-> ~ projected_violation sites parameters.
Proof.
  split.
  - intros ALL [site [point [MEMBER [OCCURS BAD]]]].
    specialize (ALL site MEMBER point OCCURS); congruence.
  - intros NO_BAD site MEMBER point OCCURS.
    destruct (site_holds site parameters point) eqn:HOLDS; [reflexivity|].
    exfalso; apply NO_BAD; exists site, point; auto.
Qed.

Lemma collection_append Parameters Point (first second : list (assumption_site Parameters Point)) p :
  collected_obligations (first ++ second) p <->
    collected_obligations first p /\ collected_obligations second p.
Proof.
  unfold collected_obligations; split.
  - intro ALL; split; intros site MEMBER point OCCURS;
      apply ALL; auto; apply in_or_app; auto.
  - intros [FIRST SECOND] site MEMBER point OCCURS.
    apply in_app_or in MEMBER; destruct MEMBER; [apply FIRST|apply SECOND]; assumption.
Qed.

(** Quantifier elimination, range propagation, and guard simplification can
    be untrusted proposers. Their output is accepted through this one-way
    certificate. Rejecting additional valid inputs remains sound. *)
Record entry_derivation {Parameters Point} (domain : Parameters -> Prop)
  (sites : list (assumption_site Parameters Point)) (condition : Parameters -> Prop) := EntryDerivation {
  entry_derivation_sound : forall p, domain p -> condition p -> collected_obligations sites p
}.

Definition strengthen_entry_condition Parameters Point domain sites first second
  (DERIVE : @entry_derivation Parameters Point domain sites first)
  (IMPLIES : forall p, domain p -> second p -> first p) :
  entry_derivation domain sites second.
Proof.
  constructor; intros p DOMAIN CONDITION.
  apply (entry_derivation_sound DERIVE); auto.
Defined.

(** This theorem connects entry derivation to the actual supplied fragments.
    A model's validity under the collected requirements is still an instance
    obligation; no generic theorem claims arbitrary programs are affine. *)
Theorem derived_guarded_rewrite_equivalent S Parameters Point (H : guard_host S)
  (view : S -> Parameters) domain parameter_domain sites entry_condition
  source candidate condition
  (DOMAIN : forall s, domain s -> parameter_domain (view s))
  (DERIVE : @entry_derivation Parameters Point parameter_domain sites entry_condition)
  (CHECK : readonly_condition H domain (fun s => entry_condition (view s)) condition)
  (LOCAL : conditional_equivalence H domain
    (fun s => collected_obligations sites (view s)) source candidate) :
  local_equivalence H domain (guarded_rewrite H source candidate condition) source.
Proof.
  apply guarded_rewrite_equivalent with
    (premise := fun s => collected_obligations sites (view s)); [|exact LOCAL].
  apply readonly_condition_entails with (encoded := fun s => entry_condition (view s)); [exact CHECK|].
  intros s ENTRY ACCEPT; apply (entry_derivation_sound DERIVE); auto.
Qed.

Print Assumptions projection_complement_exact.
Print Assumptions collection_append.
Print Assumptions strengthen_entry_condition.
Print Assumptions derived_guarded_rewrite_equivalent.
