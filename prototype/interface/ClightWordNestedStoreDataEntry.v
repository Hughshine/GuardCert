(** The same checked packages with computationally accessible body metadata.
    Projection of an opaque correctness proof does not obstruct reduction of
    the ordinary site list.  Frozen predecessor definitions remain unchanged. *)
From Stdlib Require Import List.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightSyntaxEquality ClightStraightLine.
From GuardInterface Require Import ClightWordStoreSequenceFactory ClightWordNestedStoreFactory
  ClightMultiTensorDataPackage ClightMultiTensorRegionFactory.
Set Implicit Arguments.

Definition check_word_nested_store_body body : option (checked_word_store_body body).
Proof.
  destruct (check_word_store_sites (flatten_region body)) as [sites|] eqn:CHECK; [|exact None].
  pose proof (@check_word_store_sites_sound (flatten_region body) sites CHECK) as FACTS.
  refine (Some {|wsbody_sites:=sites;wsbody_flatten:=proj1 FACTS;wsbody_words:=proj2 FACTS|}).
  - eapply word_store_sites_body_normal; exact (proj1 FACTS).
  - eapply word_store_sites_body_quiet; exact (proj1 FACTS).
  - eapply word_store_sites_body_writes; exact (proj1 FACTS).
Defined.

Definition check_word_nested_store_data_source source public pool (d : word_nested_store_description) :
    option (word_nested_store_package source public pool).
Proof.
  destruct (statement_eq source (nws_source d)) as [SOURCE|]; [|exact None].
  destruct (allocate_word_nested_store (nws_source d) public pool) as [allocation|]; [|exact None].
  destruct (check_word_nested_store_body (nws_body d)) as [body|]; [|exact None].
  destruct (check_word_nested_store_static allocation body) as [STATIC|]; [|exact None].
  exact (Some (@WordNestedStorePackage source public pool d SOURCE allocation body STATIC)).
Defined.

Definition check_word_nested_store_data_polyhedral_source source public pool (d : word_nested_store_description)
    (describe_cached : statement -> option multi_tensor_region_description) :
    option (word_nested_store_polyhedral_package source public pool).
Proof.
  destruct (check_word_nested_store_data_source source public pool d) as [header|]; [|exact None].
  destruct (describe_cached (nws_cached (nwsp_allocation header))) as [description|]; [|exact None].
  destruct (check_multi_tensor_region_source (nws_cached (nwsp_allocation header)) description) as [model|];
    [|exact None].
  exact (Some (@WordNestedStorePolyhedralPackage source public pool header model)).
Defined.

Print Assumptions check_word_nested_store_body.
Print Assumptions check_word_nested_store_data_source.
Print Assumptions check_word_nested_store_data_polyhedral_source.
