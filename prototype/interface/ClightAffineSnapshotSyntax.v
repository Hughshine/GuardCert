From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight Ctypes Cop.
From Guard Require Import ClightSyntaxEquality ClightStraightLine ClightFrontendLoopProtocol
  ClightFrontendRegion ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightLoadedSequenceProgress ClightWordReadSnapshots
  ClightAffineHeaderSnapshots ClightAffineSnapshotRows ClightAffineInnerPointerCandidates.
Import ListNotations.
Set Implicit Arguments.

Definition snapshot_word_binary_check op := match op with Oadd|Osub|Omul=>true|_=>false end.
Fixpoint snapshot_word_expression_check code := match code with
  | Econst_int _ ty | Etempvar _ ty => if type_eq ty type_int32s then true else false
  | Ederef(Etempvar pointer ty) result_ty =>
      if expression_eq(Ederef(Etempvar pointer ty)result_ty)(signed_load pointer)then true else false
  | Ebinop op first second ty => if type_eq ty type_int32s then
      snapshot_word_binary_check op && (snapshot_word_expression_check first && snapshot_word_expression_check second)
      else false
  | _=>false end.

Lemma snapshot_word_binary_check_sound op : snapshot_word_binary_check op=true ->
  op=Oadd \/ op=Osub \/ op=Omul.
Proof. destruct op; cbn; intros; try discriminate; auto. Qed.

Theorem snapshot_word_expression_check_sound code : snapshot_word_expression_check code=true ->
  snapshot_word_expression code.
Proof.
  induction code; cbn [snapshot_word_expression_check]; try discriminate.
  - destruct(type_eq _ _)as [TYPE|]; [subst; intro; constructor|discriminate].
  - destruct(type_eq _ _)as [TYPE|]; [subst; intro; constructor|discriminate].
  - destruct code; try discriminate.
    destruct(expression_eq _ _)as [SAME|]; [rewrite SAME; intro; constructor|discriminate].
  - destruct(type_eq _ _)as [TYPE|]; [subst|discriminate].
    rewrite !andb_true_iff; intros [OP [FIRST SECOND]]; constructor;
      [apply snapshot_word_binary_check_sound; exact OP|apply IHcode1; exact FIRST|apply IHcode2; exact SECOND].
Qed.

(** Every field here is produced by ordinary syntax checks or by the existing
    affine-package checker. There is no source-user semantic callback. *)
Record affine_snapshot_source_package original := AffineSnapshotSourcePackage {
  snapshot_cached_source : statement;
  snapshot_cached_package : memory_affine_inner_pointer_package snapshot_cached_source;
  snapshot_root : ident;
  snapshot_child : ident;
  snapshot_child_cache : ident;
  snapshot_original_header : expr;
  snapshot_source_exact : original=affine_snapshot_source snapshot_cached_package snapshot_root snapshot_original_header;
  snapshot_header_word : snapshot_word_expression snapshot_original_header;
  snapshot_child_read : In snapshot_child(snapshot_word_reads snapshot_original_header);
  snapshot_root_protected :
    snapshot_root<>affine_inner_pointer_row(affine_inner_pointer_shape snapshot_cached_package) /\
    snapshot_root<>affine_inner_pointer_column(affine_inner_pointer_shape snapshot_cached_package) /\
    snapshot_root<>affine_inner_pointer_inner_bound(affine_inner_pointer_shape snapshot_cached_package);
  snapshot_child_protected :
    snapshot_child<>affine_inner_pointer_row(affine_inner_pointer_shape snapshot_cached_package) /\
    snapshot_child<>affine_inner_pointer_column(affine_inner_pointer_shape snapshot_cached_package) /\
    snapshot_child<>affine_inner_pointer_inner_bound(affine_inner_pointer_shape snapshot_cached_package);
  snapshot_cache_member : In snapshot_child_cache(affine_snapshot_stable snapshot_cached_package snapshot_root snapshot_child);
  snapshot_cached_body_exact : affine_inner_pointer_outer_body(affine_inner_pointer_shape snapshot_cached_package)=
    affine_snapshot_body snapshot_cached_package
      (snapshot_word_replace(single_snapshot_binding snapshot_child snapshot_child_cache)snapshot_original_header)
}.

Definition check_affine_snapshot_source original cached_source
  (package:memory_affine_inner_pointer_package cached_source)(root child child_cache:ident)(header:expr) :
  option(affine_snapshot_source_package original).
Proof.
  destruct(statement_eq original(affine_snapshot_source package root header))as [SOURCE|]; [|exact None].
  destruct(Bool.bool_dec(snapshot_word_expression_check header)true)as [WORD|]; [|exact None].
  destruct(in_dec peq child(snapshot_word_reads header))as [READ|]; [|exact None].
  destruct(peq root(affine_inner_pointer_row(affine_inner_pointer_shape package)))as [|ROOT_ROW]; [exact None|].
  destruct(peq root(affine_inner_pointer_column(affine_inner_pointer_shape package)))as [|ROOT_COLUMN]; [exact None|].
  destruct(peq root(affine_inner_pointer_inner_bound(affine_inner_pointer_shape package)))as [|ROOT_BOUND]; [exact None|].
  destruct(peq child(affine_inner_pointer_row(affine_inner_pointer_shape package)))as [|CHILD_ROW]; [exact None|].
  destruct(peq child(affine_inner_pointer_column(affine_inner_pointer_shape package)))as [|CHILD_COLUMN]; [exact None|].
  destruct(peq child(affine_inner_pointer_inner_bound(affine_inner_pointer_shape package)))as [|CHILD_BOUND]; [exact None|].
  destruct(in_dec peq child_cache(affine_snapshot_stable package root child))as [CACHE|]; [|exact None].
  destruct(statement_eq(affine_inner_pointer_outer_body(affine_inner_pointer_shape package))
    (affine_snapshot_body package(snapshot_word_replace(single_snapshot_binding child child_cache)header)))
    as [BODY|]; [|exact None].
  exact(Some(@AffineSnapshotSourcePackage original cached_source package root child child_cache header SOURCE
    (snapshot_word_expression_check_sound header WORD)READ
    (conj ROOT_ROW(conj ROOT_COLUMN ROOT_BOUND))(conj CHILD_ROW(conj CHILD_COLUMN CHILD_BOUND))CACHE BODY)).
Defined.

(** The proposed source is checked independently of optimizer metadata. The
    first load leaf selects this two-observer family; extra unsupported leaves
    still fail the checked cached-affine shape. *)
Definition propose_affine_snapshot_source root_cache child_cache original :=
  match checked_loaded_progress original with
  | Some(row,root,outer) => match flatten_region outer with
    | [Sset inner_bound header;Sset column _;inner] =>
      match snapshot_word_reads header,propose_frontend_shape inner with
      | child::_,Some(_,_,leaf) =>
        let cached_header:=snapshot_word_replace(single_snapshot_binding child child_cache)header in
        Some(root,child,header,frontend_counted_loop row root_cache
          (affine_setup_child column inner_bound cached_header leaf))
      | _,_=>None end
    | _=>None end
  | None=>None end.

Definition describe_affine_snapshot_source(profile:affine_inner_pointer_profiler)root_cache child_cache original :=
  match propose_affine_snapshot_source root_cache child_cache original with
  | Some(root,child,header,cached_source) => match profile cached_source with
    | Some metadata => match describe_affine_inner_pointer_at cached_source metadata with
      | Some package=>check_affine_snapshot_source original package root child child_cache header
      | None=>None end
    | None=>None end
  | None=>None end.

Print Assumptions snapshot_word_expression_check_sound.
Print Assumptions check_affine_snapshot_source.
Print Assumptions describe_affine_snapshot_source.
