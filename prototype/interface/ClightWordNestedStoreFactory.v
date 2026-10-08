(** Data-only entry for the two-axis loaded store-list family.  The factory
    produces private resources and static guard obligations; it does not ask
    source users to supply execution or model-correspondence proofs. *)
From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightSyntaxEquality ClightCondition ClightTempFrame
  ClightTempFootprint ClightRegionProgress.
From GuardInterface Require Import ClightTensorRegionPackage ClightMultiTensorScanAllocation
  ClightMultiTensorDataPackage ClightMultiTensorRegionFactory ClightNestedLoadedOffset
  ClightNestedExpressionTransport ClightSignedExpressionProgress ClightWordStoreSequence
  ClightWordStoreSequenceFactory ClightWordStoreNestedGuard.
Import ListNotations.
Set Implicit Arguments.

Record word_nested_store_description := WordNestedStoreDescription {
  nws_row : ident; nws_pointer : ident; nws_delta : int;
  nws_column : ident; nws_child_pointer : ident; nws_child_delta : int;
  nws_body : statement
}.
Definition nws_source d := nested_loaded_offset_source (nws_row d) (nws_pointer d) (nws_delta d)
  (nws_column d) (nws_child_pointer d) (nws_child_delta d) (nws_body d).

(** Seven roles, with no artificial source dimension: two caches, four scan
    counters/limits and one Boolean.  A short or conflicting pool refuses. *)
Record word_nested_store_allocation source public pool := WordNestedStoreAllocation {
  nwa_cache : ident; nwa_child_cache : ident;
  nwa_row_cursor : ident; nwa_row_limit : ident;
  nwa_column_cursor : ident; nwa_column_limit : ident; nwa_flag : ident;
  nwa_unique : NoDup [nwa_cache;nwa_child_cache;nwa_row_cursor;nwa_row_limit;
    nwa_column_cursor;nwa_column_limit;nwa_flag];
  nwa_fresh : tensor_disjoint (statement_temps source++public)
    [nwa_cache;nwa_child_cache;nwa_row_cursor;nwa_row_limit;nwa_column_cursor;nwa_column_limit;nwa_flag]=true;
  nwa_typed : tensor_subset
    [nwa_cache;nwa_child_cache;nwa_row_cursor;nwa_row_limit;nwa_column_cursor;nwa_column_limit;nwa_flag]
    (multi_tensor_integer_names pool)=true
}.
Definition nwa_private source public pool (a : word_nested_store_allocation source public pool) :=
  [nwa_cache a;nwa_child_cache a;nwa_row_cursor a;nwa_row_limit a;
    nwa_column_cursor a;nwa_column_limit a;nwa_flag a].
Definition nwa_controls source public pool (a : word_nested_store_allocation source public pool) :=
  [nwa_row_cursor a;nwa_row_limit a;nwa_column_cursor a;nwa_column_limit a;nwa_flag a].

Definition allocate_word_nested_store source public pool :
    option (word_nested_store_allocation source public pool).
Proof.
  pose (names:=multi_tensor_fresh_integer_names source public pool).
  destruct (nth_error names 0) as [cache|]; [|exact None].
  destruct (nth_error names 1) as [child_cache|]; [|exact None].
  destruct (nth_error names 2) as [row_cursor|]; [|exact None].
  destruct (nth_error names 3) as [row_limit|]; [|exact None].
  destruct (nth_error names 4) as [column_cursor|]; [|exact None].
  destruct (nth_error names 5) as [column_limit|]; [|exact None].
  destruct (nth_error names 6) as [flag|]; [|exact None].
  destruct (tensor_unique [cache;child_cache;row_cursor;row_limit;column_cursor;column_limit;flag])
    eqn:UNIQUE; [|exact None].
  destruct (tensor_disjoint (statement_temps source++public)
    [cache;child_cache;row_cursor;row_limit;column_cursor;column_limit;flag]) eqn:FRESH; [|exact None].
  destruct (tensor_subset [cache;child_cache;row_cursor;row_limit;column_cursor;column_limit;flag]
    (multi_tensor_integer_names pool)) eqn:TYPED; [|exact None].
  refine (Some {|nwa_cache:=cache;nwa_child_cache:=child_cache;nwa_row_cursor:=row_cursor;
    nwa_row_limit:=row_limit;nwa_column_cursor:=column_cursor;nwa_column_limit:=column_limit;
    nwa_flag:=flag;nwa_fresh:=FRESH;nwa_typed:=TYPED|}).
  apply tensor_unique_sound; exact UNIQUE.
Defined.

Theorem nwa_allocated_int32 source public pool (a : word_nested_store_allocation source public pool) id :
  In id (nwa_private a) -> In (id,type_int32s) pool.
Proof.
  intro MEMBER; apply multi_tensor_integer_names_member.
  eapply tensor_subset_sound; [exact (nwa_typed a)|exact MEMBER].
Qed.
Theorem nwa_private_fresh source public pool (a : word_nested_store_allocation source public pool) id :
  In id (nwa_private a) -> ~In id (statement_temps source++public).
Proof.
  intros PRIVATE MEMBER; eapply tensor_disjoint_sound;
    [exact (nwa_fresh a)|exact MEMBER|exact PRIVATE].
Qed.
Lemma nwa_controls_unique source public pool (a : word_nested_store_allocation source public pool) :
  NoDup (nwa_controls a).
Proof.
  pose proof (nwa_unique a) as UNIQUE; inversion UNIQUE; subst.
  match goal with H:NoDup (_::_) |- _ => inversion H; subst end; assumption.
Qed.
Lemma nwa_caches_distinct source public pool (a : word_nested_store_allocation source public pool) :
  nwa_cache a<>nwa_child_cache a.
Proof.
  pose proof (nwa_unique a) as UNIQUE; inversion UNIQUE; subst.
  intro SAME; subst; match goal with H:~In _ (_::_) |- _ => apply H; cbn; auto end.
Qed.
Definition nwa_candidate_pool source public pool (a : word_nested_store_allocation source public pool) :=
  filter (fun declaration=>negb (tensor_member (fst declaration) (nwa_private a))) pool.
Theorem nwa_candidate_pool_private source public pool (a : word_nested_store_allocation source public pool) id ty :
  In (id,ty) (nwa_candidate_pool a) -> ~In id (nwa_private a).
Proof.
  unfold nwa_candidate_pool; intro MEMBER; apply filter_In in MEMBER as [_ CHECK].
  intro BAD; apply tensor_member_true in BAD.
  change (negb (tensor_member id (nwa_private a))=true) in CHECK.
  rewrite BAD in CHECK; discriminate.
Qed.

Definition nws_cached d public pool (a : word_nested_store_allocation (nws_source d) public pool) :=
  nested_cached_source (nws_row d) (nwa_cache a) (nws_column d) (nwa_child_cache a) (nws_body d).
Definition nws_scan_live d public pool (a : word_nested_store_allocation (nws_source d) public pool) :=
  nwa_cache a::nwa_child_cache a::statement_temps (nws_source d)++public.
Definition nws_stable d public pool (a : word_nested_store_allocation (nws_source d) public pool) :=
  filter (fun id=>negb (tensor_member id [nws_row d;nws_column d])) (nws_scan_live a).
Definition nws_rename d public pool (a : word_nested_store_allocation (nws_source d) public pool) id :=
  if peq id (nws_row d) then nwa_row_cursor a else
    if peq id (nws_column d) then nwa_column_cursor a else id.

Lemma nws_rename_row d public pool (a : word_nested_store_allocation (nws_source d) public pool) :
  nws_rename a (nws_row d)=nwa_row_cursor a.
Proof. unfold nws_rename; destruct (peq (nws_row d) (nws_row d)); congruence. Qed.
Lemma nws_rename_column d public pool (a : word_nested_store_allocation (nws_source d) public pool) :
  nws_row d<>nws_column d -> nws_rename a (nws_column d)=nwa_column_cursor a.
Proof. intro DISTINCT; unfold nws_rename; repeat destruct (peq _ _); congruence. Qed.

Lemma nws_stable_live d public pool (a : word_nested_store_allocation (nws_source d) public pool) :
  incl (nws_stable a) (nws_scan_live a).
Proof. intros id MEMBER; apply filter_In in MEMBER; exact (proj1 MEMBER). Qed.
Lemma nws_coordinate_private d public pool (a : word_nested_store_allocation (nws_source d) public pool) id :
  In id [nws_row d;nws_column d] -> ~In id (nws_stable a).
Proof.
  intros COORD MEMBER; apply filter_In in MEMBER as [_ CHECK].
  apply tensor_member_true in COORD; rewrite COORD in CHECK; discriminate.
Qed.
Lemma nws_rename_stable d public pool (a : word_nested_store_allocation (nws_source d) public pool) id :
  In id (nws_stable a) -> nws_rename a id=id.
Proof.
  intro MEMBER; unfold nws_rename.
  destruct (peq id (nws_row d)) as [SAME|];
    [subst id; exfalso; apply (@nws_coordinate_private d public pool a (nws_row d)); [cbn; auto|exact MEMBER]|].
  destruct (peq id (nws_column d)) as [SAME|];
    [subst id; exfalso; apply (@nws_coordinate_private d public pool a (nws_column d)); [cbn; auto|exact MEMBER]|reflexivity].
Qed.
Lemma nws_public_live d public pool (a : word_nested_store_allocation (nws_source d) public pool) :
  incl public (nws_scan_live a).
Proof. intros id MEMBER; unfold nws_scan_live; apply in_cons, in_cons; apply in_or_app; right; exact MEMBER. Qed.
Lemma nws_original_scope d public pool (a : word_nested_store_allocation (nws_source d) public pool) :
  statement_scope (nws_scan_live a) (nws_source d).
Proof. intros id MEMBER; unfold nws_scan_live; apply in_cons, in_cons; apply in_or_app; left; exact MEMBER. Qed.

(** Internal static evidence.  Each field is generated by a decidable check,
    allocation, or finite-scope construction. *)
Record word_nested_store_static d public pool
    (a : word_nested_store_allocation (nws_source d) public pool)
    (checked : checked_word_store_body (nws_body d)) := WordNestedStoreStatic {
  nwst_coordinates : nws_row d<>nws_column d;
  nwst_members : forall id, In id [nws_pointer d;nws_child_pointer d;nwa_cache a;nwa_child_cache a] ->
    In id (nws_stable a);
  nwst_controls : forall id, In id (nwa_controls a) -> ~In id (nws_scan_live a);
  nwst_site_pointers : forall site, In site (wsbody_sites checked) -> In (wss_pointer site) (nws_stable a);
  nwst_site_indices : forall site, In site (wsbody_sites checked) ->
    expression_scope (nws_row d::nws_column d::nws_stable a) (wss_index site);
  nwst_cached_scope : statement_scope (nws_scan_live a) (nws_cached a);
  nwst_progress : signed_expression_region_progress_supported (nws_source d)=true
}.

Definition check_word_nested_store_static d public pool
    (a : word_nested_store_allocation (nws_source d) public pool)
    (checked : checked_word_store_body (nws_body d)) : option (word_nested_store_static a checked).
Proof.
  destruct (peq (nws_row d) (nws_column d)) as [|DISTINCT]; [exact None|].
  destruct (tensor_subset [nws_pointer d;nws_child_pointer d;nwa_cache a;nwa_child_cache a]
    (nws_stable a)) eqn:MEMBERS; [|exact None].
  destruct (tensor_disjoint (nwa_controls a) (nws_scan_live a)) eqn:CONTROLS; [|exact None].
  destruct (forallb (fun site=>tensor_member (wss_pointer site) (nws_stable a)) (wsbody_sites checked))
    eqn:POINTERS; [|exact None].
  destruct (forallb (fun site=>tensor_subset (expression_temps (wss_index site))
    (nws_row d::nws_column d::nws_stable a)) (wsbody_sites checked)) eqn:INDICES; [|exact None].
  destruct (tensor_subset (statement_temps (nws_cached a)) (nws_scan_live a)) eqn:SCOPE; [|exact None].
  destruct (signed_expression_region_progress_supported (nws_source d)) eqn:PROGRESS; [|exact None].
  refine (Some {|nwst_coordinates:=DISTINCT;nwst_progress:=PROGRESS|}).
  - apply tensor_subset_sound; exact MEMBERS.
  - apply tensor_disjoint_sound; exact CONTROLS.
  - intros site MEMBER; apply tensor_member_true.
    apply forallb_forall with (x:=site) in POINTERS; assumption.
  - intros site MEMBER id READ.
    apply forallb_forall with (x:=site) in INDICES; [|exact MEMBER].
    eapply tensor_subset_sound; [exact INDICES|exact READ].
  - intros id READ; eapply tensor_subset_sound; [exact SCOPE|exact READ].
Defined.

Record word_nested_store_package source public pool := WordNestedStorePackage {
  nwsp_description : word_nested_store_description;
  nwsp_source : source=nws_source nwsp_description;
  nwsp_allocation : word_nested_store_allocation (nws_source nwsp_description) public pool;
  nwsp_body : checked_word_store_body (nws_body nwsp_description);
  nwsp_static : word_nested_store_static nwsp_allocation nwsp_body
}.
Definition check_word_nested_store_source source public pool (d : word_nested_store_description) :
    option (word_nested_store_package source public pool).
Proof.
  destruct (statement_eq source (nws_source d)) as [SOURCE|]; [|exact None].
  destruct (allocate_word_nested_store (nws_source d) public pool) as [allocation|]; [|exact None].
  destruct (check_word_store_body (nws_body d)) as [body|]; [|exact None].
  destruct (check_word_nested_store_static allocation body) as [STATIC|]; [|exact None].
  exact (Some (@WordNestedStorePackage source public pool d SOURCE allocation body STATIC)).
Defined.

Definition nwsp_rewrite source public pool (package : word_nested_store_package source public pool) :=
  let d:=nwsp_description package in let a:=nwsp_allocation package in
  word_store_nested_rewrite_code (nws_row d) (nwa_cache a) (nws_pointer d) (nws_delta d)
    (nws_column d) (nwa_child_cache a) (nws_child_pointer d) (nws_child_delta d)
    (nwa_row_cursor a) (nwa_row_limit a) (nwa_column_cursor a) (nwa_column_limit a) (nwa_flag a)
    (nws_rename a) (wsbody_sites (nwsp_body package)) (nws_body d).

Theorem nwsp_original_progress source public pool (package : word_nested_store_package source public pool) :
  exists MODEL : region_progress source, True.
Proof.
  rewrite (nwsp_source package); apply signed_expression_region_progress_supported_sound.
  exact (nwst_progress (nwsp_static package)).
Qed.

Theorem nwsp_rewrite_execution source public pool (package : word_nested_store_package source public pool)
    fe ge locals temps memory source_after final :
  exec_stmt fe ge locals temps memory source E0 source_after final Out_normal ->
  exists after, exec_stmt fe ge locals temps memory (nwsp_rewrite package) E0 after final Out_normal /\
    temp_agree public source_after after.
Proof.
  intro SOURCE; rewrite (nwsp_source package) in SOURCE.
  pose (d:=nwsp_description package); pose (a:=nwsp_allocation package).
  pose (checked:=nwsp_body package); pose (STATIC:=nwsp_static package).
  pose proof (nwst_coordinates STATIC) as DISTINCT.
  change (exec_stmt fe ge locals temps memory (nws_source d) E0 source_after final Out_normal) in SOURCE.
  unfold nwsp_rewrite; fold d a checked.
  eapply word_store_nested_rewrite_execution with (checked:=checked) (stable:=nws_stable a)
    (live:=nws_scan_live a) (public:=public).
  all: try solve [exact SOURCE|apply nws_stable_live|apply nws_public_live|apply nws_original_scope|
    apply nwa_controls_unique|apply nws_rename_stable|exact (nwst_coordinates STATIC)|
    exact (nwst_cached_scope STATIC)|exact (nwst_site_pointers STATIC)|exact (nwst_site_indices STATIC)|
    exact (nwst_controls STATIC)|apply nwa_caches_distinct].
  all: try solve [apply (nwst_members STATIC); cbn; tauto].
  all: try solve [eapply nws_coordinate_private; cbn; tauto].
  all: try solve [eapply (@nwa_private_fresh (nws_source d) public pool a);
    unfold nwa_private; cbn; tauto].
  all: try solve [exact (@nws_rename_row d public pool a)|
    exact (@nws_rename_column d public pool a DISTINCT)].
  all: match goal with |- ?G => idtac "PENDING_FACTORY" G end.
Qed.

(** The model proposer sees the actual cached AST with its allocated names.
    Its return value is metadata, checked by the existing recursive factory.
    Constructing this package performs no eager runtime parameter reads. *)
Record word_nested_store_polyhedral_package source public pool := WordNestedStorePolyhedralPackage {
  nwspp_header : word_nested_store_package source public pool;
  nwspp_model : multi_tensor_region_package (nws_cached (nwsp_allocation nwspp_header))
}.
Definition check_word_nested_store_polyhedral_source source public pool (d : word_nested_store_description)
    (describe_cached : statement -> option multi_tensor_region_description) :
    option (word_nested_store_polyhedral_package source public pool).
Proof.
  destruct (check_word_nested_store_source source public pool d) as [header|]; [|exact None].
  destruct (describe_cached (nws_cached (nwsp_allocation header))) as [description|]; [|exact None].
  destruct (check_multi_tensor_region_source (nws_cached (nwsp_allocation header)) description) as [model|];
    [|exact None].
  exact (Some (@WordNestedStorePolyhedralPackage source public pool header model)).
Defined.

Print Assumptions allocate_word_nested_store.
Print Assumptions nwa_allocated_int32.
Print Assumptions nwa_private_fresh.
Print Assumptions nwa_controls_unique.
Print Assumptions nwa_caches_distinct.
Print Assumptions nwa_candidate_pool_private.
Print Assumptions nws_rename_row.
Print Assumptions nws_rename_column.
Print Assumptions nws_stable_live.
Print Assumptions nws_coordinate_private.
Print Assumptions nws_rename_stable.
Print Assumptions nws_public_live.
Print Assumptions nws_original_scope.
Print Assumptions check_word_nested_store_static.
Print Assumptions check_word_nested_store_source.
Print Assumptions nwsp_original_progress.
Print Assumptions nwsp_rewrite_execution.
Print Assumptions check_word_nested_store_polyhedral_source.
