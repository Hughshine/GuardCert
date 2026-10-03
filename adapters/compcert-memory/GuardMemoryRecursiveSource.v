From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Coqlib Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame ClightLoopSyntax ClightRegionProgress
  ClightFrontendLoopProtocol ClightStraightLine ClightFiniteRegion ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryControlSettle GuardMemorySettledCountedLoop
  GuardMemoryTripleSource GuardMemoryTripleWords GuardMemoryNaryLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A recursive description retains every original body AST.  The shape
    certificate permits frontend sequence association, while checking the
    complete reset, counted loop and leaf at every depth. *)
Inductive memory_source_nest :=
| MemorySourceLeaf (code : statement)
| MemorySourceAxis (iterator bound : ident) (body : statement) (child : memory_source_nest).
Definition memory_nest_source nest := match nest with
  | MemorySourceLeaf code => code
  | MemorySourceAxis iterator bound body _ => frontend_counted_loop iterator bound body end.
Fixpoint memory_nest_leaf nest := match nest with
  | MemorySourceLeaf code => code | MemorySourceAxis _ _ _ child => memory_nest_leaf child end.
Fixpoint memory_nest_iterators nest := match nest with
  | MemorySourceLeaf _ => [] | MemorySourceAxis iterator _ _ child => iterator::memory_nest_iterators child end.
Fixpoint memory_nest_bounds nest := match nest with
  | MemorySourceLeaf _ => [] | MemorySourceAxis _ bound _ child => bound::memory_nest_bounds child end.
Definition memory_nest_child_shape body child := match child with
  | MemorySourceLeaf code => body = code
  | MemorySourceAxis iterator _ _ _ =>
      flatten_region body = [rectangle_reset iterator;memory_nest_source child] end.
Fixpoint memory_nest_shapes nest := match nest with
  | MemorySourceLeaf _ => True
  | MemorySourceAxis _ _ body child => memory_nest_child_shape body child /\ memory_nest_shapes child end.
Definition memory_nest_fresh nest := NoDup (memory_nest_iterators nest) /\
  (forall identifier, In identifier (memory_nest_iterators nest) -> ~ In identifier (memory_nest_bounds nest)).
Definition memory_nest_bindings (identifiers : list ident) (values : list Z) (temps : temp_env) :=
  Forall2 (fun identifier value => temps ! identifier = Some (Vint (Int.repr value))) identifiers values.
Definition memory_nest_assignments nest counts :=
  combine (memory_nest_iterators nest) (map (fun count => Vint (Int.repr (Z.of_nat count))) counts).
Definition memory_nest_exit nest counts temps := memory_settle_controls (memory_nest_assignments nest counts) temps.

Lemma memory_nest_bindings_frame identifiers values first second :
  temp_agree identifiers first second -> memory_nest_bindings identifiers values first ->
  memory_nest_bindings identifiers values second.
Proof.
  intros FRAME BINDINGS; revert FRAME; induction BINDINGS; intro FRAME; constructor.
  - rewrite FRAME by (cbn; auto); exact H.
  - apply IHBINDINGS; intros identifier MEMBER; apply FRAME; cbn; auto.
Qed.
Lemma memory_nest_bindings_append first second a b temps :
  memory_nest_bindings first a temps -> memory_nest_bindings second b temps ->
  memory_nest_bindings (first++second) (a++b) temps.
Proof. intros A B; apply Forall2_app; assumption. Qed.
Lemma memory_nest_bindings_set identifiers values temps identifier word :
  ~ In identifier identifiers -> memory_nest_bindings identifiers values temps ->
  memory_nest_bindings identifiers values (PTree.set identifier word temps).
Proof. intros FRESH WORDS; eapply memory_nest_bindings_frame; [apply temp_agree_set; exact FRESH|exact WORDS]. Qed.
Lemma memory_nest_bindings_frame_from identifiers values stable first second :
  (forall identifier, In identifier identifiers -> In identifier stable) ->
  temp_agree stable first second -> memory_nest_bindings identifiers values first ->
  memory_nest_bindings identifiers values second.
Proof. intros SUB FRAME WORDS; eapply memory_nest_bindings_frame; [eapply temp_agree_weaken; eauto|exact WORDS]. Qed.

Lemma memory_nest_fresh_child iterator bound body child :
  memory_nest_fresh (MemorySourceAxis iterator bound body child) ->
  memory_nest_fresh child /\ ~ In iterator (memory_nest_iterators child) /\
  ~ In bound (memory_nest_iterators child) /\ iterator <> bound.
Proof.
  intros [UNIQUE DISJOINT]; cbn in *; inversion UNIQUE; subst.
  repeat split; auto.
  - intros identifier MEMBER BAD; apply (DISJOINT identifier ltac:(cbn; auto)); cbn; auto.
  - intro BAD; apply (DISJOINT bound ltac:(cbn; auto)); cbn; auto.
  - intro SAME; subst; apply (DISJOINT bound ltac:(cbn; auto)); cbn; auto.
Qed.
Lemma memory_nest_lengths nest : length (memory_nest_iterators nest) = length (memory_nest_bounds nest).
Proof. induction nest; cbn; congruence. Qed.
Lemma memory_nest_assignment_keys nest counts : length counts = length (memory_nest_iterators nest) ->
  map fst (memory_nest_assignments nest counts) = memory_nest_iterators nest.
Proof.
  intro LENGTH; unfold memory_nest_assignments.
  assert (KEYS : forall (identifiers : list ident) (values : list val),
    length values = length identifiers -> map fst (combine identifiers values) = identifiers).
  { intro identifiers; induction identifiers; intros [|value values] SAME; cbn in *; try discriminate;
      [reflexivity|f_equal; apply IHidentifiers; lia]. }
  apply KEYS; rewrite length_map; exact LENGTH.
Qed.

Lemma memory_nest_source_quiet nest : memory_nest_shapes nest -> quiet_statement (memory_nest_leaf nest) = true ->
  quiet_statement (memory_nest_source nest) = true.
Proof.
  induction nest as [code|iterator bound body child IH]; cbn [memory_nest_shapes memory_nest_leaf];
    intros SHAPES QUIET; [exact QUIET|].
  change (quiet_statement (frontend_counted_loop iterator bound body) = true).
  destruct SHAPES as [SHAPE SHAPES]; apply memory_frontend_loop_quiet.
  specialize (IH SHAPES QUIET); destruct child; cbn in SHAPE; [subst; exact IH|].
  eapply memory_reset_child_quiet; eassumption.
Qed.
Lemma memory_nest_source_writes nest : memory_nest_shapes nest -> writes_only [] (memory_nest_leaf nest) ->
  writes_only (memory_nest_iterators nest) (memory_nest_source nest).
Proof.
  induction nest as [code|iterator bound body child IH]; cbn [memory_nest_shapes memory_nest_leaf];
    intros SHAPES WRITES; [exact WRITES|].
  change (writes_only (iterator::memory_nest_iterators child) (frontend_counted_loop iterator bound body)).
  destruct SHAPES as [SHAPE SHAPES]; apply memory_frontend_loop_writes; [cbn; auto|].
  assert (BODY : writes_only (memory_nest_iterators child) body).
  { specialize (IH SHAPES WRITES); destruct child; cbn in SHAPE; [subst; exact IH|].
    eapply memory_reset_child_writes; [exact SHAPE|cbn; auto|exact IH]. }
  eapply writes_only_weaken; [|exact BODY]; cbn; auto.
Qed.
Lemma memory_nest_body_writes iterator bound body child :
  memory_nest_shapes (MemorySourceAxis iterator bound body child) -> writes_only [] (memory_nest_leaf child) ->
  writes_only (memory_nest_iterators child) body.
Proof.
  cbn; intros [SHAPE SHAPES] WRITES; pose proof (memory_nest_source_writes child SHAPES WRITES) as SOURCE.
  destruct child; cbn in SHAPE; [subst; exact SOURCE|].
  eapply memory_reset_child_writes; [exact SHAPE|cbn; auto|exact SOURCE].
Qed.
Lemma memory_nest_body_normal iterator bound body child :
  memory_nest_shapes (MemorySourceAxis iterator bound body child) ->
  normal_statement (memory_nest_leaf child) = true -> quiet_statement (memory_nest_leaf child) = true ->
  normal_statement body = true.
Proof.
  cbn; intros [SHAPE SHAPES] NORMAL QUIET.
  pose proof (memory_nest_source_quiet child SHAPES QUIET) as SOURCE.
  destruct child; cbn in SHAPE; [subst; exact NORMAL|].
  eapply memory_reset_child_normal; [exact SHAPE|].
  exact SOURCE.
Qed.

Print Assumptions memory_nest_source_writes.
Print Assumptions memory_nest_body_normal.

Lemma memory_settle_controls_overwrite assignments temps identifier value :
  In identifier (map fst assignments) ->
  memory_settle_controls assignments (PTree.set identifier value temps) = memory_settle_controls assignments temps.
Proof.
  intro ASSIGNED; apply PTree.extensionality; intro key.
  destruct (in_dec peq key (map fst assignments)) as [MEMBER|FRESH].
  - apply memory_settle_controls_lookup; exact MEMBER.
  - rewrite !memory_settle_controls_frame by exact FRESH.
    rewrite PTree.gso; [reflexivity|intro SAME; subst; contradiction].
Qed.
Lemma memory_nest_exit_reset nest counts temps identifier :
  length counts = length (memory_nest_iterators nest) -> In identifier (memory_nest_iterators nest) ->
  memory_nest_exit nest counts (PTree.set identifier (Vint Int.zero) temps) = memory_nest_exit nest counts temps.
Proof.
  intros LENGTH MEMBER; unfold memory_nest_exit; apply memory_settle_controls_overwrite.
  rewrite memory_nest_assignment_keys by exact LENGTH; exact MEMBER.
Qed.
Definition memory_nest_initial nest temps := match nest with
  | MemorySourceLeaf _ => True
  | MemorySourceAxis iterator _ _ _ => temps ! iterator = Some (Vint Int.zero) end.
Definition memory_nest_child_temps child temps := match child with
  | MemorySourceLeaf _ => temps
  | MemorySourceAxis iterator _ _ _ => PTree.set iterator (Vint Int.zero) temps end.
Lemma memory_nest_child_decode fe ge locals body child temps memory after final :
  memory_nest_child_shape body child ->
  exec_stmt fe ge locals temps memory body E0 after final Out_normal ->
  exec_stmt fe ge locals (memory_nest_child_temps child temps) memory (memory_nest_source child) E0 after final Out_normal.
Proof.
  destruct child; cbn; intros SHAPE RUN; [subst; exact RUN|].
  eapply memory_reset_child_decode; eassumption.
Qed.
Lemma memory_nest_child_initial child temps : memory_nest_initial child (memory_nest_child_temps child temps).
Proof. destruct child; cbn; [exact I|apply PTree.gss]. Qed.
Lemma memory_nest_child_frame child temps identifiers :
  (forall identifier, In identifier (memory_nest_iterators child) -> ~ In identifier identifiers) ->
  temp_agree identifiers temps (memory_nest_child_temps child temps).
Proof. destruct child; cbn; intro FRESH; [apply temp_agree_refl|apply temp_agree_set; apply FRESH; cbn; auto]. Qed.
Lemma memory_nest_child_exit child counts temps : length counts = length (memory_nest_iterators child) ->
  memory_nest_exit child counts (memory_nest_child_temps child temps) = memory_nest_exit child counts temps.
Proof. destruct child; cbn [memory_nest_child_temps]; intro LENGTH; [reflexivity|].
  apply memory_nest_exit_reset; [exact LENGTH|cbn; auto]. Qed.
