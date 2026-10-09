From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryLongControl GuardMemoryLongRangeCapture GuardMemoryLongPositiveCapture
  GuardMemoryLongHeaderLicense GuardMemoryDoubleRectangularNestData.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Record rectangular_capture_step := RectangularCaptureStep {
  rectangular_capture_header : ident;
  rectangular_capture_cache : ident;
  rectangular_capture_limit : Z
}.
Fixpoint rectangular_capture_code steps flag : statement :=
  match steps with
  | []=>memory_capture_flag flag true
  | step::steps=>Ssequence
      (memory_long_positive_capture (rectangular_capture_header step) (rectangular_capture_cache step)
        flag (rectangular_capture_limit step))
      (Sifthenelse (Etempvar flag memory_signed_int_type) (rectangular_capture_code steps flag) Sskip)
  end.
Definition rectangular_capture_step_temps step flag word temps :=
  memory_long_positive_captured temps (rectangular_capture_cache step) flag word (rectangular_capture_limit step).
Definition rectangular_capture_step_accept step word := memory_long_positive_accept word (rectangular_capture_limit step).

Inductive rectangular_capture_receipt ge locals memory flag :
  list rectangular_capture_step -> temp_env -> temp_env -> bool -> Prop :=
| rectangular_capture_done temps : rectangular_capture_receipt ge locals memory flag [] temps
    (PTree.set flag (Vint Int.one) temps) true
| rectangular_capture_refused step steps temps bound_block word :
    double_global_binding ge locals (rectangular_capture_header step) bound_block ->
    Mem.load Mint64 memory bound_block 0=Some (Vlong word) ->
    0<=rectangular_capture_limit step<=Int.max_signed -> rectangular_capture_step_accept step word=false ->
    rectangular_capture_receipt ge locals memory flag (step::steps) temps
      (rectangular_capture_step_temps step flag word temps) false
| rectangular_capture_next step steps temps after accepted bound_block word :
    double_global_binding ge locals (rectangular_capture_header step) bound_block ->
    Mem.load Mint64 memory bound_block 0=Some (Vlong word) ->
    0<=rectangular_capture_limit step<=Int.max_signed -> rectangular_capture_step_accept step word=true ->
    rectangular_capture_receipt ge locals memory flag steps (rectangular_capture_step_temps step flag word temps) after accepted ->
    rectangular_capture_receipt ge locals memory flag (step::steps) temps after accepted.

Lemma rectangular_capture_flag_test ge locals temps memory flag (accepted : bool) :
  temps ! flag=Some (Vint (if accepted then Int.one else Int.zero)) ->
  expression_test (Etempvar flag memory_signed_int_type) (Entry ge locals temps memory) accepted.
Proof.
  intro VALUE; exists (Vint (if accepted then Int.one else Int.zero)); split;
    [constructor; exact VALUE|destruct accepted; reflexivity].
Qed.
Theorem rectangular_capture_receipt_flag ge locals memory flag steps temps after accepted :
  rectangular_capture_receipt ge locals memory flag steps temps after accepted ->
  after ! flag=Some (Vint (if accepted then Int.one else Int.zero)).
Proof.
  intro RECEIPT; induction RECEIPT; [apply PTree.gss| |exact IHRECEIPT].
  unfold rectangular_capture_step_temps; rewrite memory_long_positive_captured_flag.
  change (Some (Vint (if rectangular_capture_step_accept step word then Int.one else Int.zero))=Some (Vint Int.zero)).
  rewrite H2; reflexivity.
Qed.
Theorem rectangular_capture_receipt_execution fe ge locals memory flag steps temps after accepted :
  rectangular_capture_receipt ge locals memory flag steps temps after accepted ->
  exec_stmt fe ge locals temps memory (rectangular_capture_code steps flag) E0 after memory Out_normal.
Proof.
  intro RECEIPT; induction RECEIPT; cbn [rectangular_capture_code].
  - apply memory_capture_flag_execution.
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
    + eapply memory_long_positive_capture_execution; eassumption.
    + pose proof (@memory_long_positive_captured_flag temps (rectangular_capture_cache step) flag word
        (rectangular_capture_limit step)) as VALUE.
      change ((rectangular_capture_step_temps step flag word temps) ! flag=
        Some (Vint (if rectangular_capture_step_accept step word then Int.one else Int.zero))) in VALUE.
      rewrite H2 in VALUE.
      destruct (@rectangular_capture_flag_test ge locals _ memory flag false VALUE) as [value [EVAL BOOL]].
      eapply exec_Sifthenelse with (b:=false); [exact EVAL|exact BOOL|constructor].
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
    + eapply memory_long_positive_capture_execution; eassumption.
    + pose proof (@memory_long_positive_captured_flag temps (rectangular_capture_cache step) flag word
        (rectangular_capture_limit step)) as VALUE.
      change ((rectangular_capture_step_temps step flag word temps) ! flag=
        Some (Vint (if rectangular_capture_step_accept step word then Int.one else Int.zero))) in VALUE.
      rewrite H2 in VALUE.
      destruct (@rectangular_capture_flag_test ge locals _ memory flag true VALUE) as [value [EVAL BOOL]].
      eapply exec_Sifthenelse with (b:=true); [exact EVAL|exact BOOL|exact IHRECEIPT].
Qed.
Theorem rectangular_capture_receipt_frame ge locals memory flag steps temps after accepted :
  rectangular_capture_receipt ge locals memory flag steps temps after accepted ->
  forall key, key<>flag -> ~ In key (map rectangular_capture_cache steps) -> after ! key=temps ! key.
Proof.
  intro RECEIPT; induction RECEIPT; intros key FLAG CACHES.
  - apply PTree.gso; congruence.
  - apply memory_long_positive_captured_frame; [intro SAME; subst; apply CACHES; cbn; auto|exact FLAG].
  - rewrite IHRECEIPT by (try exact FLAG; intro MEMBER; apply CACHES; cbn; auto).
    apply memory_long_positive_captured_frame; [intro SAME; subst; apply CACHES; cbn; auto|exact FLAG].
Qed.

(** Construct the check receipt from a defined original execution. The emitted
    code does not run the source. Entering a suffix is used only in this proof. *)
Theorem rectangular_capture_source_licensed axes :
  forall steps flag body fe ge locals original_temps temps memory original_after original_final,
  (exists target rhs, body=Sassign target rhs) ->
  Forall2 (fun axis step => snd axis=rectangular_capture_header step) axes steps ->
  (forall axis, In axis axes -> exists bound_block, double_global_binding ge locals (snd axis) bound_block) ->
  Forall (fun step => 0<=rectangular_capture_limit step<=Int.max_signed) steps ->
  exec_stmt fe ge locals original_temps memory (double_rectangular_nest_code axes body)
    E0 original_after original_final Out_normal ->
  exists after accepted, rectangular_capture_receipt ge locals memory flag steps temps after accepted.
Proof.
  induction axes as [|[iterator header] axes IH]; intros steps flag body fe ge locals original_temps temps memory
    original_after original_final ASSIGNMENT LINK BINDINGS LIMITS SOURCE.
  - inversion LINK; subst steps; do 2 eexists; constructor.
  - inversion LINK as [|axis step axes' steps' HEADER TAIL]; subst axis axes' steps; cbn [snd] in HEADER.
    inversion LIMITS as [|step' rest LIMIT LIMITS']; subst step' rest.
    destruct (@BINDINGS (iterator,header) ltac:(left; reflexivity)) as [bound_block BINDING].
    cbn [snd] in BINDING; cbn [double_rectangular_nest_code] in SOURCE.
    destruct (@memory_global_long_initialized_license fe ge locals original_temps memory iterator header bound_block
      (double_rectangular_nest_code axes body) original_after original_final BINDING
      (@double_rectangular_nest_normal axes body ASSIGNMENT) SOURCE) as [word [LOAD CHILD]].
    destruct (rectangular_capture_step_accept step word) eqn:ACCEPT.
    + assert (POSITIVE : 0<Int64.signed word).
      { unfold rectangular_capture_step_accept in ACCEPT; apply memory_long_positive_accept_spec in ACCEPT; lia. }
      destruct (CHILD POSITIVE) as [child_temps [child_memory CHILD_SOURCE]].
      destruct (@IH steps' flag body fe ge locals (PTree.set iterator (Vlong Int64.zero) original_temps)
        (rectangular_capture_step_temps step flag word temps) memory child_temps child_memory ASSIGNMENT TAIL
        ltac:(intros axis MEMBER; apply BINDINGS; right; exact MEMBER) LIMITS' CHILD_SOURCE)
        as [after [accepted RECEIPT]].
      exists after,accepted; eapply rectangular_capture_next;
        [rewrite <- HEADER; exact BINDING|exact LOAD|exact LIMIT|exact ACCEPT|exact RECEIPT].
    + exists (rectangular_capture_step_temps step flag word temps),false; eapply rectangular_capture_refused;
        [rewrite <- HEADER; exact BINDING|exact LOAD|exact LIMIT|exact ACCEPT].
Qed.

Theorem rectangular_capture_accepted_values ge locals memory flag steps temps after :
  rectangular_capture_receipt ge locals memory flag steps temps after true ->
  NoDup (map rectangular_capture_cache steps) -> ~ In flag (map rectangular_capture_cache steps) ->
  exists parameters, Forall2 (fun step value =>
    after ! (rectangular_capture_cache step)=Some (Vint (Int.repr value)) /\
    1<=value<=rectangular_capture_limit step) steps parameters.
Proof.
  intro RECEIPT; remember true as accepted eqn:TRUE; revert TRUE.
  induction RECEIPT; intros TRUE DISTINCT FLAG; [exists []; constructor|discriminate|].
  subst accepted; inversion DISTINCT as [|cache caches FRESH TAIL]; subst cache caches.
  assert (CHILD_FLAG : ~ In flag (map rectangular_capture_cache steps)) by (intro MEMBER; apply FLAG; right; exact MEMBER).
  destruct (IHRECEIPT eq_refl TAIL CHILD_FLAG) as [parameters VALUES].
  exists (Int64.signed word::parameters); constructor.
  - split.
    + rewrite (@rectangular_capture_receipt_frame ge locals memory flag steps _ after true RECEIPT
        (rectangular_capture_cache step) ltac:(intro SAME; subst; apply FLAG; left; reflexivity) FRESH).
      exact (proj1 (@memory_long_positive_captured_cache temps (rectangular_capture_cache step) flag word
        (rectangular_capture_limit step) ltac:(intro SAME; subst; apply FLAG; left; reflexivity) H1 H2)).
    + unfold rectangular_capture_step_accept in H2; apply memory_long_positive_accept_spec; exact H2.
  - exact VALUES.
Qed.

Print Assumptions rectangular_capture_receipt_flag.
Print Assumptions rectangular_capture_receipt_execution.
Print Assumptions rectangular_capture_receipt_frame.
Print Assumptions rectangular_capture_source_licensed.
Print Assumptions rectangular_capture_accepted_values.
