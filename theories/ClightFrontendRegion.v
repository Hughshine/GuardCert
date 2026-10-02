From Stdlib Require Import Bool List ZArith Arith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import SilentRegionProtocol CompCertMemoryEquivalence AbstractGuard SemanticFacts ClightGuard ClightCondition
  ClightSyntaxEquality ClightRegionRule ClightRegionRewrite ClightPureExpr
  ClightCountedLoop ClightCountedProtocol ClightRegionProgress ClightProgressClassifier ClightZeroTrip.
From Guard Require Import ClightFrontendLoopProtocol.
Set Implicit Arguments.

Lemma frontend_loop_quiet iterator bound body : memory_body body = true ->
  quiet_statement (frontend_counted_loop iterator bound body) = true.
Proof.
  intro BODY. unfold frontend_counted_loop, counter_increment; cbn [quiet_statement].
  rewrite (finite_statement_quiet body (memory_body_finite body BODY)); reflexivity.
Qed.

Definition frontend_progress iterator bound (DISTINCT : iterator <> bound) body
  (BODY : memory_body body = true) : region_progress (frontend_counted_loop iterator bound body).
Proof.
  refine {| progress_label_free := quiet_statement_label_free _
      (frontend_loop_quiet iterator bound body BODY);
    progress_protocol := fun temps ge fn outside locals =>
      @frontend_region_protocol (adapter_entry temps) ge locals fn outside iterator bound DISTINCT body BODY;
    progress_entry := fun temps ge fn outside locals =>
      @frontend_region_entry (adapter_entry temps) ge locals fn outside iterator bound DISTINCT body BODY |}.
  - intros; reflexivity.
  - intros temps ge fn outside locals c; destruct c; cbn [cursor_state frontend_region_protocol
      frontend_cursor_state]; repeat eexists; reflexivity.
  - intros temps ge tge GLOBALS locals le m le' m' RUN.
    eapply quiet_execution_preserved; [exact GLOBALS | exact RUN |].
    apply frontend_loop_quiet; exact BODY.
Defined.

Definition propose_frontend_shape (source : statement) : option (ident * ident * statement) :=
  match source with
  | Sloop (Ssequence (Ssequence Sskip (Sifthenelse
      (Ebinop Olt (Etempvar iterator _) (Etempvar bound _) _) Sskip Sbreak)) body) _ =>
      Some (iterator, bound, body)
  | _ => None
  end.

Definition frontend_counted_supported (source : statement) : bool :=
  match propose_frontend_shape source with
  | Some (iterator, bound, body) =>
      if statement_eq source (frontend_counted_loop iterator bound body)
      then if peq iterator bound then false else memory_body body
      else false
  | None => false
  end.

Lemma frontend_counted_supported_sound source : frontend_counted_supported source = true ->
  exists MODEL : region_progress source, True.
Proof.
  unfold frontend_counted_supported.
  destruct (propose_frontend_shape source) as [[[iterator bound] body]|]; try discriminate.
  destruct (statement_eq source (frontend_counted_loop iterator bound body)) as [EQ|NE]; try discriminate.
  destruct (peq iterator bound) as [SAME|DISTINCT]; try discriminate.
  intro BODY; subst source. exists (@frontend_progress iterator bound DISTINCT body BODY); exact I.
Qed.

Definition frontend_progress_supported source := progress_supported source || frontend_counted_supported source.
Theorem frontend_progress_supported_sound source : frontend_progress_supported source = true ->
  exists MODEL : region_progress source, True.
Proof.
  unfold frontend_progress_supported; rewrite orb_true_iff; intros [CORE|FRONTEND].
  - apply progress_supported_sound; exact CORE.
  - apply frontend_counted_supported_sound; exact FRONTEND.
Qed.

Lemma skip_prefix_exec fe ge locals le m code trace le' m' outcome :
  exec_stmt fe ge locals le m (Ssequence Sskip code) trace le' m' outcome ->
  exec_stmt fe ge locals le m code trace le' m' outcome.
Proof.
  intro RUN; inversion RUN; subst;
    match goal with SKIP : exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ => inversion SKIP; subst end;
    simpl in *; try contradiction; assumption.
Qed.

Lemma frontend_entry_test fe ge locals le m iterator bound body le' m' :
  exec_stmt fe ge locals le m (frontend_counted_loop iterator bound body) E0 le' m' Out_normal ->
  exists flag, expression_test (counter_condition iterator bound) (Entry ge locals le m) flag.
Proof.
  intro RUN; inversion RUN; subst.
  all: match goal with HEADER : exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ |- _ =>
    inversion HEADER; subst;
    match goal with PRE : exec_stmt _ _ _ _ _ (Ssequence Sskip _) _ _ _ _ |- _ =>
      apply skip_prefix_exec in PRE; inversion PRE; subst;
      eexists; eexists; split; eassumption
    end
  end.
Qed.

Lemma frontend_false_header fe ge locals le m iterator bound body trace le' m' outcome :
  exec_stmt fe ge locals le m
    (Ssequence (Ssequence Sskip (Sifthenelse (counter_condition iterator bound) Sskip Sbreak)) body)
    trace le' m' outcome ->
  expression_test (counter_condition iterator bound) (Entry ge locals le m) false ->
  trace = E0 /\ le' = le /\ m' = m /\ outcome = Out_break.
Proof.
  intros RUN TEST; inversion RUN; subst.
  all: match goal with PRE : exec_stmt _ _ _ _ _ (Ssequence Sskip _) _ _ _ _ |- _ =>
    apply skip_prefix_exec in PRE;
    match type of PRE with exec_stmt _ _ _ _ _ _ ?tr ?leC ?mC ?outC =>
      pose proof (@false_header_result fe ge locals le m iterator bound Sskip tr leC mC outC PRE TEST)
        as [TRACE [TEMPS [MEMORY OUTCOME]]]
    end
  end.
  all: subst; try discriminate; repeat split; reflexivity.
Qed.

Lemma frontend_zero_trip_result fe ge locals le m iterator bound body le' m' :
  exec_stmt fe ge locals le m (frontend_counted_loop iterator bound body) E0 le' m' Out_normal ->
  expression_test (counter_condition iterator bound) (Entry ge locals le m) false ->
  le' = le /\ m' = m.
Proof.
  intros RUN TEST. inversion RUN; subst.
  all: match goal with HEADER : exec_stmt _ _ _ _ _ (Ssequence _ _) ?tr ?leH ?mH ?outH |- _ =>
    pose proof (@frontend_false_header fe ge locals le m iterator bound body tr leH mH outH HEADER TEST)
      as [TRACE [TEMPS [MEMORY OUTCOME]]]
  end.
  all: subst; try solve [split; reflexivity].
  all: match goal with BAD : out_normal_or_continue Out_break |- _ => inversion BAD end.
Qed.

Definition frontend_zero_trip_rule iterator bound body :
  encoded_region_rule (frontend_counted_loop iterator bound body) Sskip.
Proof.
  refine {| region_rule_atoms := unit;
    region_rule_domain := counter_domain iterator bound;
    region_rule_dimension := zero_trip_dimension iterator bound;
    region_rule_primitives := zero_trip_primitives iterator bound;
    region_rule_formula := Fact tt |}.
  - intros temps p locals le m le' m' RUN.
    destruct (@frontend_entry_test (adapter_entry temps) (globalenv p) locals le m
      iterator bound body le' m' RUN) as [flag TEST].
    eapply counter_test_domain; exact TEST.
  - intros temps p locals le m le' m' RUN EMPTY.
    change (expression_test (counter_condition iterator bound) (Entry (globalenv p) locals le m) false)
      in EMPTY.
    destruct (@frontend_zero_trip_result (adapter_entry temps) (globalenv p) locals le m
      iterator bound body le' m' RUN EMPTY) as [TEMPS MEMORY]; subst.
    exists m; split; [constructor | apply memory_equivalent_refl].
Defined.

Definition select_frontend_zero_trip (source : statement) : option statement :=
  match propose_frontend_shape source with
  | Some (iterator, bound, body) =>
      if statement_eq source (frontend_counted_loop iterator bound body)
      then Some (generated_region (frontend_zero_trip_rule iterator bound body)) else None
  | None => None
  end.

Theorem select_frontend_zero_trip_sound source target : select_frontend_zero_trip source = Some target ->
  region_contract source target.
Proof.
  unfold select_frontend_zero_trip; destruct (propose_frontend_shape source) as [[[iterator bound] body]|];
    try discriminate.
  destruct (statement_eq source (frontend_counted_loop iterator bound body)) as [EQ|NE]; try discriminate.
  intro TARGET; inversion TARGET; subst; apply encoded_region_rule_sound.
Qed.

Print Assumptions frontend_progress_supported_sound.
Print Assumptions select_frontend_zero_trip_sound.

Definition select_loop_zero_trip source :=
  match select_frontend_zero_trip source with
  | Some target => Some target
  | None => select_zero_trip source
  end.

Theorem select_loop_zero_trip_sound source target : select_loop_zero_trip source = Some target ->
  region_contract source target.
Proof.
  unfold select_loop_zero_trip; destruct (select_frontend_zero_trip source) as [selected|] eqn:FRONTEND.
  - intro TARGET; inversion TARGET; subst; eapply select_frontend_zero_trip_sound; exact FRONTEND.
  - apply select_zero_trip_sound.
Qed.
