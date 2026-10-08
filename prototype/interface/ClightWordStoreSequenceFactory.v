(** Static recognition produces the language obligations for a store sequence. *)
From Stdlib Require Import List Bool.
From compcert.cfrontend Require Import Clight Ctypes Cop.
From Guard Require Import ClightStraightLine ClightTempFrame ClightLoopSyntax ClightRegionProgress.
From GuardInterface Require Import ClightWordArithmeticTransport ClightWordStoreSequence.
Import ListNotations.
Set Implicit Arguments.

Definition check_word_store_site code : option word_store_site :=
  match code with
  | Sassign (Ederef (Ebinop Oadd (Etempvar pointer pointer_type) index address_type) lhs_type) rhs =>
      if type_eq pointer_type (Tpointer type_int32s noattr) then
        if type_eq address_type (Tpointer type_int32s noattr) then
          if type_eq lhs_type type_int32s then
            if word_arithmetic_check index then Some (WordStoreSite pointer index rhs) else None
          else None
        else None
      else None
  | _ => None
  end.
Lemma check_word_store_site_sound code site :
  check_word_store_site code = Some site ->
  code = word_store_site_code site /\ word_arithmetic (wss_index site).
Proof.
  destruct code; cbn; try discriminate; destruct e; try discriminate;
    destruct e; try discriminate; destruct b; try discriminate; destruct e1; try discriminate.
  repeat match goal with |- context [type_eq ?first ?second] =>
    destruct (type_eq first second); [subst|discriminate] end.
  destruct (word_arithmetic_check e2) eqn:WORD; try discriminate.
  intro CHECK; inversion CHECK; subst; split; [reflexivity|apply word_arithmetic_check_sound; exact WORD].
Qed.

Fixpoint check_word_store_sites statements : option (list word_store_site) :=
  match statements with
  | [] => Some []
  | code :: rest => match check_word_store_site code, check_word_store_sites rest with
    | Some site, Some sites => Some (site :: sites)
    | _, _ => None
    end
  end.
Theorem check_word_store_sites_sound statements sites :
  check_word_store_sites statements = Some sites ->
  statements = map word_store_site_code sites /\
  Forall (fun site => word_arithmetic (wss_index site)) sites.
Proof.
  revert sites; induction statements as [|code rest IH]; intros sites CHECK; cbn in CHECK.
  - inversion CHECK; split; [reflexivity|constructor].
  - destruct (check_word_store_site code) as [site|] eqn:HEAD; try discriminate.
    destruct (check_word_store_sites rest) as [tail|] eqn:TAIL; try discriminate.
    inversion CHECK; subst sites.
    destruct (@check_word_store_site_sound code site HEAD) as [SOURCE WORD].
    destruct (IH _ eq_refl) as [REST WORDS]; split; [cbn; congruence|constructor; assumption].
Qed.

Lemma word_store_sites_body_normal body sites :
  flatten_region body = map word_store_site_code sites -> normal_statement body = true.
Proof.
  intro BODY; apply flatten_normal_certificate; rewrite BODY; apply Forall_map,Forall_forall;
    intros site MEMBER; reflexivity.
Qed.
Lemma word_store_sites_body_quiet body sites :
  flatten_region body = map word_store_site_code sites -> quiet_statement body = true.
Proof.
  intro BODY; apply flatten_quiet_certificate; rewrite BODY; apply Forall_map,Forall_forall;
    intros site MEMBER; reflexivity.
Qed.
Lemma word_store_sites_body_writes body sites :
  flatten_region body = map word_store_site_code sites -> writes_only [] body.
Proof.
  intro BODY; apply flatten_writes_certificate; rewrite BODY; apply Forall_map,Forall_forall;
    intros site MEMBER; constructor.
Qed.

Record checked_word_store_body body := CheckedWordStoreBody {
  wsbody_sites : list word_store_site;
  wsbody_flatten : flatten_region body = map word_store_site_code wsbody_sites;
  wsbody_words : Forall (fun site => word_arithmetic (wss_index site)) wsbody_sites;
  wsbody_normal : normal_statement body = true;
  wsbody_quiet : quiet_statement body = true;
  wsbody_writes : writes_only [] body
}.
Arguments wsbody_sites {body} _.
Definition check_word_store_body body : option (checked_word_store_body body).
Proof.
  destruct (check_word_store_sites (flatten_region body)) as [sites|] eqn:CHECK; [|exact None].
  destruct (@check_word_store_sites_sound (flatten_region body) sites CHECK) as [SOURCE WORDS].
  refine (Some (@CheckedWordStoreBody body sites SOURCE WORDS _ _ _)).
  - eapply word_store_sites_body_normal; exact SOURCE.
  - eapply word_store_sites_body_quiet; exact SOURCE.
  - eapply word_store_sites_body_writes; exact SOURCE.
Defined.

Print Assumptions check_word_store_site_sound.
Print Assumptions check_word_store_sites_sound.
Print Assumptions word_store_sites_body_normal.
Print Assumptions word_store_sites_body_quiet.
Print Assumptions word_store_sites_body_writes.
Print Assumptions check_word_store_body.
