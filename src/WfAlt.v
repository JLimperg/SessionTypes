Require Import Contractive ContractiveFacts Env Free FreeFacts Msg Shape Sty
  Tac Var Wf.


Create HintDb wf' discriminated.


Inductive Ok : Env -> Sty -> Prop :=
| Ok_end :
    forall xs, Ok xs unit
| Ok_send :
    forall xs msg ty,
    Checked xs ty ->
    Ok xs (send msg ty)
| Ok_recv :
    forall xs msg ty,
    Checked xs ty ->
    Ok xs (recv msg ty)
| Ok_ichoice :
    forall xs ty1 ty2,
    Checked xs ty1 ->
    Checked xs ty2 ->
    Ok xs (ichoice ty1 ty2)
| Ok_echoice :
    forall xs ty1 ty2,
    Checked xs ty1 ->
    Checked xs ty2 ->
    Ok xs (echoice ty1 ty2)
| Ok_mu :
    forall x xs ty,
    Ok (env_add x xs) ty ->
    Ok xs (mu x ty)
with
  Checked : Env -> Sty -> Prop :=
  | Checked_var :
      forall x xs,
      env_mem x xs ->
      Checked xs (var x)
  | Checked_Ok :
      forall xs ty,
      Ok xs ty ->
      Checked xs ty
.
Hint Constructors Ok : wf'.
Hint Constructors Checked : wf'.

Scheme Ok_ind_mut := Induction for Ok Sort Prop
with Checked_ind_mut := Induction for Checked Sort Prop.

Definition Wf' S := Ok env_empty S.


Lemma Ok_inv :
  forall S S' XS,
  StySubSimple S S' ->
  Ok XS S' ->
  Checked XS S.
Proof. introv Hsub Hok. inverts Hok; inverts Hsub; auto. Qed.


Hint Extern 2 (Checked _ ?S) =>
  match goal with
  | H : Ok _ _ |- _ =>
      solve [eapply (Ok_inv S) in H; [eassumption | constructor]]
  end
: wf'.


Lemma Checked_inv :
  forall S S' XS,
  StySubSimple S S' ->
  Checked XS S' ->
  Checked XS S.
Proof. introv Hsub Hch. inverts Hsub; inverts2 Hch; assumption. Qed.


Hint Extern 2 (Checked _ ?S) =>
  match goal with
  | H : Checked _ _ |- _ =>
      solve [eapply (Checked_inv S) in H; [eassumption | constructor]]
  end
: wf'.


Lemma Ok_Checked_Contractive :
  forall S,
  (forall XS, Ok XS S -> Contractive S) /\
  (forall XS, Checked XS S -> Contractive S).
Proof.
  induction S; split; introv H; try (decompose_and IHS); constructor;
    eauto with wf'; inverts1 H.
  - eauto.
  - inverts H; autodiscriminate.
  - inverts H; eauto.
  - inverts2 H; autodiscriminate.
Qed.


Lemma Ok_Contractive :
  forall S XS,
  Ok XS S ->
  Contractive S.
Proof. introv H. pose proof (Ok_Checked_Contractive S). jauto. Qed.

Lemma Checked_Contractive :
  forall S XS,
  Checked XS S ->
  Contractive S.
Proof. introv H. pose proof (Ok_Checked_Contractive S). jauto. Qed.

Lemma Wf'_Contractive :
  forall S,
  Wf' S ->
  Contractive S.
Proof. unfold Wf'. intros. eapply Ok_Contractive. eassumption. Qed.


Lemma Ok_Checked_Free :
  forall S X XS,
  Ok XS S \/ Checked XS S ->
  ~ env_mem X XS ->
  ~ Free X S.
Proof.
  induction S; introv HOk Henv; decompose_or_auto; eauto 6 with wf' free.
  - introv H; inverts1 H. eapply IHS with (XS := env_add v XS);
    eauto using env_mem_add with wf' free.
    * inverts1 HOk. eauto.
  - introv H; inverts1 H. eapply IHS with (XS := env_add v XS);
    eauto using env_mem_add with wf' free.
    * inverts2 HOk. eauto.
  - inversion HOk.
  - inverts1 HOk.
    * introv H. inverts H. auto.
    * inversion HOk.
Qed.


Lemma Ok_Free :
  forall S X XS,
  Ok XS S ->
  ~ env_mem X XS ->
  ~ Free X S.
Proof. intros. eapply Ok_Checked_Free; eauto. Qed.


Lemma Checked_Free :
  forall S X XS,
  Checked XS S ->
  ~ env_mem X XS ->
  ~ Free X S.
Proof. intros. eapply Ok_Checked_Free; eauto. Qed.


Lemma Wf'_closed : forall S, Wf' S -> Closed S.
Proof.
  unfold Wf'. unfold Closed. intros S Hwf X. eapply Ok_Free;
    eauto.
  - apply env_mem_empty.
Qed.


Lemma Wf'_Wf :
  forall S,
  Wf' S -> Wf S.
Proof.
  introv H. unfolds. split;
  auto using Wf'_Contractive, Wf'_closed.
Qed.


Lemma Free_contractive_Checked_Ok :
  forall S XS,
  (forall X, Free X S -> env_mem X XS) ->
  Contractive S ->
  Checked XS S /\ (shape S <> varS -> Ok XS S).
Proof.
  intros S XS. gen XS. induction S; introv H; (
    let finish :=
      constructor; first [apply IHS | apply IHS1 | apply IHS2];
      auto with free contractive
    in
    split;
    [ try solve [constructor; finish]
    | introv Hsh; try solve [finish]
    ]
  ).
  - constructor. constructor. apply IHS; [|auto with contractive..].
    * introv Hfree. destruct (eq_Var_dec X v) as [Heq | Hneq].
      + subst. apply env_add_mem'.
      + apply env_add_mem. auto with free.
  - constructor. apply IHS; [|auto with contractive..].
    * introv Hfree. destruct (eq_Var_dec X v) as [Heq | Hneq].
      + subst. apply env_add_mem'.
      + apply env_add_mem. auto with free.
  - constructor. auto with free.
  - exfalso. apply Hsh. reflexivity.
Qed.


Lemma Wf_Wf' :
  forall S,
  Wf S -> Wf' S.
Proof.
  introv H. inversion H as [Hcontractive Hclosed].
  apply Free_contractive_Checked_Ok.
  - introv Hfree. contradict Hfree. auto with free.
  - assumption.
  - destruct S; simpl; try autodiscriminate; auto with free.
Qed.


Lemma Wf'_iff_Wf : 
  forall S,
  Wf S <-> Wf' S.
Proof.
  intros. split; [apply Wf_Wf' | apply Wf'_Wf].
Qed.
