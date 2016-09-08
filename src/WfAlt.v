Require Import Contractive ContractiveFacts Env Free FreeFacts Msg Shape Sty
  Tac Var Wf.

Inductive ok : Env -> Sty -> Prop :=
| ok_end :
    forall xs, ok xs unit
| ok_send :
    forall xs msg ty,
    checked xs ty ->
    ok xs (send msg ty)
| ok_recv :
    forall xs msg ty,
    checked xs ty ->
    ok xs (recv msg ty)
| ok_ichoice :
    forall xs ty1 ty2,
    checked xs ty1 ->
    checked xs ty2 ->
    ok xs (ichoice ty1 ty2)
| ok_echoice :
    forall xs ty1 ty2,
    checked xs ty1 ->
    checked xs ty2 ->
    ok xs (echoice ty1 ty2)
| ok_mu :
    forall x xs ty,
    ok (env_add x xs) ty ->
    ok xs (mu x ty)
with
  checked : Env -> Sty -> Prop :=
  | checked_var :
      forall x xs,
      env_mem x xs ->
      checked xs (var x)
  | checked_ok :
      forall xs ty,
      ok xs ty ->
      checked xs ty
.
Hint Constructors ok : wf.
Hint Constructors checked : wf.

Scheme ok_ind_mut := Induction for ok Sort Prop
with checked_ind_mut := Induction for checked Sort Prop.

Definition wellformed' S := ok env_empty S.


Lemma ok_checked_Contractive :
  forall S,
  (forall XS, ok XS S -> Contractive S) /\
  (forall XS, checked XS S -> Contractive S).
Proof.
  induction S; split; introv H; try (decompose_and IHS); constructor; inverts1 H;
    repeat match goal with
    | H : checked _ _ |- _ => inverts H
    end; try solve
    [constructor | eauto 3 | inverts H; eauto].
  - inverts H; simpl; autodiscriminate.
  - inverts2 H; simpl; autodiscriminate.
Qed.

Lemma ok_Contractive :
  forall S XS,
  ok XS S ->
  Contractive S.
Proof. introv H. pose proof (ok_checked_Contractive S). jauto. Qed.

Lemma checked_Contractive :
  forall S XS,
  checked XS S ->
  Contractive S.
Proof. introv H. pose proof (ok_checked_Contractive S). jauto. Qed.

Lemma wellformed'_Contractive :
  forall S,
  wellformed' S ->
  Contractive S.
Proof. unfold wellformed'. intros. eauto using ok_Contractive. Qed.


Lemma ok_checked_free :
  forall S X XS,
  ok XS S \/ checked XS S ->
  ~ env_mem X XS ->
  ~ Free X S.
Proof.
  induction S; introv Hok Henv; decompose_or_auto;
    auto with free;
    match goal with
    | |- context [var _]     => idtac
    | Hok : ok _ _      |- _ => inverts1 Hok
    | Hok : checked _ _ |- _ => inverts2 Hok
    end; eauto 6 with free.

    introv H; inverts H; eapply IHS; eauto with free;
    introv H; apply env_mem_add in H; auto.

    introv H; inverts H; eapply IHS; eauto with free;
    introv H; apply env_mem_add in H; auto.

    inverts1 Hok.

    inverts1 Hok.
      introv H. inverts1 H. auto.
      inverts Hok.
Qed.


Lemma ok_free :
  forall S X XS,
  ok XS S ->
  ~ env_mem X XS ->
  ~ Free X S.
Proof. intros. eapply ok_checked_free; eauto. Qed.


Lemma checked_free :
  forall S X XS,
  checked XS S ->
  ~ env_mem X XS ->
  ~ Free X S.
Proof. intros. eapply ok_checked_free; eauto. Qed.


Lemma wellformed'_closed : forall S, wellformed' S -> Closed S.
Proof.
  unfold wellformed'. unfold Closed. intros S Hwf X. eapply ok_free;
    eauto with env.
Qed.


Lemma wellformed'_wellformed :
  forall S,
  wellformed' S -> wellformed S.
Proof.
  introv H. unfolds. split;
  auto using wellformed'_Contractive, wellformed'_closed.
Qed.


Lemma free_contractive_checked_ok :
  forall S XS,
  (forall X, Free X S -> env_mem X XS) ->
  Contractive S ->
  checked XS S /\ (shape S <> varS -> ok XS S).
Proof.
  intros S XS. gen XS. induction S; introv H; (
    let finish :=
      constructor; first [apply IHS | apply IHS1 | apply IHS2];
      auto with free contractive in
    split;
    [ try solve [constructor; finish]
    | introv Hsh; try solve [finish]
    ]
  ).
  - constructor. constructor. apply IHS; [|auto with contractive..].
    * introv Hfree. destruct (eq_var_dec X v) as [Heq | Hneq].
      + subst. apply env_add_mem'.
      + apply env_add_mem. auto with free.
  - constructor. apply IHS; [|auto with contractive..].
    * introv Hfree. destruct (eq_var_dec X v) as [Heq | Hneq].
      + subst. apply env_add_mem'.
      + apply env_add_mem. auto with free.
  - constructor. auto with free.
  - exfalso. apply Hsh. reflexivity.
Qed.


Lemma wellformed_wellformed' :
  forall S,
  wellformed S -> wellformed' S.
Proof.
  introv H. inversion H as [Hcontractive Hclosed].
  apply free_contractive_checked_ok.
  - introv Hfree. contradict Hfree. auto with free.
  - assumption.
  - destruct S; simpl; try autodiscriminate; auto with free.
Qed.


Lemma wellformed'_iff_wellformed : 
  forall S,
  wellformed S <-> wellformed' S.
Proof.
  intros. split.
  - apply wellformed_wellformed'.
  - apply wellformed'_wellformed.
Qed.