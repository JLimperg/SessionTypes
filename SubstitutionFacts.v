Require Import Env Free FreeFacts SessionTypes Shape ShapeFacts Substitution
  Tac Var Wellformed.

Create HintDb subst discriminated.

Lemma subst_preserves_shape :
  forall S X r,
  shape S <> varS ->
  shape (subst X r S) = shape S.
Proof.
  induction S; introv Hvarsh; simpl in *; auto;
    destruct (beq_var X v); auto.
    exfalso; auto.
Qed.


Lemma subst_neutral :
  forall S X R,
  ~ Free X S ->
  subst X R S = S.
Proof.
  induction S; introv Hfree; simpl; auto; try solve
    [ rewrite IHS; auto with free
    | rewrite IHS1; auto with free; rewrite IHS2; auto with free
    ];
    destruct (beq_var X v) eqn:HXeqv; auto.
      rewrite <- beq_var_false_iff in HXeqv. rewrite IHS; auto with free.
      rewrite <- beq_var_true_iff in HXeqv. subst. exfalso; auto with free.
Qed.


Lemma subst_preserves_free :
  forall S X Y R,
  X <> Y ->
  Free X S ->
  Free X (subst Y R S).
Proof.
  induction S; introv Hneq Hfree; simpl; auto with free; try solve
    [inverts1 Hfree; decompose_or Hfree; auto with free].
    destruct (beq_var Y v) eqn:HYeqv; auto with free.
      constructor; auto with free. inverts1 Hfree. auto.
    inverts Hfree. rewrite beq_var_neq; auto with free.
Qed.


(* TODO beautify *)
Lemma free_subst_inversion :
  forall S X Y R,
  Free X (subst Y R S) ->
  Free X R \/ (X <> Y /\ Free X S).
Proof.
  induction S; introv H; simpl in *.
    auto with free.
    inverts1 H. apply IHS in H; destruct H; intuition (auto with free).
    inverts1 H. apply IHS in H; destruct H; intuition (auto with free).
    inverts1 H. destruct H; [apply IHS1 in H | apply IHS2 in H]; destruct H; intuition (auto with free).
    inverts1 H. destruct H; [apply IHS1 in H | apply IHS2 in H]; destruct H; intuition (auto with free).
    destruct (beq_var Y v) eqn:HYeqv.
      apply beq_var_true_iff in HYeqv. subst. inversion H. iauto.
      inverts1 H. apply IHS in H. destruct H; intuition (auto with free).
    destruct (beq_var Y v) eqn:HYeqv; [auto|].
      inverts1 H. apply beq_var_false_iff in HYeqv. auto with free.
Qed.


Lemma substall_shape :
  forall XS S,
  ok XS S ->
  shape (substall S) = unitS \/
  shape (substall S) = sendS \/
  shape (substall S) = recvS \/
  shape (substall S) = ichoiceS \/
  shape (substall S) = echoiceS.
Proof.
  introv Hwf. induction Hwf; simpl in *; solve
    [iauto | decompose sum IHHwf; simpl in *; shape_inv_auto; iauto].
Qed.


Lemma substall_preserves_free :
  forall S X,
  Free X S <-> Free X (substall S).
Proof.
  induction S; split; introv H; auto with free.
    simpl. inverts H. rewrite IHS in H3. apply subst_preserves_free; auto.

    simpl in H. apply free_subst_inversion in H; destruct H; [auto|..].
    destruct H as [H H']. apply IHS in H'. auto with free.
Qed.


Lemma subst_nonfree :
  forall S X R,
  ~ Free X R ->
  ~ Free X (subst X R S).
Proof.
  introv HR. destruct (Free_dec S X) as [HS | HS].
    gen S. induction S; introv HS; auto with free.

      introv H. simpl in H. inverts1 H. destruct H;
        [destruct (Free_dec S1 X) | destruct (Free_dec S2 X)]; unfold not in *;
          auto; rewrite subst_neutral in H; auto.

      introv H. simpl in H. inverts1 H. destruct H;
        [destruct (Free_dec S1 X) | destruct (Free_dec S2 X)]; unfold not in *;
          auto; rewrite subst_neutral in H; auto.

      inverts HS. simpl. rewrite beq_var_neq; auto with free.

      inverts HS. simpl. rewrite <- beq_var_refl; auto.

  introv H. rewrite subst_neutral in H; auto with free.
Qed.


Lemma subst_substall_distr_nonfree :
  forall S X R,
  ~ Free X S ->
  subst X R (substall S) = substall (subst X R S).
Proof.
  introv Hfree. rewrite subst_neutral. rewrite subst_neutral; auto.
  introv H. apply substall_preserves_free in H. auto.
Qed.


Lemma shape_subst_substall_1 :
  forall XS X R S,
  ok XS S ->
  shape (subst X R (substall S)) = shape (substall S).
Proof.
  introv Hok. pose proof (substall_shape XS S Hok) as H.
  decompose sum H; clear H; shape_inv_auto; auto.
Qed.


Lemma shape_subst_substall_2 :
  forall S XS X R,
  ok XS R ->
  ok (env_add X XS) S ->
  shape (substall S) = shape (substall (subst X R S)).
Proof.
  induction S; introv HokR HokS; eauto.
    simpl. destruct (beq_var X v) eqn:HXv; simpl.
      inverts1 HokS. erewrite shape_subst_substall_1; eauto.

      inverts1 HokS. erewrite shape_subst_substall_1; [|eauto].
      rewrite shape_subst_substall_1 with (XS := env_add v XS).
        apply IHS with (XS := env_add v XS).
          auto with wf.
          rewrite env_add_assoc; auto.
        apply subst_preserves_wellformedness.
          auto with wf.
          rewrite env_add_assoc; auto.

    inverts HokS.
Qed.
