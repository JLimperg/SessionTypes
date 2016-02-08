Require Import Env Free FreeFacts SessionTypes SessionTypesInd Shape ShapeFacts
  Substitution Tac Var Wellformed.

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


Lemma cs_det :
  forall S XS T1 T2,
  ok XS S ->
  cs S T1 ->
  cs S T2 ->
  T1 = T2.
Proof.
  induction S using (well_founded_ind lt_Sty_mu_prefix_wf).
  introv Hok H1 H2; inverts H1; inverts H2; auto with subst.
    pose proof Hok. inverts1 Hok.
    eapply H with (y := subst X (mu X S0) S0);
      eauto using subst_preserves_wellformedness, lt_Sty_mu_prefix_subst.
Qed.


Lemma cs_shape :
  forall S S' XS,
  ok XS S ->
  cs S S' ->
  shape S' = unitS \/
  shape S' = sendS \/
  shape S' = recvS \/
  shape S' = ichoiceS \/
  shape S' = echoiceS.
Proof.
  induction S using (well_founded_ind lt_Sty_mu_prefix_wf); introv Hok Hcs;
    inverts Hcs; auto.
  - pose proof Hok. inverts1 Hok. eapply H with (y := subst X (mu X S0) S0);
      eauto using subst_preserves_wellformedness, lt_Sty_mu_prefix_subst.
  - inverts Hok.
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
