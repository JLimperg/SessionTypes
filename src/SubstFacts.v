Require Import Contractive ContractiveFacts Env Free FreeFacts Sty StyInd Shape
  ShapeFacts Subst Tac Var Wf.


Lemma subst_preserves_shape :
  forall S X r,
  shape S <> varS ->
  shape (subst X r S) = shape S.
Proof.
  induction S; introv Hvarsh; simpl in *; auto;
    destruct (beq_var X v); auto.
    exfalso; auto.
Qed.


Lemma subst_preserves_Contractive :
  forall S X R,
  Contractive S ->
  Contractive R ->
  shape R <> varS ->
  Contractive (subst X R S).
Proof.
  introv HcontrS HcontrT HshapeT. induction HcontrS; simpl; auto with contractive.
  - destruct (beq_var X X0); [auto with contractive|]. constructor; [auto|].
    * destruct S; simpl; auto with contractive.
      + destruct (beq_var X v); auto.
  - destruct (beq_var X X0); auto with contractive.
Qed.
Hint Resolve subst_preserves_Contractive : subst.


Lemma mu_unfold_preserves_Contractive :
  forall S X,
  Contractive (mu X S) ->
  Contractive (subst X (mu X S) S).
Proof.
  introv H. apply subst_preserves_Contractive; auto with contractive.
  - simpl. autodiscriminate.
Qed.
Hint Resolve mu_unfold_preserves_Contractive : contractive.


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


Lemma subst_preserves_Free :
  forall S X Y R,
  X <> Y ->
  Free X S ->
  Free X (subst Y R S).
Proof.
  induction S; introv Hneq Hfree; simpl; auto with free; try solve
    [inverts1 Hfree; decompose_or Hfree; auto with free].
  - destruct (beq_var Y v) eqn:HYeqv; auto with free.
  - inverts Hfree. rewrite beq_var_neq; auto with free.
Qed.


Lemma subst_Nonfree :
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


(* TODO beautify *)
Lemma Free_subst_inversion :
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


Lemma subst_preserves_Closed :
  forall S X R,
  Closed S ->
  Closed R ->
  Closed (subst X R S).
Proof.
  introv HS HR. unfold Closed in *. introv Hfree.
  apply Free_subst_inversion in Hfree. norm_hyp_auto; [eapply HR | eapply HS];
    eauto.
Qed.
Hint Resolve subst_preserves_Closed : subst.


Lemma subst_preserves_Wf :
  forall S X R,
  Wf S ->
  Wf R ->
  Wf (subst X R S).
Proof.
  unfold Wf. introv HS HR. norm_hyp_auto. split.
  - assert (shape R <> varS) by (
      destruct R; simpl; try autodiscriminate; auto with free).
    auto with subst.
  - auto with subst.
Qed.


Lemma mu_unfold_preserves_Closed :
  forall S X,
  Closed (mu X S) ->
  Closed (subst X (mu X S) S).
Proof.
  unfold Closed; introv H; intro Y; specialize H with Y; contradict H;
  apply Free_subst_inversion in H; auto with free.
Qed.
Hint Resolve mu_unfold_preserves_Closed : free.


Lemma mu_unfold_preserves_Wf :
  forall S X,
  Wf (mu X S) ->
  Wf (subst X (mu X S) S).
Proof. unfold Wf. auto with contractive free. Qed.


Lemma lt_Sty_mu_prefix_subst :
  forall S X R,
  Contractive S ->
  shape S <> varS ->
  lt_Sty_mu_prefix (subst X R S) (mu X S).
Proof.
  intros S X R; induction S; introv Hcontr Hsh; try solve [constructor].
  - simpl. destruct (beq_var X v); [constructor|].
    inverts Hcontr. unfold lt_Sty_mu_prefix in *. unfold Wf_nat.ltof in *.
    simpl in *. apply Lt.lt_n_S. eauto.
  - exfalso; auto.
Qed.


Lemma lt_Sty_mu_prefix_subst_mu :
  forall S X,
  Contractive (mu X S) ->
  lt_Sty_mu_prefix (subst X (mu X S) S) (mu X S).
Proof. intros. apply lt_Sty_mu_prefix_subst; auto with contractive. Qed.
Hint Resolve lt_Sty_mu_prefix_subst_mu : subst.
