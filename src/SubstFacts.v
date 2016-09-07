Require Import Contractive Env Free FreeFacts Sty StyInd Shape ShapeFacts
  Subst Tac Var Wf.

Hint Resolve subst_preserves_wellformedness : subst.

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
  forall T X S,
  shape T <> varS ->
  Contractive T ->
  Contractive S ->
  Contractive (subst X T S).
Proof.
  introv HshapeT HcontrT HcontrS. induction HcontrS; simpl; auto with contract.
  - destruct (beq_var X X0); [auto with contract|]. constructor; [auto|].
    * destruct S; simpl; auto with contract.
      + destruct (beq_var X v); auto.
  - destruct (beq_var X X0); auto with contract.
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
  - destruct (beq_var Y v) eqn:HYeqv; auto with free.
  - inverts Hfree. rewrite beq_var_neq; auto with free.
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


Lemma Closed_shortcut_mu :
  forall S X,
  Closed (mu X S) ->
  Closed (subst X (mu X S) S).
Proof.
  unfold Closed; introv H; intro Y; specialize H with Y; contradict H;
  apply free_subst_inversion in H; auto with free.
Qed.

Hint Extern 2 (Closed (subst ?X (mu ?X ?S) ?S)) =>
  match goal with
  | H : Closed (mu X S) |- _ =>
      apply Closed_shortcut_mu in H; assumption
  end
: free.


Lemma subst_ok_mu :
  forall S X XS,
  ok XS (mu X S) ->
  ok XS (subst X (mu X S) S).
Proof.
  introv Hok. eapply subst_preserves_wellformedness; [|inverts Hok]; auto.
Qed.
Hint Resolve subst_ok_mu : subst.


Lemma lt_Sty_mu_prefix_subst :
  forall S X R,
  ok_some S ->
  lt_Sty_mu_prefix (subst X R S) (mu X S).
Proof.
  intros S X R; induction S; introv Hok; try solve [constructor].
  - simpl. destruct (beq_var X v); [constructor|].
      decompose_ex Hok. inverts Hok. unfold lt_Sty_mu_prefix in *.
      unfold Wf_nat.ltof in *. simpl in *. apply Lt.lt_n_S. eauto.
  - inverts2 Hok.
Qed.


Lemma lt_Sty_mu_prefix_subst_mu :
  forall S XS X Y,
  ok XS (mu Y S) ->
  lt_Sty_mu_prefix (subst X (mu X S) S) (mu X S).
Proof. introv H. apply lt_Sty_mu_prefix_subst. inverts H. eauto. Qed.

Hint Extern 1 (lt_Sty_mu_prefix (subst ?X (mu ?X ?S) ?S) (mu ?X ?S)) =>
  match goal with
  | H : ok ?XS1 (mu ?Y1 S) |- _ =>
      apply lt_Sty_mu_prefix_subst_mu with (XS := XS1) (Y := Y1);
      assumption
  end
: subst.
