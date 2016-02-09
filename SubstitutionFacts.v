Require Import Env Equivalence Free FreeFacts SessionTypes SessionTypesInd
  Shape ShapeFacts Substitution Tac Var Wellformed.

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


Lemma cs_ex :
  forall S XS,
  ok XS S ->
  exists csS,
  cs S csS.
Proof.
  induction S using (well_founded_ind lt_Sty_mu_prefix_wf). destruct S;
    eauto with subst; introv Hok.
  - assert (exists csS', cs (subst v (mu v S) S) csS').
      pose proof Hok. inverts Hok.
      eapply H;
        eauto using subst_preserves_wellformedness, lt_Sty_mu_prefix_subst.
    eauto with subst.
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


Lemma cs_mu_absurd :
  forall S XS X S',
  ok XS S ->
  cs S (mu X S') ->
  False.
Proof.
  introv Hok Hcs. eapply cs_shape in Hcs; eauto.
  decompose_or_auto; discriminate.
Qed.


(* TODO beautify. Perhaps use that sequiv is symmetric. *)
Lemma cs_preserves_sequiv :
  forall S S' csS csS' XS XS',
  ok XS S ->
  ok XS' S' ->
  cs S csS ->
  cs S' csS' ->
  sequiv S S' ->
  sequiv csS csS'.
Proof.
  refine (
    Sty_ind_mu_prefix2
      (fun S S' => forall csS csS' XS XS',
        ok XS S ->
        ok XS' S' ->
        cs S csS ->
        cs S' csS' ->
        sequiv S S' ->
        sequiv csS csS')
      _
  ).
  introv IH Hok Hok' Hcs Hcs' Heq. inverts2 Heq; inverts1 Hcs; inverts1 Hcs';
    auto; solve
    [ pose proof Hok; inverts1 Hok; eapply IH with (T := (subst X (mu X S0) S0));
        eauto using lt_Sty_mu_prefix_subst, subst_preserves_wellformedness
        with subst
    | pose proof Hok'; inverts Hok'; eapply IH with (T' := (subst X (mu X S'0) S'0));
        eauto using lt_Sty_mu_prefix_subst, subst_preserves_wellformedness
        with subst
    ].
Qed.


Lemma uncs_preserves_sequiv_l :
  forall S S' csS csS' XS,
  ok XS S ->
  cs S csS ->
  cs S' csS' ->
  sequiv csS csS' ->
  sequiv S csS'.
Proof.
  induction S using (well_founded_ind lt_Sty_mu_prefix_wf);
    introv Hok Hcs Hcs' Heq; inverts1 Hcs; auto.
  - do 2 constructor. pose proof Hok. inverts Hok.
    eapply H with
      (y := subst X (mu X S0) S0)
      (S':= S')
      (csS := csS);
      eauto using lt_Sty_mu_prefix_subst, subst_preserves_wellformedness.
Qed.


(* TODO Avoid duplication between this and uncs_preserves_sequiv_l. *)
Lemma uncs_preserves_sequiv_r :
  forall S S' csS csS' XS',
  ok XS' S' ->
  cs S csS ->
  cs S' csS' ->
  sequiv csS csS' ->
  sequiv csS S'.
Proof.
  induction S' using (well_founded_ind lt_Sty_mu_prefix_wf);
    introv Hok' Hcs Hcs' Heq; inverts1 Hcs'; auto.
  - do 2 constructor. pose proof Hok'. inverts Hok'.
    eapply H with
      (y := subst X (mu X S0) S0)
      (csS' := csS');
      eauto using lt_Sty_mu_prefix_subst, subst_preserves_wellformedness.
Qed.


Lemma cs_preserves_sequiv_l :
  forall S S' csS XS XS',
  ok XS S ->
  ok XS' S' ->
  cs S csS ->
  sequiv S S' ->
  sequiv csS S'.
Proof.
  intros. pose proof (cs_ex S') as HcsS'. edestruct HcsS'; eauto.
  eapply uncs_preserves_sequiv_r with (S := S); eauto.
  eapply cs_preserves_sequiv with (S := S) (S' := S'); eauto.
Qed.


Lemma cs_preserves_sequiv_r :
  forall S S' csS' XS XS',
  ok XS S ->
  ok XS' S' ->
  cs S' csS' ->
  sequiv S S' ->
  sequiv S csS'.
Proof.
  intros. pose proof (cs_ex S) as HcsS. edestruct HcsS; eauto.
  eapply uncs_preserves_sequiv_l with (S' := S'); eauto.
  eapply cs_preserves_sequiv with (S := S) (S' := S'); eauto.
Qed.


Lemma cs_preserves_wellformedness :
  forall S csS,
  cs S csS ->
  wellformed S ->
  wellformed csS.
Proof.
  induction S using (well_founded_ind lt_Sty_mu_prefix_wf);
    introv Hcs Hwf; inverts Hcs; auto.
  - pose proof Hwf. inverts Hwf. eapply H with (y := subst X (mu X S0) S0);
      [eauto using lt_Sty_mu_prefix_subst|auto|].
      apply subst_preserves_wellformedness; auto.
Qed.
