Require Import CS Contractive ContractiveFacts Equiv NonEquiv Shape ShapeFacts
  Sty StyInd Subst SubstFacts Symmetry Tac TL TLFacts Wf.


Lemma cs_shape :
  forall S,
  Contractive S ->
  shape (cs S) = unitS \/
  shape (cs S) = sendS \/
  shape (cs S) = recvS \/
  shape (cs S) = ichoiceS \/
  shape (cs S) = echoiceS \/
  shape (cs S) = varS.
Proof.
  induction S using (well_founded_ind lt_Sty_mu_prefix_wf); intros;
    destruct S; cs_simpl; eauto 10 with contractive subst.
Qed.


Lemma cs_mu_absurd :
  forall S X S',
  Contractive S ->
  cs S <> mu X S'.
Proof.
  introv Hok H. eapply cs_shape in Hok. decompose_or_auto; shape_inv_auto;
  discriminate.
Qed.

Hint Extern 1 =>
  let step S X S' := (exfalso; apply (cs_mu_absurd S X S')) in
  match goal with
  | H : cs ?S = mu ?X ?S' |- _ => step S X S'
  | H : mu ?X ?S' = cs ?S |- _ => symmetry in H; step S X S'
  end
: subst.


Lemma cs_preserves_sequiv :
  forall S S',
  Contractive S ->
  Contractive S' ->
  sequiv S S' ->
  sequiv (cs S) (cs S').
Proof.
  apply (
    Sty_ind_mu_prefix2 (fun S S' =>
      Contractive S ->
      Contractive S' ->
      sequiv S S' ->
      sequiv (cs S) (cs S'))
  ).
  introv IH Hcontr Hcontr' Heq. inverts2 Heq; cs_simpl;
    eauto 10 with contractive subst.
Qed.


Lemma uncs_preserves_sequiv_l :
  forall S S',
  Contractive S ->
  sequiv (cs S) S' ->
  sequiv S S'.
Proof.
  induction S using (well_founded_ind lt_Sty_mu_prefix_wf);
    intros; destruct S; cs_simpl; eauto 10 with contractive subst.
Qed.


Lemma uncs_preserves_sequiv_r :
  forall S S',
  Contractive S' ->
  sequiv S (cs S') ->
  sequiv S S'.
Proof.
  introv Hcontr H. apply sequiv_symmetric. apply sequiv_symmetric in H.
  apply uncs_preserves_sequiv_l; assumption.
Qed.


Lemma uncs_preserves_sequiv :
  forall S S',
  Contractive S ->
  Contractive S' ->
  sequiv (cs S) (cs S') ->
  sequiv S S'.
Proof.
  intros. eapply uncs_preserves_sequiv_l; eauto.
  eapply uncs_preserves_sequiv_r; eauto.
Qed.


Lemma cs_preserves_sequiv_l :
  forall S S',
  Contractive S ->
  Contractive S' ->
  sequiv S S' ->
  sequiv (cs S) S'.
Proof.
  intros. eapply uncs_preserves_sequiv_r; eauto.
  eapply cs_preserves_sequiv; eauto.
Qed.


Lemma cs_preserves_sequiv_r :
  forall S S',
  Contractive S ->
  Contractive S' ->
  sequiv S S' ->
  sequiv S (cs S').
Proof.
  intros. eapply uncs_preserves_sequiv_l; eauto.
  eapply cs_preserves_sequiv; eauto.
Qed.


Lemma cs_preserves_not_sequiv :
  forall S S',
  Contractive S ->
  Contractive S' ->
  ~ sequiv S S' ->
  ~ sequiv (cs S) (cs S').
Proof.
  introv Hok Hok' H contra. apply H. eapply uncs_preserves_sequiv; eauto.
Qed.


Lemma uncs_preserves_not_sequiv :
  forall S S',
  Contractive S ->
  Contractive S' ->
  ~ sequiv (cs S) (cs S') ->
  ~ sequiv S S'.
Proof.
  introv Hok Hok' H contra. apply H. eapply cs_preserves_sequiv; eauto.
Qed.


Lemma cs_preserves_nsequiv :
  forall S S',
  Contractive S ->
  Contractive S' ->
  nsequiv S S' ->
  nsequiv (cs S) (cs S').
Proof.
  apply (Sty_ind_mu_prefix2 (fun S S' =>
    Contractive S ->
    Contractive S' ->
    nsequiv S S' ->
    nsequiv (cs S) (cs S')
  )).
  introv IH Hok Hok' Hneq. inverts Hneq; try cs_simpl;
    eauto 10 with contractive subst nsequiv.
  - destruct S; destruct S'; cs_simpl; auto with nsequiv; false.
Qed.


Lemma uncs_preserves_nsequiv :
  forall S S',
  Contractive S ->
  Contractive S' ->
  nsequiv (cs S) (cs S') ->
  nsequiv S S'.
Proof.
  apply (Sty_ind_mu_prefix2 (fun S S' =>
    Contractive S ->
    Contractive S' ->
    nsequiv (cs S) (cs S') ->
    nsequiv S S'
  )).
  introv IH Hok Hok' Hneq. destruct S; destruct S'; solve
    [ cs_simpl; auto
    | constructor; apply IH; eauto with contractive subst; cs_simpl;
        auto with nsequiv
    ].
Qed.


Lemma cs_preserves_Contractive :
  forall S,
  Contractive S ->
  Contractive (cs S).
Proof.
  induction S using (well_founded_ind lt_Sty_mu_prefix_wf); introv Hcontr;
    destruct S; cs_simpl; auto with contractive subst.
Qed.
Hint Resolve cs_preserves_Contractive : subst.


Lemma cs_preserves_wellformed :
  forall S,
  wellformed S ->
  wellformed (cs S).
Proof.
  unfold wellformed. induction S using (well_founded_ind lt_Sty_mu_prefix_wf);
    introv Hwf; destruct S; cs_simpl; eauto 10 with contractive free subst.
Qed.
Hint Resolve cs_preserves_wellformed : subst.


Lemma tl_eq :
  forall eta S S' c c',
  S = S' ->
  tl eta S c = tl eta S' c'.
Proof.
  introv Heq. gen c c'. rewrite Heq. apply tl_contractive_irrelevant.
Qed.


Lemma cs_preserves_tl :
  forall S eta c c',
  wellformed S ->
  tl eta S c = tl eta (cs S) c'.
Proof.
  intros S eta. induction S using (well_founded_ind lt_Sty_mu_prefix_wf);
    introv Hwf; destruct S; try solve [apply tl_eq; cs_simpl; reflexivity];
    unfold wellformed in *; norm_hyp_auto.
  - erewrite tl_mu_subst. erewrite H with (y := subst v (mu v S) S).
    apply tl_eq. cs_simpl. reflexivity.
    all: auto 10 with contractive subst free.
Unshelve.
  all: auto with contractive subst.
Qed.