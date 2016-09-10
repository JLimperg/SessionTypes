Require Import CompleteSubstitution Contractive Equivalence NonEquivalence
  SessionTypes SessionTypesInd Shape ShapeFacts Substitution SubstitutionFacts
  Tac TraceLanguage TraceLanguageFacts Wellformed.

Lemma cs_shape :
  forall S,
  ok_some S ->
  shape (cs S) = unitS \/
  shape (cs S) = sendS \/
  shape (cs S) = recvS \/
  shape (cs S) = ichoiceS \/
  shape (cs S) = echoiceS.
Proof.
  induction S using (well_founded_ind lt_Sty_mu_prefix_wf); intros;
    destruct S; cs_simpl; eauto with subst wf.
Qed.


Lemma cs_mu_absurd :
  forall S X S',
  ok_some S ->
  cs S = mu X S' ->
  False.
Proof.
  introv Hok H. eapply cs_shape in Hok. decompose_or_auto; shape_inv_auto;
  discriminate.
Qed.

Hint Extern 1 =>
  match goal with
  | H : cs ?S1 = mu ?X1 ?S'1, Hok : ex ?XS1 (ok ?XS1 ?S1) |- _ =>
      solve [ exfalso; exact (cs_mu_absurd S1 X1 S'1 Hok H) ]
  end
: subst.


Lemma cs_preserves_sequiv :
  forall S S',
  ok_some S ->
  ok_some  S' ->
  sequiv S S' ->
  sequiv (cs S) (cs S').
Proof.
  apply (
    Sty_ind_mu_prefix2 (fun S S' =>
      ok_some S ->
      ok_some S' ->
      sequiv S S' ->
      sequiv (cs S) (cs S'))
  ).
  introv IH Hok Hok' Heq. inverts2 Heq; cs_simpl; eauto 10 with subst.
Qed.


Lemma uncs_preserves_sequiv_l :
  forall S S',
  ok_some S ->
  sequiv (cs S) S' ->
  sequiv S S'.
Proof.
  induction S using (well_founded_ind lt_Sty_mu_prefix_wf);
    intros; destruct S; cs_simpl; eauto 10 with subst.
Qed.


Lemma uncs_preserves_sequiv_r :
  forall S S',
  ok_some S' ->
  sequiv S (cs S') ->
  sequiv S S'.
Proof.
  induction S' using (well_founded_ind lt_Sty_mu_prefix_wf);
    intros; destruct S'; cs_simpl; eauto 10 with subst.
Qed.


Lemma uncs_preserves_sequiv :
  forall S S',
  ok_some S ->
  ok_some S' ->
  sequiv (cs S) (cs S') ->
  sequiv S S'.
Proof.
  intros. eapply uncs_preserves_sequiv_l; eauto.
  eapply uncs_preserves_sequiv_r; eauto.
Qed.


Lemma cs_preserves_sequiv_l :
  forall S S',
  ok_some S ->
  ok_some S' ->
  sequiv S S' ->
  sequiv (cs S) S'.
Proof.
  intros. eapply uncs_preserves_sequiv_r; eauto.
  eapply cs_preserves_sequiv; eauto.
Qed.


Lemma cs_preserves_sequiv_r :
  forall S S',
  ok_some S ->
  ok_some S' ->
  sequiv S S' ->
  sequiv S (cs S').
Proof.
  intros. eapply uncs_preserves_sequiv_l; eauto.
  eapply cs_preserves_sequiv; eauto.
Qed.


Lemma cs_preserves_not_sequiv :
  forall S S',
  ok_some S ->
  ok_some S' ->
  ~ sequiv S S' ->
  ~ sequiv (cs S) (cs S').
Proof.
  introv Hok Hok' H contra. apply H. eapply uncs_preserves_sequiv; eauto.
Qed.


Lemma uncs_preserves_not_sequiv :
  forall S S',
  ok_some S ->
  ok_some S' ->
  ~ sequiv (cs S) (cs S') ->
  ~ sequiv S S'.
Proof.
  introv Hok Hok' H contra. apply H. eapply cs_preserves_sequiv; eauto.
Qed.


Lemma cs_preserves_nsequiv :
  forall S S',
  ok_some S ->
  ok_some S' ->
  nsequiv S S' ->
  nsequiv (cs S) (cs S').
Proof.
  apply (Sty_ind_mu_prefix2 (fun S S' =>
    ok_some S ->
    ok_some S' ->
    nsequiv S S' ->
    nsequiv (cs S) (cs S')
  )).
  introv IH Hok Hok' Hneq. inverts Hneq; try cs_simpl;
    eauto 10 with subst nsequiv.
  - destruct S; destruct S'; cs_simpl; auto with nsequiv; false.
Qed.


Lemma uncs_preserves_nsequiv :
  forall S S',
  ok_some S ->
  ok_some S' ->
  nsequiv (cs S) (cs S') ->
  nsequiv S S'.
Proof.
  apply (Sty_ind_mu_prefix2 (fun S S' =>
    ok_some S ->
    ok_some S' ->
    nsequiv (cs S) (cs S') ->
    nsequiv S S'
  )).
  introv IH Hok Hok' Hneq. destruct S; destruct S'; try solve
    [ cs_simpl; auto
    | constructor; apply IH; eauto with subst; cs_simpl; auto with nsequiv
    ].
Qed.


Lemma cs_preserves_wellformedness :
  forall S,
  wellformed S ->
  wellformed (cs S).
Proof.
  induction S using (well_founded_ind lt_Sty_mu_prefix_wf);
    introv Hwf; destruct S; cs_simpl; eauto 10 with subst.
Qed.
Hint Resolve cs_preserves_wellformedness : subst.


Lemma tl_eq :
  forall eta S S' c c',
  S = S' ->
  tl eta S c = tl eta S' c'.
Proof.
  introv Heq. gen c c'. rewrite Heq. apply tl_contractive_irrelevant.
Qed.


(* TODO beautify *)
Lemma cs_preserves_tl :
  forall S eta c c',
  wellformed S ->
  tl eta S c = tl eta (cs S) c'.
Proof.
  intros S eta. induction S using (well_founded_ind lt_Sty_mu_prefix_wf);
    introv Hwf; destruct S; try solve [apply tl_eq; cs_simpl; reflexivity].
  - erewrite tl_mu_subst. erewrite H with (y := subst v (mu v S) S).
    apply tl_eq. cs_simpl. reflexivity.
    all: auto with subst wf free.
Unshelve.
  apply subst_preserves_Contractive.
    intro contra; simpl in contra; discriminate contra.
    apply wellformed_Contractive; auto.
    inverts c. assumption.
  apply wellformed_Contractive. auto with subst.
Qed.