Require Import CS CSFacts Equiv Reflexivity Sty StyInd Subst SubstFacts Tac Wf
  WfFacts.

Create HintDb trans discriminated.
Hint Resolve sequiv_reflexive : trans.


Inductive trans_helper : Sty -> Sty -> Prop :=
| trans_helper_trans :
    forall S T U,
    wellformed S ->
    wellformed T ->
    wellformed U ->
    sequiv S T ->
    sequiv T U ->
    trans_helper S U
.
Hint Constructors trans_helper : trans.

Lemma trans_helper_refl :
  forall S,
  wellformed S ->
  trans_helper S S.
Proof. eauto with trans. Qed.

Lemma sequiv_impl_trans_helper :
  forall S T,
  wellformed S ->
  wellformed T ->
  sequiv S T ->
  trans_helper S T.
Proof. eauto with trans. Qed.

Lemma trans_helper_transitive :
  (forall S T, trans_helper S T -> sequiv S T) ->
  (forall S T U,
    wellformed S ->
    wellformed T ->
    wellformed U ->
    sequiv S T ->
    sequiv T U ->
    sequiv S U
  ).
Proof. eauto with trans. Qed.


(* TODO beautify (a lot) *)
Theorem sequiv_transitive :
  forall S T U,
  wellformed S ->
  wellformed T ->
  wellformed U ->
  sequiv S T ->
  sequiv T U ->
  sequiv S U.
Proof.
  apply trans_helper_transitive. apply sequiv_coind.
  introv H. rename S' into U. inverts H.
  assert (sequiv S (cs T)) as HSeqT  by (
    eapply cs_preserves_sequiv_r; eauto with wf
  ).
  assert (sequiv (cs T) U) as HTeqU by (
    eapply cs_preserves_sequiv_l; eauto with wf
  ).
  clear H3 H4. inverts2 HSeqT; inverts2 HTeqU; subst; try solve [false].

  (* unit *)
  - auto.

  - constructor. rewrite <- HSeqT in *.
    apply sequiv_impl_trans_helper; auto with wf.

  (* send *)
  - rewrite <- H4 in H3. injection H3; intros; subst.
    constructor. apply trans_helper_trans with (T := S); eauto with wf.
      apply cs_preserves_wellformed in H1. rewrite <- H4 in H1.
      eauto with wf.

  - constructor. rewrite <- H3 in *.
    apply trans_helper_trans with (T := send B S'); eauto with wf.
      rewrite H3. eauto with wf.

  (* recv *)
  - rewrite <- H4 in H3. injection H3; intros; subst.
    constructor. apply trans_helper_trans with (T := S); eauto with wf.
      apply cs_preserves_wellformed in H1. rewrite <- H4 in H1.
      eauto with wf.

  - constructor. rewrite <- H3 in *.
    apply trans_helper_trans with (T := recv B S'); eauto with wf.
      rewrite H3. eauto with wf.

  (* echoice *)
  - assert (wellformed (echoice S1' S2')) by (rewrite H3; eauto with wf).
    rewrite <- H4 in H3. injection H3; intros; subst.
    constructor.
    * apply trans_helper_trans with (T := S0); eauto with wf.
    * apply trans_helper_trans with (T := S3); eauto with wf.

  - assert (wellformed (echoice S1' S2')) by (rewrite H3; eauto with wf).
    constructor. rewrite <- H3 in *.
    apply trans_helper_trans with (T := echoice S1' S2'); eauto with wf.

  (* ichoice *)
  - assert (wellformed (ichoice S1' S2')) by (rewrite H3; eauto with wf).
    rewrite <- H4 in H3. injection H3; intros; subst.
    constructor.
    * apply trans_helper_trans with (T := S0); eauto with wf.
    * apply trans_helper_trans with (T := S3); eauto with wf.

  - assert (wellformed (ichoice S1' S2')) by (rewrite H3; eauto with wf).
    constructor. rewrite <- H3 in *.
    apply trans_helper_trans with (T := ichoice S1' S2'); eauto with wf.

  (* unit *)
  - rewrite <- HTeqU in *. constructor. apply sequiv_impl_trans_helper;
      auto with wf.

  (* send *)
  - constructor. rewrite <- H3 in *.
    apply trans_helper_trans with (T := send B S); auto with wf.
      rewrite H3; eauto with wf.

  (* recv *)
  - constructor. rewrite <- H3 in *.
    apply trans_helper_trans with (T := recv B S); auto with wf.
      rewrite H3; eauto with wf.

  (* echoice *)
  - constructor. rewrite <- H3 in *.
    apply trans_helper_trans with (T := echoice S1 S2); auto with wf.
      rewrite H3; eauto with wf.

  (* ichoice *)
  - constructor. rewrite <- H3 in *.
    apply trans_helper_trans with (T := ichoice S1 S2); auto with wf.
      rewrite H3; eauto with wf.

  (* mu 1 (impossible) *)
  - exfalso; eauto with subst wf.

  (* mu 2 *)
  - constructor.
    assert (sequiv (cs T) (mu X0 S')) as HTeqU' by auto.
    apply trans_helper_trans with (T := cs T);
      eauto with wf.

  (* mu 3 (impossible) *)
  - exfalso; eauto with subst wf.

  (* mu 4 (impossible) *)
  - exfalso; eauto with subst wf.
Qed.