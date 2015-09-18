Require Import OrdersFacts.

Module CompFacts (Import O : DecStrOrder) <: CompareFacts O.

  Lemma compare_eq_iff : forall x y, compare x y = Eq <-> eq x y.
  Proof.
    intros.
    assert (CompareSpec (eq x y) (lt x y) (lt y x) (compare x y)) as cs.
      apply compare_spec.
    split; intros H.
      inversion cs; auto; rewrite <- H0 in H; discriminate.
      inversion cs; auto; contradict H1; rewrite H; apply irreflexivity.
  Qed.

  Lemma compare_eq : forall x y, compare x y = Eq -> eq x y.
  Proof. apply compare_eq_iff. Qed.

  Lemma compare_lt_iff : forall x y, compare x y = Lt <-> lt x y.
  Proof with auto.
    intros.
    assert (CompareSpec (eq x y) (lt x y) (lt y x) (compare x y)) as cs.
      apply compare_spec.
    split; intros H.
      inversion cs; auto; rewrite <- H0 in H; discriminate.
      inversion cs...
        rewrite H1 in H. contradict H. apply irreflexivity.
        assert (lt x x) as Contra. eapply transitivity; eassumption.
          contradict Contra. apply irreflexivity.
  Qed.

  Lemma compare_gt_iff : forall x y, compare x y = Gt <-> lt y x.
  Proof with auto.
    intros.
    assert (CompareSpec (eq x y) (lt x y) (lt y x) (compare x y)) as cs.
      apply compare_spec.
    split; intros H.
      inversion cs; auto; rewrite <- H0 in H; discriminate.
      inversion cs...
        rewrite H1 in H. contradict H. apply irreflexivity.
        assert (lt x x) as Contra. eapply transitivity; eassumption.
          contradict Contra. apply irreflexivity.
  Qed.

  Lemma compare_nlt_iff : forall x y, compare x y <> Lt <-> ~ (lt x y).
  Proof. intros x y. split; intros H1 H2; apply H1; apply compare_lt_iff; auto. Qed.

  Lemma compare_ngt_iff : forall x y, compare x y <> Gt <-> ~ (lt y x).
  Proof. intros x y. split; intros H1 H2; apply H1; apply compare_gt_iff; auto. Qed.

  Instance compare_compat : Proper (eq==>eq==>Logic.eq) compare.
  Proof with auto.
    unfold Proper. unfold respectful. intros x y eqxy x0 y0 eqx0y0.
    destruct (compare x x0) eqn:compxx0; destruct (compare y y0) eqn:compyy0...
      apply compare_lt_iff in compyy0. apply compare_eq_iff in compxx0.
      contradict compyy0. rewrite <- eqx0y0. rewrite <- eqxy. rewrite <- compxx0.
      apply irreflexivity.

      apply compare_eq_iff in compxx0. apply compare_gt_iff in compyy0.
      contradict compyy0. rewrite <- eqx0y0. rewrite <- compxx0. rewrite eqxy.
      apply irreflexivity.

      apply compare_lt_iff in compxx0. apply compare_eq_iff in compyy0.
      contradict compxx0. rewrite eqx0y0. rewrite <- compyy0. rewrite eqxy.
      apply irreflexivity.

      apply compare_lt_iff in compxx0. apply compare_gt_iff in compyy0.
      contradict compxx0. rewrite eqx0y0. rewrite eqxy. intro H.
      assert (lt y y). eapply transitivity; eassumption.
      contradict H0. apply irreflexivity.

      apply compare_gt_iff in compxx0. apply compare_eq_iff in compyy0.
      contradict compxx0. rewrite eqx0y0. rewrite eqxy. rewrite compyy0.
      apply irreflexivity.

      apply compare_gt_iff in compxx0. apply compare_lt_iff in compyy0.
      rewrite eqxy in compxx0. rewrite eqx0y0 in compxx0.
      assert (lt y0 y0). eapply transitivity; eassumption. contradict H.
      apply irreflexivity.
  Qed.

  Lemma compare_refl : forall x, compare x x = Eq.
  Proof. intros x. apply compare_eq_iff. apply reflexivity. Qed.

  Lemma compare_antisym : forall x y, compare y x = CompOpp (compare x y).
  Proof with auto.
    intros x y. destruct (compare x y) eqn:cxy; simpl.
      apply compare_eq_iff in cxy. rewrite cxy. apply compare_refl.
      apply compare_lt_iff in cxy. apply compare_gt_iff...
      apply compare_gt_iff in cxy. apply compare_lt_iff...
  Qed.

End CompFacts.
