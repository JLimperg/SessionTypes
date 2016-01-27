Require Import Env Morphisms SessionTypes Substitution Program.Basics Msg
  TLC.LibTactics Var.

Create HintDb wf discriminated.

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

Definition wellformed S := ok env_empty S.
Hint Unfold wellformed : wf.

Lemma ok_checked_subset :
  forall S e e',
  env_subset e e' ->
  (checked e S -> checked e' S) /\
  (ok e S -> ok e' S).
Proof.
  induction S; introv Hsub; split; introv H;
    try (first [edestruct IHS | edestruct IHS1; edestruct IHS2]); eauto;
    try solve
      [ constructor; constructor; inverts H as H; inverts H; auto
      | constructor; inverts H; auto
      ].

    constructor. constructor.
    destruct IHS with (e := env_add v e) (e' := env_add v e').
    apply env_add_m_subset. auto. inverts H. inverts H4. auto.

    constructor. inverts H. eapply IHS. apply env_add_m_subset; eauto. auto.

    constructor. inverts H.
      eapply env_mem_spec_subset; eauto.
      inverts H0.

    inverts H.
Qed.

Global Instance checked_m_subset : Proper (env_subset ==> eq ==> impl) checked.
Proof.
  unfold Proper. unfold respectful. unfold impl.
  introv Hsub Heq Hch. subst. remember ok_checked_subset as lemma.
  edestruct lemma; eauto.
Qed.

Global Instance ok_m_subset : Proper (env_subset ==> eq ==> impl) ok.
Proof.
  unfold Proper. unfold respectful. unfold impl.
  introv Hsub Heq Hch. subst. remember ok_checked_subset as lemma.
  edestruct lemma; eauto.
Qed.

Global Instance checked_m_env_eq : Proper (env_eq ==> eq ==> impl) checked.
Proof.
  unfold Proper. unfold respectful. unfold impl. introv Hsub Heq Hch. subst.
  apply env_subset_equal in Hsub. rewrite <- Hsub. auto.
Qed.

Global Instance ok_m_env_eq : Proper (env_eq ==> eq ==> impl) ok.
Proof.
  unfold Proper. unfold respectful. unfold impl. introv Hsub Heq Hch. subst.
  apply env_subset_equal in Hsub. rewrite <- Hsub. auto.
Qed.

Lemma ok_add :
  forall XS X S,
  ok XS S ->
  ok (env_add X XS) S.
Proof.
  introv H.
  asserts_rewrite <- (env_subset XS (env_add X XS)). apply env_subset_add.
  auto.
Qed.
Hint Resolve ok_add : wf.

Lemma checked_add :
  forall XS X S,
  checked XS S ->
  checked (env_add X XS) S.
Proof.
  introv H.
  asserts_rewrite <- (env_subset XS (env_add X XS)). apply env_subset_add.
  auto.
Qed.
Hint Resolve checked_add : wf.

Lemma subst_preserves_wellformedness :
  forall S T XS X,
  ok XS T ->
  ok (env_add X XS) S ->
  ok XS (subst X T S).
Proof with (auto with env wf).
  assert (forall XS X T x,
          ok XS T ->
          env_mem x (env_add X XS) ->
          checked XS (subst X T (var x))) as Hvar.

    intros XS X T x HT HxXXS.
    assert ({ x = X } + { x <> X }) as HxX...
    inversion_clear HxX; subst; simpl.
      rewrite <- beq_var_refl...
      assert (beq_var X x = false) as HXx... rewrite HXx. clear HXx.
      assert (env_mem x XS). eapply env_mem_add; eauto.
      auto with env wf.


  let rec v        := apply Hvar; auto with env
  with    c        := constructor; auto with env
  with    sendrecv := inversion_clear H; subst; constructor; [v | c]
  with    choice   := constructor; solve [ inversion_clear H ; [v | c]
                                         | inversion_clear H0; [v | c]]
  in
  induction S; intros T XS X HT HS; simpl; auto with env wf;
    inversion_clear HS; [sendrecv | sendrecv | choice | choice | ..].

    destruct (beq_var X v) eqn:HXv.
      apply beq_var_true_iff in HXv. subst. rewrite env_add_twice in H...

      apply beq_var_false_iff in HXv. constructor. apply IHS.
        apply ok_add...
        rewrite env_add_assoc...
Qed.

Lemma wellformed_inversion :
  forall S S1 S2 B X,
     (wellformed (send B S) -> wellformed S)
  /\ (wellformed (recv B S) -> wellformed S)
  /\ (wellformed (echoice S1 S2) -> wellformed S1 /\ wellformed S2)
  /\ (wellformed (ichoice S1 S2) -> wellformed S1 /\ wellformed S2)
  /\ (wellformed (mu X S) -> wellformed (subst X (mu X S) S)).
Proof with (auto with env).
  let rec prefix := inversion_clear H; inversion_clear H0
  with    csr    := prefix; [auto | contradict H]
  with    cch    := prefix; [contradict H | inversion_clear H1; [contradict H0 | split; assumption]]
  with    cmu    := apply subst_preserves_wellformedness; auto with env; inversion H; auto with env
  in
  intros S S1 S2 B X; unfold wellformed in *; repeat split; try (intro H);
    try (solve [cmu]); inversion_clear H; inversion_clear H0; try assumption;
    try (solve [contradict H; auto with env]);
    inversion_clear H1;
    try (solve [contradict H0; auto with env | auto with env]).
Qed.

Lemma wellformed_inversion_send : forall B S,
  wellformed (send B S) -> wellformed S.
Proof with auto. intros B S. apply wellformed_inversion... apply (mkVar 0). Qed.
Hint Resolve wellformed_inversion_send : wf.

Lemma wellformed_inversion_recv : forall B S,
  wellformed (recv B S) -> wellformed S.
Proof with auto. intros B S. apply wellformed_inversion... apply (mkVar 0). Qed.
Hint Resolve wellformed_inversion_recv : wf.

Lemma wellformed_inversion_echoice : forall S1 S2,
  wellformed (echoice S1 S2) -> wellformed S1 /\ wellformed S2.
Proof with auto.
  intros S1 S2. apply wellformed_inversion... apply (mkMsg 0). apply (mkVar 0).
Qed.

Lemma wellformed_inversion_echoice1 : forall S1 S2,
  wellformed (echoice S1 S2) -> wellformed S1.
Proof with auto. intros S1 S2. apply wellformed_inversion_echoice... Qed.
Hint Resolve wellformed_inversion_echoice1 : wf.

Lemma wellformed_inversion_echoice2 : forall S1 S2,
  wellformed (echoice S1 S2) -> wellformed S2.
Proof with auto. intros S1 S2. apply wellformed_inversion_echoice... Qed.
Hint Resolve wellformed_inversion_echoice2 : wf.

Lemma wellformed_inversion_ichoice : forall S1 S2,
  wellformed (ichoice S1 S2) -> wellformed S1 /\ wellformed S2.
Proof with auto.
  intros S1 S2. apply wellformed_inversion... apply (mkMsg 0). apply (mkVar 0).
Qed.

Lemma wellformed_inversion_ichoice1 : forall S1 S2,
  wellformed (ichoice S1 S2) -> wellformed S1.
Proof with auto. intros S1 S2. apply wellformed_inversion_ichoice... Qed.
Hint Resolve wellformed_inversion_ichoice1 : wf.

Lemma wellformed_inversion_ichoice2 : forall S1 S2,
  wellformed (ichoice S1 S2) -> wellformed S2.
Proof with auto. intros S1 S2. apply wellformed_inversion_ichoice... Qed.
Hint Resolve wellformed_inversion_ichoice2 : wf.

Lemma wellformed_inversion_mu : forall X S,
  wellformed (mu X S) -> wellformed (subst X (mu X S) S).
Proof with auto. intros X S. apply wellformed_inversion... apply (mkMsg 0). Qed.
Hint Resolve wellformed_inversion_mu : wf.
