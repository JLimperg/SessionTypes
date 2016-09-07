Require Import Env Sty Subst Msg Shape Tac Var.
Require Import Morphisms Program.Basics.

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

Scheme ok_ind_mut := Induction for ok Sort Prop
with checked_ind_mut := Induction for checked Sort Prop.

Definition wellformed S := ok env_empty S.

Hint Extern 1 =>
  match goal with
  | H : wellformed _ |- _ => unfold wellformed in H
  | |- wellformed _ => unfold wellformed
  end
.

Notation ok_some S := (exists XS, ok XS S).

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
Hint Resolve subst_preserves_wellformedness : wf.


Lemma ok_mu_shape :
  forall XS X S,
  ok XS (mu X S) ->
  shape S = unitS \/
  shape S = sendS \/
  shape S = recvS \/
  shape S = echoiceS \/
  shape S = ichoiceS \/
  shape S = muS.
Proof. introv Hok. inverts2 Hok; iauto. Qed.


(*****************************************************************************)
(* Automation *)


Lemma ok_var_absurd :
  forall X XS,
  ok XS (var X) -> False.
Proof. introv H. inverts H. Qed.

Hint Extern 1 =>
  match goal with
  | H : ok _ (var _) |- _ =>
      solve [exfalso; apply ok_var_absurd in H; assumption]
  end
: wf.

Hint Extern 4 (checked _ ?S) =>
  match goal with
  | H : ok _ (send _ S) |- _ => inverts H
  | H : ok _ (recv _ S) |- _ => inverts H
  | H : ok _ (echoice S _) |- _ => inverts H
  | H : ok _ (echoice _ S) |- _ => inverts H
  | H : ok _ (ichoice S _) |- _ => inverts H
  | H : ok _ (ichoice _ S) |- _ => inverts H
  end
: wf.


Hint Extern 4 (ok _ ?S) =>
  match goal with
  | H : checked _ S |- _ => inverts H
  end
: wf.


Lemma wellformed_inv :
  (forall B S, wellformed (send B S) -> wellformed S) /\
  (forall B S, wellformed (recv B S) -> wellformed S) /\
  (forall S1 S2, wellformed (echoice S1 S2) -> wellformed S1 /\ wellformed S2) /\
  (forall S1 S2, wellformed (ichoice S1 S2) -> wellformed S1 /\ wellformed S2) /\
  (forall X S, wellformed (mu X S) -> ok (env_add X env_empty) S /\ wellformed (subst X (mu X S) S)).
Proof.
  Hint Extern 1 =>
    match goal with
    | H : env_mem _ env_empty |- _ =>
        solve [exfalso; apply env_mem_empty in H; assumption]
    end
  .
  splits; introv H; try solve [inverts2 H; auto with wf].
  - split.
    + inverts2 H; auto with wf.
    + inverts H; auto with wf.
Qed.

Hint Extern 4 (wellformed ?S) =>
  let inv H := apply wellformed_inv in H in
  match goal with
  | H : wellformed (send _ S) |- _ => inv H
  | H : wellformed (recv _ S) |- _ => inv H
  | H : wellformed (echoice S _) |- _ => inv H
  | H : wellformed (echoice _ S) |- _ => inv H
  | H : wellformed (ichoice S _) |- _ => inv H
  | H : wellformed (ichoice _ S) |- _ => inv H
  end
: wf.

Hint Extern 4 (wellformed (subst ?X (mu ?X ?S) ?S)) =>
  match goal with
  | H : wellformed (mu X S) |- _ =>
    apply wellformed_inv in H
  end
: wf.

Hint Extern 4 (ok _ ?S) =>
  match goal with
  | H : wellformed (mu _ S) |- _ => apply wellformed_inv in H
  end
: wf.
