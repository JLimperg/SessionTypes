Require Import Env Morphisms SessionTypes Program.Basics Msg Var.

Create HintDb wf discriminated.

Module Wf.

Import Sty.

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

Lemma wf_m :
  forall S e e',
  env_eq e e' ->
  (checked e S -> checked e' S) /\
  (ok e S -> ok e' S).
Proof with (eauto with wf).
  induction S; intros e e' eqee'; split; intros He...

    inversion_clear He. inversion_clear H.
    specialize IHS with (e := e) (e' := e'). destruct IHS as [Hch Hok]...

    inversion_clear He. inversion_clear H.
      rewrite eqee' in H0...
      specialize IHS with (e := e) (e' := e'). destruct IHS as [Hch Hok]...

    inversion_clear He. inversion_clear H.
    specialize IHS with (e := e) (e' := e'). destruct IHS as [Hch Hok]...

    inversion_clear He. inversion_clear H.
      rewrite eqee' in H0...
      specialize IHS with (e := e) (e' := e'). destruct IHS as [Hch Hok]...

    inversion_clear He. inversion_clear H.
    specialize IHS1 with (e := e) (e' := e'). specialize IHS2 with (e := e) (e' := e').
    destruct IHS1... destruct IHS2...

    inversion_clear He.
    specialize IHS1 with (e := e) (e' := e'). specialize IHS2 with (e := e) (e' := e').
    destruct IHS1... destruct IHS2...

    inversion_clear He. inversion_clear H.
    specialize IHS1 with (e := e) (e' := e'). specialize IHS2 with (e := e) (e' := e').
    destruct IHS1... destruct IHS2...

    inversion_clear He.
    specialize IHS1 with (e := e) (e' := e'). specialize IHS2 with (e := e) (e' := e').
    destruct IHS1... destruct IHS2...

    inversion_clear He. inversion_clear H. constructor.
    assert (env_eq (env_add v e) (env_add v e')). eapply env_add_eq in eqee'...
    constructor. eapply IHS in H0...

    inversion_clear He. eapply env_add_eq in eqee'. constructor. eapply IHS in H...

    inversion_clear He.
      rewrite eqee' in H...
      inversion H.

    inversion He.
Qed.

Lemma ok_m' :
  forall e e' S,
  env_eq e e' ->
  ok e S ->
  ok e' S.
Proof with auto.
  intros. remember wf_m as Hwf. clear HeqHwf.
  specialize Hwf with (S := S) (e := e) (e' := e'). apply Hwf in H. destruct H...
Qed.

Lemma checked_m' :
  forall e e' S,
  env_eq e e' ->
  checked e S ->
  checked e' S.
Proof with auto.
  intros. remember wf_m as Hwf. clear HeqHwf.
  specialize Hwf with (S := S) (e := e) (e' := e'). apply Hwf in H. destruct H...
Qed.

Instance ok_m : Proper (env_eq ==> eq ==> impl) ok.
Proof with eauto.
  unfold Proper. unfold respectful. unfold impl. intros x y eqxy X Y eqXY H.
  eapply ok_m'... rewrite <- eqXY...
Qed.

Instance checked_m : Proper (env_eq ==> eq ==> impl) checked.
Proof with eauto.
  unfold Proper. unfold respectful. unfold impl. intros x y eqxy X Y eqXY H.
  eapply checked_m'... rewrite <- eqXY...
Qed.

Lemma surplus_variables_in_env :
  forall S XS X,
  (checked XS S ->
  checked (env_add X XS) S) /\
  (ok XS S ->
  ok (env_add X XS) S).
Proof with (auto with env wf).
  let aut := (auto with env wf)
  in
  induction S; split; aut; intros H; inversion_clear H;
    (try (  (specialize IHS with (XS := XS) (X := X); apply proj1 in IHS;
            solve [inversion_clear H0; aut | aut])
         || (specialize IHS1 with (XS := XS) (X := X);
            specialize IHS2 with (XS := XS) (X := X);
            apply proj1 in IHS1; apply proj1 in IHS2;
            solve [inversion_clear H0; aut | aut])
         )).

    constructor. constructor. inversion_clear H0.
    specialize IHS with (XS := env_add v XS) (X := X).
    apply proj2 in IHS. rewrite env_add_exchange...

    specialize IHS with (XS := env_add v XS) (X := X).
    constructor. rewrite env_add_exchange. apply IHS...

    constructor. apply env_add_mem...

    inversion H0.
Qed.

Lemma surplus_variables_in_env_ok :
  forall XS X S,
  ok XS S ->
  ok (env_add X XS) S.
Proof. intros XS X S. apply surplus_variables_in_env. Qed.
Hint Resolve surplus_variables_in_env_ok : wf.

Lemma surplus_variables_in_env_checked :
  forall XS X S,
  checked XS S ->
  checked (env_add X XS) S.
Proof. intros XS X S. apply surplus_variables_in_env. Qed.
Hint Resolve surplus_variables_in_env_checked : wf.

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
        apply surplus_variables_in_env_ok...
        rewrite env_add_exchange...
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

End Wf.
