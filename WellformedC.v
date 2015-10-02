Require Import Env List1 Morphisms Msg Program.Basics SessionTypesC
  Shape TLC.LibTactics Var.

Create HintDb wf discriminated.

Module WfC.
Import StyC.

Inductive ok : Env -> Sty -> Prop :=
| ok_unit :
    forall xs, ok xs unit
| ok_send :
    forall xs B S,
    ok xs S ->
    ok xs (send B S)
| ok_recv :
    forall xs B S,
    ok xs S ->
    ok xs (recv B S)
| ok_echoice :
    forall xs S1 S2,
    ok xs S1 ->
    ok xs S2 ->
    ok xs (echoice S1 S2)
| ok_ichoice :
    forall xs S1 S2,
    ok xs S1 ->
    ok xs S2 ->
    ok xs (ichoice S1 S2)
| ok_mu :
    forall xs ys S,
    shape S <> varS ->
    shape S <> muS ->
    ok (env_union_vars xs ys) S ->
    ok xs (mu ys S)
| ok_var :
    forall X xs,
    env_mem X xs ->
    ok xs (var X)
.
Hint Constructors ok : wf.

Definition wellformed (S : Sty) := ok env_empty S.

Global Instance ok_m_env_eq : Proper (env_eq ==> eq ==> iff) ok.
Proof with (eauto with wf).
  unfold Proper. unfold respectful. intros xs ys Hxsys S. gen ys xs.
  induction S; intros xs ys Hysxs T HST; rewrite <- HST; clear HST;
    assert (env_eq xs ys) as Hxsys by (symmetry; auto);
    split; try (intro H; inverts H); constructor; eauto; try solve
    [eapply IHS; eauto | eapply IHS1; eauto | eapply IHS2; eauto].

    assert (env_eq (env_union_vars xs l) (env_union_vars ys l)).
      rewrite Hxsys. reflexivity.
    eapply IHS; eauto.

    assert (env_eq (env_union_vars ys l) (env_union_vars xs l)).
      rewrite Hysxs. reflexivity.
    eapply IHS; eauto.

    rewrite Hxsys. auto.

    rewrite Hysxs. auto.
Qed.

Global Instance ok_m_subset : Proper (env_subset ==> eq ==> impl) ok.
Proof.
  unfold Proper. unfold respectful. unfold impl. introv Hsub Heq H.
  subst. rename y0 into S. gen x y.
  induction S; introv H Hsub; constructor; inverts H; eauto.
    eapply IHS; [eauto | rewrite Hsub; reflexivity].
Qed.

End WfC.
