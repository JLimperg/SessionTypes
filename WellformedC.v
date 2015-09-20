Require Import Env Morphisms Program.Basics SessionTypesC Msg Shape Var.

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
    (shape S <> varS) ->
    (shape S <> muS) ->
    ok (env_union xs ys) S ->
    ok xs (mu ys S)
| ok_var :
    forall X xs,
    env_mem X xs ->
    ok xs (var X)
.
Hint Constructors ok : wf.

Definition wellformed (S : Sty) := ok env_empty S.

(* TODO beautify *)
Instance ok_m : Proper (env_eq ==> eq_syn ==> iff) ok.
Proof with (eauto with wf).
  unfold Proper. unfold respectful. intros xs ys Hxsys S.
  generalize dependent ys. generalize dependent xs.
  induction S; intros xs ys Hxsys T HST.
    inversion_clear HST. split; constructor.

    inversion_clear HST. split;
      intro H'; constructor; inversion_clear H'; eapply IHS; eauto with wf.

    inversion_clear HST. split;
      intro H'; constructor; inversion_clear H'; eapply IHS; eauto with wf.

    inversion_clear HST. split.
      intro H'; inversion_clear H'; constructor; [eapply IHS1 | eapply IHS2]; eauto with wf.
      intro H'; inversion_clear H'; constructor; [eapply IHS1 | eapply IHS2]; eauto with wf.

    inversion_clear HST. split.
      intro H'; inversion_clear H'; constructor; [eapply IHS1 | eapply IHS2]; eauto with wf.
      intro H'; inversion_clear H'; constructor; [eapply IHS1 | eapply IHS2]; eauto with wf.

    inversion_clear HST. split.
      intro H'. inversion_clear H'. constructor.
        unfold not in *. apply eq_syn_shape in H0. intro Hsh.
        rewrite <- H0 in Hsh. apply H1. rewrite Hsh. trivial.

        unfold not in *. apply eq_syn_shape in H0. intro Hsh.
        rewrite <- H0 in Hsh. apply H2. rewrite Hsh. trivial.

        eapply IHS; eauto with wf. rewrite Hxsys. rewrite <- H. reflexivity.

      intro H'. inversion_clear H'. constructor.
        unfold not in *. apply eq_syn_shape in H0. intro Hsh.
        rewrite H0 in Hsh. apply H1. rewrite Hsh. trivial.

        unfold not in *. apply eq_syn_shape in H0. intro Hsh.
        rewrite H0 in Hsh. apply H2. rewrite Hsh. trivial.

        eapply IHS; eauto with wf. rewrite Hxsys. rewrite <- H. reflexivity.

    inversion_clear HST. subst. split; intro H; inversion_clear H;
      constructor.
      rewrite <- Hxsys...
      rewrite Hxsys...
Qed.

End WfC.
