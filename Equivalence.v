Require Import Env SessionTypes SessionTypesInd Shape ShapeFacts Substitution
  SubstitutionFacts Tac Var Wellformed.

Inductive sequiv_gen sequiv : Sty -> Sty -> Prop :=
| sequiv_gen_end : sequiv_gen sequiv unit unit
| sequiv_gen_send : forall B S S',
    sequiv S S' ->
    sequiv_gen sequiv (send B S) (send B S')
| sequiv_gen_recv : forall B S S',
    sequiv S S' ->
    sequiv_gen sequiv (recv B S) (recv B S')
| sequiv_gen_echoice : forall S1 S2 S1' S2',
    sequiv S1 S1' ->
    sequiv S2 S2' ->
    sequiv_gen sequiv (echoice S1 S2) (echoice S1' S2')
| sequiv_gen_ichoice : forall S1 S2 S1' S2',
    sequiv S1 S1' ->
    sequiv S2 S2' ->
    sequiv_gen sequiv (ichoice S1 S2) (ichoice S1' S2')
| sequiv_gen_mu1 : forall X S S',
    sequiv (subst X (mu X S) S) S' ->
    sequiv_gen sequiv (mu X S) S'
| sequiv_gen_mu2 : forall X S S',
    sequiv S (subst X (mu X S') S') ->
    sequiv_gen sequiv S (mu X S')
.
Hint Constructors sequiv_gen.

CoInductive sequiv : Sty -> Sty -> Prop :=
| sequiv_fold : forall S S', sequiv_gen sequiv S S' -> sequiv S S'.
Hint Constructors sequiv.


Lemma sequiv_coind : forall R,
  (forall S S', R S S' -> sequiv_gen R S S')
  -> (forall S S', R S S' -> sequiv S S').
Proof. cofix CIH. introv H HR. apply H in HR. inverts HR; eauto. Qed.


Lemma sequiv_shape :
  forall S S',
  ok_some S ->
  ok_some S' ->
  sequiv S S' ->
  shape (substall S) = shape (substall S').
Proof.
  intros S S'.
  apply well_founded_induction_type_2 with
    (R := lt_Sty_mu_prefix2)
    (P := fun S S' => ok_some S -> ok_some S' -> sequiv S S' ->
     shape (substall S) = shape (substall S')).
  apply lt_Sty_mu_prefix2_wf. clear S S'.

  intros S S' IH HokS HokS' Heq. inverts2 Heq; auto; decompose_ex HokS;
    decompose_ex HokS'.

    rename S0 into S. simpl. inversion HokS; subst.
    rewrite shape_subst_substall_1 with (XS := env_add X XS); auto.
    rewrite shape_subst_substall_2 with (XS := XS) (X := X) (R := mu X S); auto.
    apply IH; eauto using subst_preserves_wellformedness.
      constructor; eauto using lt_Sty_mu_prefix_subst.

    rename S'0 into S'. simpl. inversion HokS'; subst.
    rewrite shape_subst_substall_1 with (XS := env_add X XS0); auto.
    asserts_rewrite (shape (substall S') = shape (substall (subst X (mu X S') S'))).
      apply shape_subst_substall_2 with (XS := XS0); auto.
    apply IH; eauto using subst_preserves_wellformedness.
      constructor; eauto using lt_Sty_mu_prefix_subst.
Qed.
