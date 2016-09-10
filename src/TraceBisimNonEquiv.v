Require Import Msg Equiv EquivFacts NonEquiv Sty Tac TL TLFacts Var Wf WfFacts.
Require Import Classical.


Lemma contrapositive :
  forall P Q,
  (~ Q -> ~ P) ->
  P -> Q.
Proof. introv H HP. pose proof (classic Q) as HQ. inverts1 HQ; tauto. Qed.


Lemma NSequiv_not_Tl_bisim :
  forall S S' eta c c',
  Wf S ->
  Wf S' ->
  NSequiv S S' ->
  ~ Tl_bisim (tl eta S c) (tl eta S' c').
Proof.
  introv Hwf Hwf' Hnsequiv. induction Hnsequiv; introv Hcontra; try solve
    [ inverts2 Hcontra; false
    | inverts2 Hcontra; eapply IHHnsequiv; eauto with wf
    ].
  - erewrite tl_mu_subst in Hcontra.
    * eapply IHHnsequiv; eauto with wf.
    * auto with wf.
  - erewrite tl_mu_subst in Hcontra.
    * eapply IHHnsequiv; eauto with wf.
    * auto with wf.
  - destruct S; destruct S'; simpl in *; solve
      [inverts2 Hcontra | false | auto with wf].
Unshelve.
  all: auto with wf.
Qed.

Theorem trace_bisim_equivalence_alt :
  forall S S' eta
  (Swf : Wf S)
  (S'wf : Wf S'),
  Tl_bisim (tl eta S (Wf_Contractive Swf)) (tl eta S' (Wf_Contractive S'wf)) ->
  Sequiv S S'.
Proof.
  intros S S' eta Swf Swf'. apply contrapositive.
  rewrite <- NSequiv_iff_not_Sequiv; trivial. apply NSequiv_not_Tl_bisim; auto.
Qed.
