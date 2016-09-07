Require Import Contractive Env Free FreeFacts Map Msg SessionTypes Shape
  Substitution SubstitutionFacts Tac TraceLanguage Var Wellformed.
Require Import FunctionalExtensionality.


Lemma tl_contractive_irrelevant :
  forall eta S contr contr',
  tl eta S contr = tl eta S contr'.
Proof.
  intros eta S. gen eta. induction S; intros; simpl; try solve [fequal; auto].
  - fequal. extensionality lx. auto.
Qed.


Lemma eta_irrelevance' :
  forall S eta eta' Hcontractive,
  (forall X, Free X S -> eta X = eta' X) ->
  tl eta S Hcontractive = tl eta' S Hcontractive.
Proof.
  induction S; introv Heq; simpl in *; try solve
    [ reflexivity
    | first [erewrite IHS | erewrite IHS1, IHS2]; eauto with free
    ].
  - fequal. extensionality lx. apply IHS.
    * introv Hfree. destruct (eq_var_dec v X).
      + subst. rewrite_all eta_override_same. reflexivity.
      + rewrite_all eta_override_different; [|assumption..]. apply Heq.
        auto with free.
  - apply Heq. auto with free.
Qed.


Lemma eta_irrelevance :
  forall S eta eta' Hcontractive,
  Closed S ->
  tl eta S Hcontractive = tl eta' S Hcontractive.
Proof.
  introv Hwf. apply eta_irrelevance'.
  - introv Hfree. contradict Hfree. auto with free.
Qed.


Lemma tl_subst :
  forall S T X eta HcontractiveS HcontractiveT HcontractiveST,
  Closed T ->
  tl (eta_override eta X (tl eta T HcontractiveT)) S HcontractiveS =
  tl eta (subst X T S) HcontractiveST.
Proof.
  intros. gen eta T. induction S; intros; simpl.
  - reflexivity.
  - erewrite IHS; trivial.
  - erewrite IHS; trivial.
  - erewrite IHS1; trivial; erewrite IHS2; trivial.
  - erewrite IHS1; trivial; erewrite IHS2; trivial.
  - simpl in *; destruct (beq_var X v) eqn:Heq; simpl; fequal; extensionality x.
    * apply beq_var_true in Heq. subst. rewrite eta_override_overwrite;
        auto using tl_contractive_irrelevant.
    * apply beq_var_false in Heq. rewrite eta_override_exchange; [|auto].
      erewrite eta_irrelevance with (S := T); trivial. eapply IHS; trivial.
  - simpl in *. destruct (beq_var X v) eqn:Heq.
    * apply beq_var_true in Heq. subst. rewrite override_same.
      apply tl_contractive_irrelevant.
    * simpl. auto using override_different, beq_var_false.
Qed.


Lemma tl_mu_unfold :
  forall S eta X Hcontractive Hcontractive',
  tl eta (mu X S) Hcontractive =
  tl (eta_override eta X (tl eta (mu X S) Hcontractive)) S Hcontractive'.
Proof.
  intros. simpl. rewrite tl_fix_fix at 1. apply tl_contractive_irrelevant.
Qed.


Lemma tl_mu_subst :
  forall S eta X Hcontractive Hcontractive',
  Closed (mu X S) ->
  tl eta (mu X S) Hcontractive = tl eta (subst X (mu X S) S) Hcontractive'.
Proof.
  introv Hclosed. erewrite tl_mu_unfold. erewrite tl_subst; eauto.
Unshelve.
  inversion Hcontractive. assumption.
Qed.