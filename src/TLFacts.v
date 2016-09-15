Require Import Contractive Env Free FreeFacts Map Msg Sty Shape
  Subst SubstFacts Tac TL Var.
Require Import FunctionalExtensionality.


(******************************************************************************)
(* Facts about Tl_bisim *)


Inductive R_Tl_bisim_reflexive : Tl -> Tl -> Prop :=
| R_Tl_bisim_reflexive_intro :
    forall l,
    R_Tl_bisim_reflexive l l
.

Lemma Tl_bisim_reflexive :
  forall l,
  Tl_bisim l l.
Proof.
  intros. apply Tl_bisim_coind with (R := R_Tl_bisim_reflexive);
    [|constructor; auto].
  clear. introv H. inverts H. rename l' into l. destruct l; constructor;
    constructor.
Qed.


Inductive R_Tl_bisim_symmetric : Tl -> Tl -> Prop :=
| R_Tl_bisim_symmetric_intro :
    forall l l',
    Tl_bisim l l' ->
    R_Tl_bisim_symmetric l' l
.

Lemma Tl_bisim_symmetric :
  forall l l',
  Tl_bisim l l' ->
  Tl_bisim l' l.
Proof.
  intros. apply Tl_bisim_coind with (R := R_Tl_bisim_symmetric);
    [|constructor; auto].
  clear. introv H. inverts1 H. inverts2 H; constructor; constructor; auto.
Qed.



Inductive R_Tl_bisim_transitive : Tl -> Tl -> Prop :=
| R_Tl_bisim_transitive_intro :
    forall l1 l2 l3,
    Tl_bisim l1 l2 ->
    Tl_bisim l2 l3 ->
    R_Tl_bisim_transitive l1 l3
.

Lemma Tl_bisim_transitive :
  forall l1 l2 l3,
  Tl_bisim l1 l2 ->
  Tl_bisim l2 l3 ->
  Tl_bisim l1 l3.
Proof.
  intros. apply Tl_bisim_coind with (R := R_Tl_bisim_transitive);
    [|econstructor; eauto].
  clear. introv H. inversion_clear H as [l1 l2 l3 H1 H2]. subst.
  inverts2 H1; inverts2 H2; constructor; econstructor; eauto.
Qed.


Add Relation Tl Tl_bisim
  reflexivity proved by Tl_bisim_reflexive
  symmetry proved by Tl_bisim_symmetric
  transitivity proved by Tl_bisim_transitive
  as Tl_bisim_rel.


(******************************************************************************)
(* Facts about tl *)


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
    * introv Hfree. destruct (eq_Var_dec v X).
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
  - simpl in *; destruct (eq_Var_dec X v); simpl; fequal; extensionality x.
    * subst. rewrite eta_override_overwrite;
      auto using tl_contractive_irrelevant.
    * rewrite eta_override_exchange; [|auto].
      erewrite eta_irrelevance with (S := T); trivial. eapply IHS; trivial.
  - simpl in *. destruct (eq_Var_dec X v).
    * subst. rewrite override_same. apply tl_contractive_irrelevant.
    * simpl. auto using override_different.
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
