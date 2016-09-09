Require Import Contractive CS CSFacts Equiv Free Sty Subst SubstFacts Msg Tac
  TL TLFacts Var Wf WfFacts.


Inductive R_trace_bisim_equivalence' : Sty -> Sty -> Prop :=
| R_trace_bisim_equivalence'_intro :
    forall S S' eta c c',
    Wf S ->
    Wf S' ->
    Tl_bisim (tl eta S c) (tl eta S' c') ->
    R_trace_bisim_equivalence' S S'.


Lemma trace_bisim_equivalence' :
  forall S S' eta c c',
  Wf S ->
  Wf S' ->
  Tl_bisim (tl eta S c) (tl eta S' c') ->
  Sequiv S S'.
Proof.
  Ltac solve_same_shape H :=
    inverts2 H; constructor; econstructor; eauto with wf
  .

  Ltac solve_mu H :=
    erewrite tl_mu_subst in H; [constructor; econstructor|]; eauto with free wf
  .

  Ltac solve_Wf_var :=
    match goal with
    | _ : Wf (var _) |- _ => auto with wf
    end
  .

  intros. apply Sequiv_coind with (R := R_trace_bisim_equivalence');
    [|econstructor; eauto].
  clear. introv H. inverts H. rename H2 into Heq. destruct S; destruct S';
    try solve
      [ constructor
      | solve_Wf_var
      | solve_mu Heq
      | solve_same_shape Heq
      ].
Unshelve.
  all: eauto with contractive subst.
Qed.

Theorem trace_bisim_equivalence :
  forall S S' eta
  (Swf : Wf S)
  (Swf' : Wf S'),
  Tl_bisim
    (tl eta S (Wf_Contractive Swf))
    (tl eta S' (Wf_Contractive Swf')) ->
  Sequiv S S'.
Proof. intros. eapply trace_bisim_equivalence'; eauto. Qed.

Theorem trace_eq_equivalence :
  forall S S' eta
  (Swf : Wf S)
  (Swf' : Wf S'),
  (tl eta S (Wf_Contractive Swf)) =
    (tl eta S' (Wf_Contractive Swf')) ->
  Sequiv S S'.
Proof. introv H. eapply trace_bisim_equivalence. rewrite H. reflexivity. Qed.


Inductive R_equivalence_trace_bisim' : Tl -> Tl -> Prop :=
| R_equivalence_trace_bisim'_intro :
    forall l l' eta,
    (exists S S' c c',
     l = tl eta (cs S) c /\
     l' = tl eta (cs S') c' /\
     Wf S /\
     Wf S' /\
     Sequiv (cs S) (cs S')
    ) ->
    R_equivalence_trace_bisim' l l'
.


(* TODO beautify *)
Lemma equivalence_trace_bisim' :
  forall S S' eta c c',
  Wf S ->
  Wf S' ->
  Sequiv S S' ->
  Tl_bisim (tl eta S c) (tl eta S' c').
Proof.
  Ltac wf_inv S1 H1 S2 :=
    let Htmp := fresh in
    assert (Wf S1) as Htmp by (rewrite H1; auto with wf);
    assert (Wf S2) by (auto with wf);
    clear Htmp
  .

  Ltac finish :=
    simpl; constructor; econstructor; eauto 15 with subst wf
  .

  intros. (rewrite_strat (subterms cs_preserves_tl)); try assumption.
  apply Tl_bisim_coind with (R := R_equivalence_trace_bisim');
    [|econstructor; eauto 10 with subst]; clear.

  introv CIH. inverts1 CIH. norm_hyp_auto.
  rename H0 into Hwf. rename H2 into Hwf'. rename H4 into HSequiv. subst.
  inverts2 HSequiv.
  - gen c c' Hwf Hwf'. rewrite <- HSequiv. rewrite <- H2.
    constructor.
  - gen c c' Hwf Hwf'. rewrite <- H0. rewrite <- H1. intros.
    wf_inv (send B S0) H0 S0.
    wf_inv (send B S'0) H1 S'0.
    finish.
  - gen c c' Hwf Hwf'. rewrite <- H0. rewrite <- H1. intros.
    wf_inv (recv B S0) H0 S0.
    wf_inv (recv B S'0) H1 S'0.
    finish.
  - gen c c' Hwf Hwf'. rewrite <- H0. rewrite <- H1. intros.
    wf_inv (echoice S1 S2) H0 S1.
    wf_inv (echoice S1 S2) H0 S2.
    wf_inv (echoice S1' S2') H1 S1'.
    wf_inv (echoice S1' S2') H1 S2'.
    finish.
  - gen c c' Hwf Hwf'. rewrite <- H0. rewrite <- H1. intros.
    wf_inv (ichoice S1 S2) H0 S1.
    wf_inv (ichoice S1 S2) H0 S2.
    wf_inv (ichoice S1' S2') H1 S1'.
    wf_inv (ichoice S1' S2') H1 S2'.
    finish.
  - auto with subst wf.
  - auto with subst wf.
Unshelve.
  all: auto with wf.
Grab Existential Variables.
  all: auto with subst.
Qed.

Theorem equivalence_trace_bisim :
  forall S S' eta
  (Swf : Wf S)
  (S'wf : Wf S'),
  Sequiv S S' ->
  Tl_bisim (tl eta S (Wf_Contractive Swf))
    (tl eta S' (Wf_Contractive S'wf)).
Proof. intros. apply equivalence_trace_bisim'; auto. Qed.
