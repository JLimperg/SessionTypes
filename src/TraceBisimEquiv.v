Require Import Contractive CS CSFacts Equiv Free Sty Subst SubstFacts Msg Tac
  TL TLFacts Var Wf WfFacts.


Create HintDb tleq discriminated.


Inductive R_trace_bisim_equivalence' : Sty -> Sty -> Prop :=
| R_trace_bisim_equivalence'_intro :
    forall S S' eta c c',
    wellformed S ->
    wellformed S' ->
    Tl_bisim (tl eta S c) (tl eta S' c') ->
    R_trace_bisim_equivalence' S S'.
Hint Constructors R_trace_bisim_equivalence' : tleq.


Lemma trace_bisim_equivalence' :
  forall S S' eta c c',
  wellformed S ->
  wellformed S' ->
  Tl_bisim (tl eta S c) (tl eta S' c') ->
  sequiv S S'.
Proof.
  Ltac solve_same_shape H :=
    inverts2 H; constructor; econstructor; eauto with wf
  .

  Ltac solve_mu H :=
    erewrite tl_mu_subst in H; [constructor; econstructor|]; eauto with free wf
  .

  Ltac solve_wellformed_var :=
    match goal with
    | _ : wellformed (var _) |- _ => auto with wf
    end
  .

  intros. apply sequiv_coind with (R := R_trace_bisim_equivalence');
    [|econstructor; eauto].
  clear. introv H. inverts H. rename H2 into Heq. destruct S; destruct S';
    try solve
      [ constructor
      | solve_wellformed_var
      | solve_mu Heq
      | solve_same_shape Heq
      ].
Unshelve.
  all: eauto with contractive subst.
Qed.

Theorem trace_bisim_equivalence :
  forall S S' eta
  (Swf : wellformed S)
  (Swf' : wellformed S'),
  Tl_bisim
    (tl eta S (wellformed_Contractive Swf))
    (tl eta S' (wellformed_Contractive Swf')) ->
  sequiv S S'.
Proof. intros. eapply trace_bisim_equivalence'; eauto. Qed.

Theorem trace_eq_equivalence :
  forall S S' eta
  (Swf : wellformed S)
  (Swf' : wellformed S'),
  (tl eta S (wellformed_Contractive Swf)) =
    (tl eta S' (wellformed_Contractive Swf')) ->
  sequiv S S'.
Proof.
  introv Heq. eapply trace_bisim_equivalence. rewrite Heq. Abort.


Inductive R_equivalence_trace_bisim' : Tl -> Tl -> Prop :=
| R_equivalence_trace_bisim'_intro :
    forall l l' eta,
    (exists S S' c c',
     tl eta (cs S) c = l /\
     tl eta (cs S') c' = l' /\
     wellformed S /\
     wellformed S' /\
     sequiv (cs S) (cs S')
    ) ->
    R_equivalence_trace_bisim' l l'
.


(* TODO ouch *)
Lemma equivalence_trace_bisim' :
  forall S S' eta c c',
  wellformed S ->
  wellformed S' ->
  sequiv S S' ->
  Tl_bisim (tl eta S c) (tl eta S' c').
Proof.
  Ltac wf_inv S1 H1 S2 :=
    let Htmp := fresh in
    assert (wellformed S1) as Htmp by (rewrite H1; auto with wf);
    assert (wellformed S2) by (auto with wf);
    clear Htmp
  .

  intros. (rewrite_strat (subterms cs_preserves_tl)); try assumption.
  apply Tl_bisim_coind with (R := R_equivalence_trace_bisim').
  - clear. introv CIH. inverts1 CIH. norm_hyp_auto.
    rename H0 into Hwf. rename H2 into Hwf'. rename H4 into Hsequiv.
    subst. inverts2 Hsequiv.
    * gen c c' Hwf Hwf'. rewrite <- Hsequiv. rewrite <- H2.
      clear Hsequiv. intros. constructor.
    * gen c c' Hwf Hwf'. rewrite <- H0. rewrite <- H1.
      introv Hwf Hwf'.
      wf_inv (send B S0) H0 S0.
      wf_inv (send B S'0) H1 S'0.
      simpl. constructor. econstructor.
      exists S0 S'0. eexists. eexists. splits.
      + symmetry. apply cs_preserves_tl. assumption.
      + symmetry. apply cs_preserves_tl. assumption.
      + assumption.
      + assumption.
      + apply cs_preserves_sequiv; eauto with wf.
    * gen c c' Hwf Hwf'. rewrite <- H0. rewrite <- H1.
      introv Hwf Hwf'.
      wf_inv (recv B S0) H0 S0.
      wf_inv (recv B S'0) H1 S'0.
      simpl. constructor. econstructor.
      exists S0 S'0. eexists. eexists. splits.
      + symmetry. apply cs_preserves_tl. assumption.
      + symmetry. apply cs_preserves_tl. assumption.
      + assumption.
      + assumption.
      + apply cs_preserves_sequiv; eauto with wf.
    * gen c c' Hwf Hwf'. rewrite <- H0. rewrite <- H1.
      introv Hwf Hwf'.
      wf_inv (echoice S1 S2) H0 S1.
      wf_inv (echoice S1 S2) H0 S2.
      wf_inv (echoice S1' S2') H1 S1'.
      wf_inv (echoice S1' S2') H1 S2'.
      simpl. constructor.
      + econstructor. exists S1. exists S1'. eexists. eexists. splits.
        -- symmetry. apply cs_preserves_tl. assumption.
        -- symmetry. apply cs_preserves_tl. assumption.
        -- assumption.
        -- assumption.
        -- apply cs_preserves_sequiv; eauto with wf.
      + econstructor. exists S2. exists S2'. eexists. eexists. splits.
        -- symmetry. apply cs_preserves_tl. assumption.
        -- symmetry. apply cs_preserves_tl. assumption.
        -- assumption.
        -- assumption.
        -- apply cs_preserves_sequiv; eauto with wf.
    * gen c c' Hwf Hwf'. rewrite <- H0. rewrite <- H1.
      introv Hwf Hwf'.
      wf_inv (ichoice S1 S2) H0 S1.
      wf_inv (ichoice S1 S2) H0 S2.
      wf_inv (ichoice S1' S2') H1 S1'.
      wf_inv (ichoice S1' S2') H1 S2'.
      simpl. constructor.
      + econstructor. exists S1. exists S1'. eexists. eexists. splits.
        -- symmetry. apply cs_preserves_tl. assumption.
        -- symmetry. apply cs_preserves_tl. assumption.
        -- assumption.
        -- assumption.
        -- apply cs_preserves_sequiv; eauto with wf.
      + econstructor. exists S2. exists S2'. eexists. eexists. splits.
        -- symmetry. apply cs_preserves_tl. assumption.
        -- symmetry. apply cs_preserves_tl. assumption.
        -- assumption.
        -- assumption.
        -- apply cs_preserves_sequiv; eauto with wf.
    * symmetry in H0. apply cs_mu_absurd in H0.
      + contradiction.
      + eauto with contractive wf.
    * symmetry in H0. apply cs_mu_absurd in H0.
      + contradiction.
      + eauto with contractive wf.
  - econstructor. exists S. exists S'. eexists. eexists. splits;
    auto with subst.
    * apply cs_preserves_sequiv; assumption.
Unshelve.
  all: auto with wf.
Qed.

Theorem equivalence_trace_bisim :
  forall S S' eta
  (Swf : wellformed S)
  (S'wf : wellformed S'),
  sequiv S S' ->
  Tl_bisim (tl eta S (wellformed_Contractive Swf))
    (tl eta S' (wellformed_Contractive S'wf)).
Proof. intros. apply equivalence_trace_bisim'; auto. Qed.