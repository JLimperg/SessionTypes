Require Import Contractive CS CSFacts Equiv Free Sty Subst SubstFacts Msg Tac
  TL TLFacts Var Wf.


Create HintDb tleq discriminated.


Inductive R_trace_equality_equivalence : Sty -> Sty -> Prop :=
| R_trace_equality_equivalence_intro :
    forall S S' eta (Swf : wellformed S) (S'wf : wellformed S'),
    tl eta S (wellformed_Contractive S Swf) =
      tl eta S' (wellformed_Contractive S' S'wf) ->
    R_trace_equality_equivalence S S'.
Hint Constructors R_trace_equality_equivalence : tleq.


Theorem trace_equality_equivalence :
  forall S S' eta
  (Swf : wellformed S)
  (S'wf : wellformed S'),
  tl eta S (wellformed_Contractive S Swf) =
    tl eta S' (wellformed_Contractive S' S'wf) ->
  sequiv S S'.
Proof.
  Ltac solve_different_shape H := simpl in H; discriminate H.

  Ltac solve_wellformed_var H :=
    match goal with
    | _ : wellformed (var _) |- _ =>
      clear H; eauto with wf
    end
  .

  Ltac solve_mu H := erewrite tl_mu_subst in H; eauto with tleq free.

  Ltac solve_same_shape H :=
    inverts2 H; constructor; econstructor;
      match goal with
      | |- tl _ ?s _ = tl _ ?s' _ =>
        erewrite tl_contractive_irrelevant with (S := s);
        erewrite tl_contractive_irrelevant with (S := s')
      end;
      eassumption
  .

  introv H. apply sequiv_coind with (R := R_trace_equality_equivalence);
    [|econstructor; eauto].
  clear. introv HR. inverts HR. rename H into Heq. destruct S; destruct S';
    solve
      [ constructor
      | solve_wellformed_var Heq
      | solve_different_shape Heq
      | solve_mu Heq
      | solve_same_shape Heq
      ].
Unshelve.
  all:
    repeat match goal with
    | H : tl _ _ _ = tl _ _ _ |- _ =>
        clear H
    end;
    eauto with subst wf.
Qed.


Inductive R_trace_bisim_equivalence : Sty -> Sty -> Prop :=
| R_trace_bisim_equivalence_intro :
    forall S S' eta (Swf : wellformed S) (S'wf : wellformed S'),
    Tl_bisim (tl eta S (wellformed_Contractive S Swf))
      (tl eta S' (wellformed_Contractive S' S'wf)) ->
    R_trace_bisim_equivalence S S'.
Hint Constructors R_trace_bisim_equivalence : tleq.


Theorem trace_bisim_equivalence :
  forall S S' eta
  (Swf : wellformed S)
  (S'wf : wellformed S'),
  Tl_bisim (tl eta S (wellformed_Contractive S Swf))
    (tl eta S' (wellformed_Contractive S' S'wf)) ->
  sequiv S S'.
Proof.
  Ltac solve_same_shape' H :=
    inverts2 H; constructor; econstructor;
    match goal with
    | |- Tl_bisim (tl _ ?s _) (tl _ ?s' _) =>
      erewrite tl_contractive_irrelevant with (S := s);
      erewrite tl_contractive_irrelevant with (S := s')
    end;
    eassumption
  .

  introv H. apply sequiv_coind with (R := R_trace_bisim_equivalence);
    [|econstructor; eauto].
  clear. introv H. inverts1 H. rename H into Heq. destruct S; destruct S';
    try solve
    [ constructor
    | solve_wellformed_var Heq
    | inverts2 Heq
    | solve_mu Heq
    | solve_same_shape' Heq
    ].
Unshelve.
  all:
    repeat match goal with
    | H : Tl_bisim (tl _ _ _) (tl _ _ _) |- _ =>
        clear H
    end;
    eauto with wf subst.
Qed.


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
    R_equivalence_trace_bisim' l l'.


(* TODO ouch *)
Lemma equivalence_trace_bisim' :
  forall S S' eta c c',
  wellformed S ->
  wellformed S' ->
  sequiv S S' ->
  Tl_bisim (tl eta S c) (tl eta S' c').
Proof.
  intros. (rewrite_strat (subterms cs_preserves_tl)); try assumption.
  apply Tl_bisim_coind with (R := R_equivalence_trace_bisim').
  - clear. introv CIH. inverts1 CIH. norm_hyp_auto.
    rename H0 into Hwf. rename H2 into Hwf'. rename H4 into Hsequiv.
    subst. inverts2 Hsequiv.
    * gen c c' Hwf Hwf'. rewrite <- Hsequiv. rewrite <- H2.
      clear Hsequiv. clear H2.
      introv Hwf Hwf'. constructor.
    * gen c c' Hwf Hwf'. rewrite <- H0. rewrite <- H1.
      introv Hwf Hwf'.
      assert (wellformed (send B S0)) as Htmp1 by (rewrite H0; auto with subst).
      assert (wellformed (send B S'0)) as Htmp2 by (rewrite H1; auto with subst).
      apply wellformed_inv in Htmp1. apply wellformed_inv in Htmp2.
      simpl. constructor. econstructor.
      exists S0 S'0. eexists. eexists. splits.
      + symmetry. apply cs_preserves_tl. assumption.
      + symmetry. apply cs_preserves_tl. assumption.
      + assumption.
      + assumption.
      + apply cs_preserves_sequiv; eauto.
    * gen c c' Hwf Hwf'. rewrite <- H0. rewrite <- H1.
      introv Hwf Hwf'.
      assert (wellformed (recv B S0)) as Htmp1 by (rewrite H0; auto with subst).
      assert (wellformed (recv B S'0)) as Htmp2 by (rewrite H1; auto with subst).
      apply wellformed_inv in Htmp1. apply wellformed_inv in Htmp2.
      simpl. constructor. econstructor.
      exists S0 S'0. eexists. eexists. splits.
      + symmetry. apply cs_preserves_tl. assumption.
      + symmetry. apply cs_preserves_tl. assumption.
      + assumption.
      + assumption.
      + apply cs_preserves_sequiv; eauto.
    * gen c c' Hwf Hwf'. rewrite <- H0. rewrite <- H1.
      introv Hwf Hwf'.
      assert (wellformed (echoice S1 S2)) as Htmp1 by (rewrite H0; auto with subst).
      assert (wellformed (echoice S1' S2')) as Htmp2 by (rewrite H1; auto with subst).
      apply wellformed_inv in Htmp1. apply wellformed_inv in Htmp2.
      destruct Htmp1. destruct Htmp2.
      simpl. constructor.
      + econstructor. exists S1. exists S1'. eexists. eexists. splits.
        -- symmetry. apply cs_preserves_tl. assumption.
        -- symmetry. apply cs_preserves_tl. assumption.
        -- assumption.
        -- assumption.
        -- apply cs_preserves_sequiv; eauto.
      + econstructor. exists S2. exists S2'. eexists. eexists. splits.
        -- symmetry. apply cs_preserves_tl. assumption.
        -- symmetry. apply cs_preserves_tl. assumption.
        -- assumption.
        -- assumption.
        -- apply cs_preserves_sequiv; eauto.
    * gen c c' Hwf Hwf'. rewrite <- H0. rewrite <- H1.
      introv Hwf Hwf'.
      assert (wellformed (ichoice S1 S2)) as Htmp1 by (rewrite H0; auto with subst).
      assert (wellformed (ichoice S1' S2')) as Htmp2 by (rewrite H1; auto with subst).
      apply wellformed_inv in Htmp1. apply wellformed_inv in Htmp2.
      destruct Htmp1. destruct Htmp2.
      simpl. constructor.
      + econstructor. exists S1. exists S1'. eexists. eexists. splits.
        -- symmetry. apply cs_preserves_tl. assumption.
        -- symmetry. apply cs_preserves_tl. assumption.
        -- assumption.
        -- assumption.
        -- apply cs_preserves_sequiv; eauto.
      + econstructor. exists S2. exists S2'. eexists. eexists. splits.
        -- symmetry. apply cs_preserves_tl. assumption.
        -- symmetry. apply cs_preserves_tl. assumption.
        -- assumption.
        -- assumption.
        -- apply cs_preserves_sequiv; eauto.
    * symmetry in H0. apply cs_mu_absurd in H0.
      + contradiction.
      + eauto with wf.
    * symmetry in H0. apply cs_mu_absurd in H0.
      + contradiction.
      + eauto with wf.
  - econstructor. exists S. exists S'. eexists. eexists. splits;
    auto with subst.
    * apply cs_preserves_sequiv; eauto with wf.
Unshelve.
  all:
    try solve
      [apply wellformed_Contractive; auto with subst].
Qed.

Theorem equivalence_trace_bisim :
  forall S S' eta
  (Swf : wellformed S)
  (S'wf : wellformed S'),
  sequiv S S' ->
  Tl_bisim (tl eta S (wellformed_Contractive _ Swf))
    (tl eta S' (wellformed_Contractive _ S'wf)).
Proof. intros. apply equivalence_trace_bisim'; auto. Qed.
