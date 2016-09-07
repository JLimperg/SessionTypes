Require Import Contractive Equivalence Free SessionTypes Substitution
  SubstitutionFacts Msg Tac TraceLanguage TraceLanguageFacts Var Wellformed.


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