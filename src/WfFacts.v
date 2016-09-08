Require Import Contractive ContractiveFacts CSFacts Free FreeFacts SubstFacts
  Sty Tac Wf.


Hint Resolve cs_preserves_wellformed : wf.
Hint Resolve wellformed_Contractive : wf.
Hint Resolve wellformed_Closed : wf.
Hint Resolve mu_unfold_preserves_wellformed : wf.


Lemma wellformed_inv :
  (forall B S, wellformed (send B S) -> wellformed S) /\
  (forall B S, wellformed (recv B S) -> wellformed S) /\
  (forall S1 S2, wellformed (echoice S1 S2) -> wellformed S1 /\ wellformed S2) /\
  (forall S1 S2, wellformed (ichoice S1 S2) -> wellformed S1 /\ wellformed S2).
Proof. splits; unfold wellformed; auto with contractive free. Qed.


Hint Extern 2 (wellformed _) =>
  match goal with
  | H : wellformed _ |- _ =>
      solve [apply wellformed_inv in H; try (decompose_and H); assumption]
  end
: wf.


Hint Extern 2 =>
  match goal with
  | H : wellformed (var _) |- _ =>
      solve [
        unfold wellformed in H; destruct H as [_ H]; apply Closed_var_absurd in H;
        contradiction
      ]
  end
: wf.