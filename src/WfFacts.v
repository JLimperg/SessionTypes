Require Import Contractive ContractiveFacts CSFacts Free FreeFacts SubstFacts
  Sty Tac Wf.


Hint Resolve cs_preserves_wellformed : wf.
Hint Resolve wellformed_Contractive : wf.
Hint Resolve wellformed_Closed : wf.
Hint Resolve mu_unfold_preserves_wellformed : wf.


Lemma wellformed_inv :
  forall S S',
  StySubSimple S S' ->
  wellformed S' ->
  wellformed S.
Proof.
  introv sub; inverts1 sub; unfold wellformed in *;
  auto with contractive free.
Qed.


Hint Extern 2 (wellformed ?S) =>
  match goal with
  | H : wellformed _ |- _ =>
      solve [apply (wellformed_inv S) in H; [exact H | auto with stysub]]
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