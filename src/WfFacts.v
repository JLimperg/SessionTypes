Require Import Contractive ContractiveFacts CSFacts Free FreeFacts SubstFacts
  Sty Tac Wf.


Hint Resolve cs_preserves_Wf : wf.
Hint Resolve Wf_Contractive : wf.
Hint Resolve Wf_Closed : wf.
Hint Resolve mu_unfold_preserves_Wf : wf.


Lemma Wf_inv :
  forall S S',
  StySubSimple S S' ->
  Wf S' ->
  Wf S.
Proof.
  introv sub; inverts1 sub; unfold Wf in *;
  auto with contractive free.
Qed.


Hint Extern 2 (Wf ?S) =>
  match goal with
  | H : Wf _ |- _ =>
      solve [apply (Wf_inv S) in H; [exact H | auto with stysub]]
  end
: wf.


Hint Extern 2 =>
  match goal with
  | H : Wf (var _) |- _ =>
      solve [
        unfold Wf in H; destruct H as [_ H]; apply Closed_var_absurd in H;
        contradiction
      ]
  end
: wf.
