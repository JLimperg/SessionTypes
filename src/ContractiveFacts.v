Require Import Contractive Sty Shape Tac.

(******************************************************************************)
(* Automation *)


Lemma Contractive_inv :
  forall S S',
  StySub S S' ->
  Contractive S' ->
  Contractive S.
Proof.
  introv sub; inverts1 sub; [inverts1 sub|]; introv H; inverts H; auto.
Qed.


Hint Extern 2 (Contractive ?S) =>
  match goal with
  | H : Contractive _ |- _ =>
      solve [apply (Contractive_inv S) in H; [exact H | auto with stysub]]
  end
: contractive.


Hint Extern 2 (shape ?S <> varS) =>
  match goal with
  | H : Contractive (mu _ S) |- _ => solve [inversion H; assumption]
  end
: contractive.