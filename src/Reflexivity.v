Require Import Equiv Sty Subst Tac Var Wf WfFacts.

Create HintDb refl discriminated.

Inductive R_refl : Sty -> Sty -> Prop :=
| refl_helper_refl :
    forall S,
    Wf S ->
    R_refl S S
| refl_helper_mu1   :
    forall X S,
    Wf (subst X (mu X S) S) ->
    R_refl (mu X S) (subst X (mu X S) S)
| refl_helper_mu2 :
    forall X S,
    Wf (subst X (mu X S) S) ->
    R_refl (subst X (mu X S) S) (mu X S)
.
Hint Constructors R_refl : refl.

Lemma R_refl_reflexivity :
  (forall S S', R_refl S S' -> Sequiv S S')
  -> (forall S, Wf S -> Sequiv S S).
Proof. auto with refl. Qed.

Theorem Sequiv_reflexive :
  forall S,
  Wf S ->
  Sequiv S S.
Proof.
  apply R_refl_reflexivity. apply Sequiv_coind.
  introv H. inverts1 H; [destruct S'|..]; auto with wf refl.
Qed.
