Require Import Equivalence SessionTypes Substitution Tac Var Wellformed.

Create HintDb refl discriminated.

Inductive R_refl : Sty -> Sty -> Prop :=
| refl_helper_refl :
    forall S,
    wellformed S ->
    R_refl S S
| refl_helper_mu1   :
    forall X S,
    wellformed (subst X (mu X S) S) ->
    R_refl (mu X S) (subst X (mu X S) S)
| refl_helper_mu2 :
    forall X S,
    wellformed (subst X (mu X S) S) ->
    R_refl (subst X (mu X S) S) (mu X S)
.
Hint Constructors R_refl : refl.

Lemma R_refl_reflexivity :
  (forall S S', R_refl S S' -> sequiv S S')
  -> (forall S, wellformed S -> sequiv S S).
Proof. auto with refl. Qed.

Theorem sequiv_reflexive :
  forall S,
  wellformed S ->
  sequiv S S.
Proof.
  apply R_refl_reflexivity. apply sequiv_coind.
  introv H. inverts1 H; [destruct S'|..]; auto with wf refl.
Qed.
