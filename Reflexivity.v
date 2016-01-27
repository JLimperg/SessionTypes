Require Import Equivalence SessionTypes Substitution Wellformed Var.

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
Hint Constructors R_refl.

Lemma R_refl_reflexivity :
  (forall S S', R_refl S S' -> sequiv S S')
  -> (forall S, wellformed S -> sequiv S S).
Proof. auto. Qed.

Theorem sequiv_reflexive :
  forall S,
  wellformed S ->
  sequiv S S.
Proof with auto.
  apply R_refl_reflexivity. apply sequiv_coind.
  intros S S' H. inversion_clear H.
    destruct S';
      try (constructor; constructor; apply wellformed_inversion in H0;
        try (apply H0); repeat constructor).
      inversion H0.
      constructor. constructor...
      constructor. constructor...
Qed.
