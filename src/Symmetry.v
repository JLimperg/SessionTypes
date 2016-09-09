Require Import Sty Equiv.

Inductive sym {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| sym_sym : forall x y, R x y -> sym R y x
.

Lemma symmetric_closure_symmetry {A} : forall (R : A -> A -> Prop),
  (forall x y, sym R x y -> R x y)
  -> (forall x y, R x y -> R y x).
Proof.
  intros R H1 x y H2. apply H1. constructor. assumption.
Qed.

Theorem Sequiv_symmetric : forall S S',
  Sequiv S S' -> Sequiv S' S.
Proof with auto.
  apply symmetric_closure_symmetry. apply Sequiv_coind.
  intros S S' H.
  inversion_clear H. inversion_clear H0.
  inversion H; constructor; subst; constructor...
Qed.
