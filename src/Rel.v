Require Import Tac.
Require Export Relations.


Create HintDb rel discriminated.
Hint Unfold inclusion : rel.
Hint Unfold symmetric : rel.


Inductive clos_sym A (R : relation A) : relation A :=
| clos_sym_intro : forall x y : A, R x y -> clos_sym A R y x
.
Hint Constructors clos_sym : rel.
Hint Constructors clos_trans : rel.


Lemma clos_sym_sym :
  forall A (R : relation A),
  inclusion A (clos_sym A R) R ->
  symmetric A R.
Proof. auto with rel. Qed.
