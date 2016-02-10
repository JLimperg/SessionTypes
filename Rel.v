Require Import Tac.
Require Export Relations.

Create HintDb rel discriminated.
Hint Unfold inclusion : rel.
Hint Unfold symmetric : rel.
Hint Unfold transitive : rel.

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

Lemma clos_trans_trans :
  forall A (R : relation A),
  inclusion A (clos_trans A R) R ->
  transitive A R.
Proof.
  unfold inclusion. unfold transitive. eauto with rel.
Qed.

Inductive clos_trans' {A} (R : relation A) : relation A :=
| clos_trans'_intro :
    forall x y z,
    R x y -> R y z -> clos_trans' R x z
.
Hint Constructors clos_trans' : rel.

Lemma clos_trans'_trans :
  forall A R,
  inclusion A (clos_trans' R) R ->
  transitive A R.
Proof. eauto with rel. Qed.
