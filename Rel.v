Require Import Relations.Relation_Definitions Relations.Relation_Operators.

Create HintDb rel discriminated.

Inductive clos_sym A (R : relation A) : relation A :=
| clos_sym_intro : forall x y : A, R x y -> clos_sym A R y x
.
Hint Constructors clos_sym : rel.
Hint Constructors clos_trans : rel.

Lemma clos_sym_sym :
  forall A (R : relation A),
  inclusion A (clos_sym A R) R ->
  symmetric A R.
Proof with (auto with rel).
  unfold inclusion. unfold symmetric. intros A R Hinc. intros x y HRxy.
  apply Hinc...
Qed.

Lemma clos_trans_trans :
  forall A (R : relation A),
  inclusion A (clos_trans A R) R ->
  transitive A R.
Proof with (eauto with rel).
  unfold inclusion. unfold transitive. intros A R Hinc. intros x y z Hxy Hyz.
  apply Hinc...
Qed.
