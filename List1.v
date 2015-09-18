Require Import List Var.

Create HintDb list1 discriminated.

Inductive list1 (A : Type) :=
| nil1 : A -> list1 A
| cons1 : A -> list1 A -> list1 A
.

Inductive In1 {A : Type} : A -> list1 A -> Prop :=
| in1_nil : forall x y, x = y -> In1 x (nil1 A y)
| in1_cons : forall x y ys, x = y \/ In1 x ys -> In1 x (cons1 A y ys)
.
Hint Constructors In1 : list1.

Section Dec.

Variable A : Type.
Hypothesis eq_dec : forall (x y : A), {x = y} + {x <> y}.

Lemma eq_list1_dec :
  forall (l l' : list1 A),
  {l = l'} + {l <> l'}.
Proof. intros. decide equality. Qed.

Lemma In1_dec :
  forall (x : A) l,
  {In1 x l} + {~ In1 x l}.
Proof with (auto with list1).
  intros. induction l; destruct (eq_dec x a)...
    right. intros H. inversion_clear H...
    destruct IHl...
      right. intros H. inversion_clear H. inversion_clear H0...
Qed.

End Dec.

Fixpoint fold_right1 {A B : Type} (f : A -> B -> B) (a0 : B) (xs : list1 A) : B :=
  match xs with
  | nil1 x => f x a0
  | cons1 x xs' => f x (fold_right1 f a0 xs')
  end
.
