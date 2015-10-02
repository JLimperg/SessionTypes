Require Import List Logic.FunctionalExtensionality.
Import ListNotations.

Lemma fold_left_snoc :
  forall A B (f : B -> A -> B) a0 x xs,
  fold_left f (xs ++ [x]) a0 = f (fold_left f xs a0) x.
Proof.
  intros. rewrite <- fold_left_rev_right. rewrite rev_unit. simpl.
  rewrite fold_left_rev_right.
  assert ((fun x y => f x y) = f) as Hf.
    apply functional_extensionality. intros.
    apply functional_extensionality. auto.
  rewrite Hf. trivial.
Qed.
