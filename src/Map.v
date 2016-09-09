(* TODO Refactor this whole module. *)
Require Import Tac Var.
Require Import FunctionalExtensionality.

Definition override
  {A B}
  (eq_dec : forall x y, {x = y} + {x <> y})
  (f : A -> B) (y : A) (y' : B) : A -> B :=

  fun x => if eq_dec x y then y' else f x.
Hint Unfold override : tl.

Notation eta_override := (override eq_Var_dec).


Lemma override_exchange :
  forall A B eq_dec (f : A -> B) y z y' z',
  y <> z ->
  override eq_dec (override eq_dec f z z') y y' =
  override eq_dec (override eq_dec f y y') z z'.
Proof.
  introv Hneq. compute. extensionality x.
  destruct (eq_dec x y) as [Hxy | Hxy]; destruct (eq_dec x z) as [Hxz | Hxz];
    congruence.
Qed.

Lemma eta_override_exchange :
  forall B (f : Var -> B) y z y' z',
  y <> z ->
  eta_override (eta_override f z z') y y' =
  eta_override (eta_override f y y') z z'.
Proof. introv H. apply override_exchange. auto. Qed.


Lemma override_overwrite :
  forall A B eq_dec (f : A -> B) y z y' z',
  y = z ->
  override eq_dec (override eq_dec f z z') y y' = override eq_dec f y y'.
Proof.
  intros. subst. compute. extensionality x.
  destruct (eq_dec x z) as [Hxz | Hxz]; auto.
Qed.

Lemma eta_override_overwrite :
  forall B (f : Var -> B) y z y' z',
  y = z ->
  eta_override (eta_override f z z') y y' = eta_override f y y'.
Proof. introv H. apply override_overwrite. auto. Qed.


Lemma override_same :
  forall A B eq_dec (f : A -> B) x x',
  override eq_dec f x x' x = x'.
Proof.
  intros. compute. destruct (eq_dec x x); [reflexivity | exfalso; auto].
Qed.

Lemma eta_override_same :
  forall B (f : Var -> B) x x',
  eta_override f x x' x = x'.
Proof. intros. apply override_same. Qed.


Lemma override_different :
  forall A B eq_dec (f : A -> B) x x' y,
  x <> y ->
  override eq_dec f x x' y = f y.
Proof.
  intros. compute. destruct (eq_dec y x); [exfalso; auto | reflexivity].
Qed.

Lemma eta_override_different :
  forall B (f : Var -> B) x x' y,
  x <> y ->
  eta_override f x x' y = f y.
Proof. intros. apply override_different. assumption. Qed.
