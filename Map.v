Require Export FunctionalExtensionality Tac Var.

Definition override
  {A B}
  (eq_dec : forall x y, {x = y} + {x <> y})
  (f : A -> B) (y : A) (y' : B) : A -> B :=

  fun x => if eq_dec x y then y' else f x.
Hint Unfold override : tl.

Notation eta_override := (override eq_var_dec).


Lemma override_exchange :
  forall A B eq_dec f (y z : A) (y' z' : B),
  y <> z ->
  override eq_dec (override eq_dec f z z') y y' =
  override eq_dec (override eq_dec f y y') z z'.
Proof.
  introv Hneq. compute. extensionality x.
  destruct (eq_dec x y) as [Hxy | Hxy]; destruct (eq_dec x z) as [Hxz | Hxz];
    congruence.
Qed.

Lemma eta_override_exchange :
  forall B (f : Var -> B) (y z : Var) (y' z' : B),
  y <> z ->
  eta_override (eta_override f z z') y y' =
  eta_override (eta_override f y y') z z'.
Proof. introv H. apply override_exchange. auto. Qed.


Lemma override_overwrite :
  forall A B eq_dec f (y z : A) (y' z' : B),
  y = z ->
  override eq_dec (override eq_dec f z z') y y' = override eq_dec f y y'.
Proof.
  intros. subst. compute. extensionality x.
  destruct (eq_dec x z) as [Hxz | Hxz]; auto.
Qed.

Lemma eta_override_overwrite :
  forall B (f : Var -> B) (y z : Var) (y' z' : B),
  y = z ->
  eta_override (eta_override f z z') y y' = eta_override f y y'.
Proof. introv H. apply override_overwrite. auto. Qed.
