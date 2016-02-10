Require Export FunctionalExtensionality Var.

Definition override {a b : Type} (beq : a -> a -> bool) (f : a -> b) (y : a) (y' : b) :=
  fun x => if beq x y then y' else f x.
Hint Unfold override : tl.

Notation eta_override := (override beq_var).

Lemma override_exchange :
  forall A B beq f (y z : A) (y' z' : B),
  (forall a b : A, a = b <-> beq a b = true) ->
  beq y z = false ->
  override beq (override beq f z z') y y' =
  override beq (override beq f y y') z z'.
Proof with auto.
  intros A B beq f y y' z z' Hbeq Hyneqz. unfold not in Hyneqz. unfold override.
  apply functional_extensionality. intros x.
  destruct (beq x y) eqn:Hxy.
    apply Hbeq in Hxy. rewrite Hxy. rewrite Hyneqz...
    destruct (beq x y')...
Qed.

Lemma override_overwrite :
  forall A B beq f (y z : A) (y' z' : B),
  (forall a b : A, a = b <-> beq a b = true) ->
  beq y z = true ->
  override beq (override beq f z z') y y' = override beq f y y'.
Proof with auto.
  intros A B beq f y z y' z' Hbeq Hyeqz. unfold override.
  apply functional_extensionality. intros x. destruct (beq x y) eqn:Hxy...
    apply Hbeq in Hyeqz. rewrite <- Hyeqz. rewrite Hxy...
Qed.
