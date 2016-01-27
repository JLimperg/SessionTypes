Require Import SessionTypes Shape ShapeFacts Substitution Tac Var Wellformed.

Lemma subst_preserves_shape :
  forall S X r,
  shape S <> varS ->
  shape (subst X r S) = shape S.
Proof.
  induction S; introv Hvarsh; simpl in *; auto;
    destruct (beq_var X v); auto.
    exfalso; auto.
Qed.


Lemma substall_shape :
  forall S,
  wellformed S ->
  shape (substall S) = unitS \/
  shape (substall S) = sendS \/
  shape (substall S) = recvS \/
  shape (substall S) = ichoiceS \/
  shape (substall S) = echoiceS.
Proof.
  introv Hwf. induction Hwf; simpl in *; solve
    [iauto | decompose sum IHHwf; simpl in *; shape_inv_auto; iauto].
Qed.
