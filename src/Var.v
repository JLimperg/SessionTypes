Require Import Tac.
Require Import Arith Structures.Orders Structures.OrdersFacts.

Create HintDb env discriminated.

Inductive Var :=
| mkVar : nat -> Var
.
Hint Constructors Var : env.

Lemma eq_var_dec : forall (X Y : Var), {X = Y} + {X <> Y}.
Proof. decide equality. apply eq_nat_dec. Defined.
Hint Immediate eq_var_dec : env.

Definition beq_var x y :=
  match (x, y) with
  | (mkVar x', mkVar y') => beq_nat x' y'
  end
.
Hint Unfold beq_var : env.

Lemma beq_var_refl : forall x, true = beq_var x x.
Proof. intros. destruct x; unfold beq_var; apply beq_nat_refl. Qed.
Hint Resolve beq_var_refl : env.

Lemma beq_var_true_iff : forall x y, x = y <-> beq_var x y = true.
Proof with (auto with env).
  intros. split; intros H.
    rewrite H; auto with env.

    destruct x; destruct y; unfold beq_var in *. rewrite beq_nat_true_iff in H.
    rewrite H. auto.
Qed.
Hint Resolve beq_var_true_iff : env.

Lemma beq_var_true : forall x y, beq_var x y = true -> x = y.
Proof with auto. intros. apply beq_var_true_iff... Qed.
Hint Resolve beq_var_true : env.

Lemma beq_var_false_iff : forall x y, x <> y <-> beq_var x y = false.
Proof with (auto with env).
  intros x y. split; intros H; destruct x; destruct y.
    unfold beq_var. apply beq_nat_false_iff. auto.

    introv contra. rewrite contra in H. rewrite <- beq_var_refl in H.
    discriminate.
Qed.
Hint Resolve beq_var_false_iff : env.

Lemma beq_var_false : forall x y, beq_var x y = false -> x <> y.
Proof. intros. apply beq_var_false_iff; auto. Qed.
Hint Resolve beq_var_false : env.

Lemma beq_var_eq : forall x y, x = y -> beq_var x y = true.
Proof. intros. apply beq_var_true_iff; auto. Qed.
Hint Resolve beq_var_eq : env.

Lemma beq_var_neq : forall x y, x <> y -> beq_var x y = false.
Proof. intros. apply beq_var_false_iff; auto. Qed.
Hint Resolve beq_var_neq : env.

Lemma beq_nat_sym : forall x y, beq_nat x y = beq_nat y x.
Proof. induction x; intros y; destruct y; simpl; auto. Qed.
Hint Resolve beq_nat_sym : env.

Lemma beq_var_sym : forall x y, beq_var x y = beq_var y x.
Proof. intros. destruct x; destruct y; unfold beq_var. apply beq_nat_sym. Qed.

Module VarOrder <: OrderedType.

  Module N := PeanoNat.Nat.
  Module NF := OrderedTypeFacts N.

  Definition t := Var.
  Definition eq (x y : Var) := eq x y.
  Definition lt (x y : Var) :=
    match x, y with
    | mkVar n, mkVar m => lt n m
    end
  .
  Definition compare (x y : Var) :=
    match x, y with
    | mkVar n, mkVar m => N.compare n m
    end
  .

  Definition eq_equiv := eq_equivalence (A := Var).
  Definition eq_dec := eq_var_dec.

  Instance lt_irreflexive : Irreflexive lt.
  Proof.
    unfold Irreflexive. unfold Reflexive. unfold complement. intros x H.
    destruct x. unfold lt in H. apply StrictOrder_Irreflexive in H. assumption.
  Qed.

  Instance lt_transitive : Transitive lt.
  Proof.
    unfold Transitive. intros x y z Hxy Hyz. destruct x; destruct y; destruct z.
    unfold lt in *. eapply transitivity; eassumption.
  Qed.

  Instance lt_strorder : StrictOrder lt := {
    StrictOrder_Irreflexive := lt_irreflexive ;
    StrictOrder_Transitive := lt_transitive
  }.

  Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof. solve_proper. Qed.

  Lemma compare_spec : forall x y : Var, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros x y. destruct (compare x y) eqn:Hxy; destruct x; destruct y;
      simpl in Hxy; constructor; first
        [ apply NF.compare_eq_iff in Hxy
        | apply NF.compare_lt_iff in Hxy
        | apply NF.compare_gt_iff in Hxy
        ]; auto.
  Qed.

End VarOrder.
