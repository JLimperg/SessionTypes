Require Import Tac.
Require Import Arith Structures.Orders Structures.OrdersFacts.


Create HintDb env discriminated.


Inductive Var :=
| mkVar : nat -> Var
.
Hint Constructors Var : env.


Lemma eq_Var_dec : forall (X Y : Var), {X = Y} + {X <> Y}.
Proof. decide equality. apply eq_nat_dec. Defined.
Hint Immediate eq_Var_dec : env.


Module VarEq <: DecidableType.
  Definition t := Var.
  Definition eq (x y : Var) := eq x y.
  Instance eq_equiv : Equivalence eq := eq_equivalence.
  Definition eq_dec := eq_Var_dec.
End VarEq.
