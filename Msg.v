Require Import Arith.

Inductive Msg :=
| mkMsg : nat -> Msg
.

Definition beq_msg x y :=
  match (x, y) with
  | (mkMsg x, mkMsg y) => beq_nat x y
  end
.

Lemma eq_Msg_dec :
  forall (M M' : Msg), {M = M'} + {M <> M'}.
Proof. decide equality. apply eq_nat_dec. Defined.
