Require Import Arith.

Inductive Msg :=
| mkMsg : nat -> Msg
.

Definition beq_msg x y :=
  match (x, y) with
  | (mkMsg x, mkMsg y) => beq_nat x y
  end
.
