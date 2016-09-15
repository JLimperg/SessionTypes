Require Import Arith.

Inductive Msg :=
| mkMsg : nat -> Msg
.


Lemma eq_Msg_dec :
  forall (M M' : Msg), {M = M'} + {M <> M'}.
Proof. decide equality. apply eq_nat_dec. Defined.
