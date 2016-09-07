Require Import SessionTypes.

Inductive Shape : Set :=
| unitS
| sendS
| recvS
| echoiceS
| ichoiceS
| muS
| varS
.


Definition shape (S : Sty) : Shape :=
  match S with
  | unit => unitS
  | send _ _ => sendS
  | recv _ _ => recvS
  | ichoice _ _ => ichoiceS
  | echoice _ _ => echoiceS
  | mu _ _ => muS
  | var _ => varS
  end
.
