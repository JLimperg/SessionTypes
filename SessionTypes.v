Require Import Env Msg Shape Var.

Inductive Sty : Set :=
| unit : Sty
| send : Msg -> Sty -> Sty
| recv : Msg -> Sty -> Sty
| echoice : Sty -> Sty -> Sty
| ichoice : Sty -> Sty -> Sty
| mu : Var -> Sty -> Sty
| var : Var -> Sty
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


Lemma shape_dec :
  forall S sh, {shape S = sh} + {shape S <> sh}.
Proof. decide equality. Qed.
