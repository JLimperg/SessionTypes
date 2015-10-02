Require Import Env Msg Shape Var.

Module Sty.

Inductive Sty : Set :=
| unit : Sty
| send : Msg -> Sty -> Sty
| recv : Msg -> Sty -> Sty
| echoice : Sty -> Sty -> Sty
| ichoice : Sty -> Sty -> Sty
| mu : Var -> Sty -> Sty
| var : Var -> Sty
.

Fixpoint subst (x : Var) (r : Sty) (orig : Sty) : Sty :=
  match orig with
  | unit => unit
  | send msg tail => send msg (subst x r tail)
  | recv msg tail => recv msg (subst x r tail)
  | ichoice tail1 tail2 => ichoice (subst x r tail1) (subst x r tail2)
  | echoice tail1 tail2 => echoice (subst x r tail1) (subst x r tail2)
  | mu y tail => if beq_var x y then mu y tail else mu y (subst x r tail)
  | var y => if beq_var x y then r else var y
  end
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

End Sty.
