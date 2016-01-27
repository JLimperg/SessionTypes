Require Import Env Msg Var.

Inductive Sty : Set :=
| unit : Sty
| send : Msg -> Sty -> Sty
| recv : Msg -> Sty -> Sty
| echoice : Sty -> Sty -> Sty
| ichoice : Sty -> Sty -> Sty
| mu : Var -> Sty -> Sty
| var : Var -> Sty
.
