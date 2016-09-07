Require Import Sty Tac Var.

Create HintDb free discriminated.

Inductive Free : Var -> Sty -> Prop :=
| Free_send : forall X B S, Free X S -> Free X (send B S)
| Free_recv : forall X B S, Free X S -> Free X (recv B S)
| Free_echoice : forall X S1 S2, Free X S1 \/ Free X S2 -> Free X (echoice S1 S2)
| Free_ichoice : forall X S1 S2, Free X S1 \/ Free X S2 -> Free X (ichoice S1 S2)
| Free_mu : forall X Y S, Free X S -> X <> Y -> Free X (mu Y S)
| Free_var : forall X, Free X (var X)
.
Hint Constructors Free : free.


Definition Closed (S : Sty) : Prop :=
  forall X, ~ Free X S.
Hint Unfold Closed : free.
