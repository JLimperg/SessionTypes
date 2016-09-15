Require Import Msg Tac Var.
Require Import TLC.LibLogic.


Inductive Sty : Set :=
| unit : Sty
| send : Msg -> Sty -> Sty
| recv : Msg -> Sty -> Sty
| echoice : Sty -> Sty -> Sty
| ichoice : Sty -> Sty -> Sty
| mu : Var -> Sty -> Sty
| var : Var -> Sty
.


Lemma eq_Sty_dec :
  forall (S T : Sty), {S = T} + {S <> T}.
Proof.
  pose proof eq_Msg_dec. pose proof eq_Var_dec. decide equality; auto.
Defined.


Instance Sty_Inhab : Inhab Sty.
Proof. constructor. exists unit. trivial. Qed.


Create HintDb stysub discriminated.


Inductive StySubSimple : Sty -> Sty -> Prop :=
| StySubSimple_send : forall B S, StySubSimple S (send B S)
| StySubSimple_recv : forall B S, StySubSimple S (recv B S)
| StySubSimple_echoice1 : forall S1 S2, StySubSimple S1 (echoice S1 S2)
| StySubSimple_echoice2 : forall S1 S2, StySubSimple S2 (echoice S1 S2)
| StySubSimple_ichoice1 : forall S1 S2, StySubSimple S1 (ichoice S1 S2)
| StySubSimple_ichoice2 : forall S1 S2, StySubSimple S2 (ichoice S1 S2)
.
Hint Constructors StySubSimple : stysub.


Inductive StySub : Sty -> Sty -> Prop :=
| StySub_StySubSimple : forall S S', StySubSimple S S' -> StySub S S'
| StySub_mu : forall X S, StySub S (mu X S)
.
Hint Constructors StySub : stysub.
