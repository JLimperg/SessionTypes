Require Import Msg Tac TLC.LibLogic Var.

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
  pose proof eq_Msg_dec. pose proof eq_var_dec. decide equality; auto.
Defined.

Fixpoint beq_Sty (S T : Sty) : bool :=
  match (S, T) with
  | (unit, unit) => true
  | (send B S', send B' T') => andb (beq_msg B B') (beq_Sty S' T')
  | (recv B S', recv B' T') => andb (beq_msg B B') (beq_Sty S' T')
  | (echoice S1 S2, echoice T1 T2) => andb (beq_Sty S1 T1) (beq_Sty S2 T2)
  | (ichoice S1 S2, ichoice T1 T2) => andb (beq_Sty S1 T1) (beq_Sty S2 T2)
  | (mu X S', mu Y T') => andb (beq_var X Y) (beq_Sty S' T')
  | (var X, var Y) => beq_var X Y
  | _ => false
  end
.

Global Instance Sty_Inhab : Inhab Sty.
Proof. constructor. exists unit. trivial. Qed.
