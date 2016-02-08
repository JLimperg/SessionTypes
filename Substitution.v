Require Import SessionTypes Var.

Create HintDb subst discriminated.

Fixpoint subst (x : Var) (r : Sty) (orig : Sty) : Sty :=
  match orig with
  | unit => unit
  | send msg tail => send msg (subst x r tail)
  | recv msg tail => recv msg (subst x r tail)
  | ichoice tail1 tail2 => ichoice (subst x r tail1) (subst x r tail2)
  | echoice tail1 tail2 => echoice (subst x r tail1) (subst x r tail2)
  | mu y tail => if beq_var x y then orig else mu y (subst x r tail)
  | var y => if beq_var x y then r else orig
  end
.


(* Read: cs S S' <=> cs S = S' *)
Inductive cs : Sty -> Sty -> Prop :=
| substall_unit : cs unit unit
| substall_send : forall B S, cs (send B S) (send B S)
| substall_recv : forall B S, cs (recv B S) (recv B S)
| substall_echoice : forall S1 S2, cs (echoice S1 S2) (echoice S1 S2)
| substall_ichoice : forall S1 S2, cs (ichoice S1 S2) (ichoice S1 S2)
| substall_mu :
    forall X S csS,
    cs (subst X (mu X S) S) csS ->
    cs (mu X S) csS
| substall_var : forall X, cs (var X) (var X)
.
Hint Constructors cs : subst.
