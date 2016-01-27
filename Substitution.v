Require Import SessionTypes Var.

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


Fixpoint substall (S : Sty) : Sty :=
  match S with
  | unit => unit
  | send _ _ => S
  | recv _ _ => S
  | ichoice _ _ => S
  | echoice _ _ => S
  | mu X S' => subst X S (substall S')
  | var _ => S
  end
.
