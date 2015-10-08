Require Import Env List List1 Morphisms Msg Program Relations.Relation_Definitions
  Relations.Relation_Operators Shape TLC.LibTactics Var Vars.
Require Setoid.
Require Program.Basics.
Require Program.Subset.
Require Program.Tactics.
Require Program.Wf.
Require Recdef.
Import ListNotations.

Create HintDb styc discriminated.

Module StyC.

Inductive Sty : Type :=
| unit : Sty
| send : Msg -> Sty -> Sty
| recv : Msg -> Sty -> Sty
| echoice : Sty -> Sty -> Sty
| ichoice : Sty -> Sty -> Sty
| mu : Vars -> Sty -> Sty
| var : Var -> Sty
.

Fixpoint subst (x : Var) (r orig : Sty) : Sty :=
  match orig with
  | unit => unit
  | send msg tail => send msg (subst x r tail)
  | recv msg tail => recv msg (subst x r tail)
  | echoice tail1 tail2 => echoice (subst x r tail1) (subst x r tail2)
  | ichoice tail1 tail2 => ichoice (subst x r tail1) (subst x r tail2)
  | mu ys tail => if In_Vars_dec x ys then orig else mu ys (subst x r tail)
  | var y => if beq_var x y then r else orig
  end
.

Fixpoint substc (xs : list Var) (S : Sty) :=
  match xs with
  | [] => S
  | x :: xs' => subst x (mu (list_to_list1 x xs') S) (substc xs' S)
  end
.

Definition shape (S : Sty) : Shape :=
  match S with
  | unit => unitS
  | send _ _ => sendS
  | recv _ _ => recvS
  | echoice _ _ => echoiceS
  | ichoice _ _ => ichoiceS
  | mu _ _ => muS
  | var _ => varS
  end
.

End StyC.
