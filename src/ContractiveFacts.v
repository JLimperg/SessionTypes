Require Import Contractive Sty Shape.

(******************************************************************************)
(* Automation *)


Hint Extern 2 (Contractive ?S) =>
  let inv H := solve [inversion H; assumption] in
  match goal with
  | H : Contractive (send _ S) |- _ => inv H
  | H : Contractive (recv _ S) |- _ => inv H
  | H : Contractive (echoice S _) |- _ => inv H
  | H : Contractive (echoice _ S) |- _ => inv H
  | H : Contractive (ichoice S _) |- _ => inv H
  | H : Contractive (ichoice _ S) |- _ => inv H
  | H : Contractive (mu _ S) |- _ => inv H
  end
: contractive.


Hint Extern 2 (shape ?S <> varS) =>
  match goal with
  | H : Contractive (mu _ S) |- _ => solve [inversion H; assumption]
  end
: contractive.