Require Import Sty Shape Tac.

Lemma shape_dec :
  forall S sh, {shape S = sh} + {shape S <> sh}.
Proof. decide equality. Qed.


Definition shape_prop (sh : Shape) (S : Sty) : Prop :=
  match sh with
  | unitS => S = unit
  | sendS => exists B S', S = send B S'
  | recvS => exists B S', S = recv B S'
  | echoiceS => exists S1 S2, S = echoice S1 S2
  | ichoiceS => exists S1 S2, S = ichoice S1 S2
  | muS => exists X S', S = mu X S'
  | varS => exists X, S = var X
  end
.


Lemma shape_inv_helper S sh (p : shape S = sh) : shape_prop sh S.
Proof. destruct sh; destruct S; simpl; try discriminate; iauto. Qed.


Ltac shape_inv H :=
  let inv S sh p :=
    let H := fresh in
    pose proof (shape_inv_helper S sh p) as H;
    simpl in H;
    try (decompose_ex H);
    rewrite H in *;
    clear H p
  in
    match type of H with
    | shape ?S = ?sh => inv S sh H
    | ?sh = shape ?S => symmetry in H; shape_inv H
    end
.


Ltac shape_inv_auto :=
  match goal with
  | H : shape _ = _ |- _ => shape_inv H
  | H : _ = shape _ |- _ => shape_inv H
  end;
  try shape_inv_auto
.
