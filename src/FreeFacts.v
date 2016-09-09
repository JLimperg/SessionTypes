Require Import Env Free Sty Subst Tac Var.

(* -------------------------------------------------------------------------- *)
(* Absurdities *)

Lemma Free_unit_absurd : forall X, Free X unit -> False.
Proof. introv H. inverts H. Qed.

Hint Extern 1 =>
  match goal with
  | H : Free _ unit |- _ =>
      apply Free_unit_absurd in H; contradiction
  end
: free.


Lemma Free_mu_absurd : forall X S, Free X (mu X S) -> False.
Proof. introv H; inverts H; auto. Qed.

Hint Extern 1 =>
  match goal with
  | H : Free ?Y (mu ?Y _) |- _ =>
      apply Free_mu_absurd in H; contradiction
  end
: free.


Lemma Closed_var_absurd :
  forall X,
  Closed (var X) -> False.
Proof. introv H. unfold Closed in H. specialize H with X. auto with free. Qed.

Hint Extern 1 =>
  match goal with
  | H : Closed (var _) |- _ =>
    apply Closed_var_absurd in H; contradiction
  end
: free.


(* -------------------------------------------------------------------------- *)
(* Inversion of Free *)


Lemma Free_inv_mu : forall X Y S, Free X (mu Y S) -> X <> Y.
Proof. introv H; inverts H; auto. Qed.

Hint Extern 1 (?X1 <> ?Y1) =>
  match goal with
  | H : Free ?X1 (mu ?Y1 ?S1) |- _ =>
      apply Free_inv_mu in H; assumption
  end
: free.


Lemma Free_inv_var : forall X Y, Free X (var Y) -> X = Y.
Proof. introv H; inverts H; auto. Qed.

Hint Extern 1 (?X1 = ?Y1) =>
  solve [apply Free_inv_var; assumption]
: free.


Ltac Free_inv_auto X S :=
  match goal with
  | H : Free X unit |- _ => inverts H
  | H : Free X (send _ S) |- _ => inverts H
  | H : Free X (recv _ S) |- _ => inverts H
  | H : Free X (echoice S _) |- _ => inverts H
  | H : Free X (echoice _ S) |- _ => inverts H
  | H : Free X (ichoice S _) |- _ => inverts H
  | H : Free X (ichoice _ S) |- _ => inverts H
  | H : Free X (mu _ S) |- _ => inverts H
  end
.

Hint Extern 4 (Free ?X ?S) =>
  Free_inv_auto X S
: free.


Hint Extern 2 (Free _ _) =>
  match goal with
  | H : Free _ _ \/ _ |- _ => decompose_or H
  | H : _ \/ Free _ _ |- _ => decompose_or H
  end
: free.


Lemma Nonfree_shortcut :
  (forall X S B, ~ Free X S -> ~ Free X (send B S)) /\
  (forall X S B, ~ Free X S -> ~ Free X (recv B S)) /\
  (forall X S1 S2,  ~ Free X S1 -> ~ Free X S2 -> ~ Free X (echoice S1 S2)) /\
  (forall X S1 S2,  ~ Free X S1 -> ~ Free X S2 -> ~ Free X (ichoice S1 S2)) /\
  (forall X Y S, ~ Free X S -> ~ Free X (mu Y S)).
Proof.
  splits; auto with free;
    introv HS1 HS2 contra; inverts1 contra; decompose_or contra; auto.
Qed.

Hint Extern 2 (~ Free _ _) => apply Nonfree_shortcut : free.


(* -------------------------------------------------------------------------- *)
(* Closed automation *)


Lemma Closed_inv :
  forall S S',
  StySubSimple S S' ->
  Closed S' ->
  Closed S.
Proof.
  introv sub; inverts sub; introv H; unfold Closed in *; try split; intro Y;
  specialize H with Y; contradict H; auto with free.
Qed.

Hint Extern 2 (Closed ?S) =>
  match goal with
  | H : Closed _ |- _ =>
      solve [apply (Closed_inv S) in H; [assumption | auto with stysub]]
  end
: free.


(* -------------------------------------------------------------------------- *)
(* Non-automation lemmas *)


Lemma Free_dec : forall S X, {Free X S} + {~ Free X S}.
Proof.
  intros S X. induction S;
    repeat (
      match goal with
      | H : {_} + {_} |- _ => decompose sum H; clear H
      end
    );
    auto with free;
    destruct (eq_Var_dec X v); subst; auto with free.
Defined.
