Require Import Env Free SessionTypes Tac Var Wellformed.

Lemma free_inv_unit : forall (P : Prop) X, Free X unit -> P.
Proof. introv H. inversion H. Qed.

Hint Extern 0 =>
  match goal with
  | H : Free ?Y unit |- _ =>
      apply free_inv_unit with (X := Y); assumption
  end
: free.


Lemma nonfree_unit : forall X, ~ Free X unit.
Proof. auto with free. Qed.

Hint Extern 0 (~ Free _ unit) =>
  apply nonfree_unit
: free.


Lemma free_inv_mu : forall (P : Prop) X S, Free X (mu X S) -> P.
Proof. introv H; inversion H; exfalso; auto. Qed.

Hint Extern 0 =>
  match goal with
  | H : Free ?Y (mu ?Y ?T) |- _ =>
      apply free_inv_mu with (X := Y) (S := T); assumption
  end
: free.


Lemma free_inv_mu2 : forall X Y S, Free X (mu Y S) -> X <> Y.
Proof. introv H; inverts H; auto. Qed.

Hint Extern 0 (?X1 <> ?Y1) =>
  match goal with
  | H : Free ?X1 (mu ?Y1 ?S1) |- _ =>
      apply free_inv_mu2; assumption
  end
: free.


Lemma nonfree_inv_mu : forall X S, ~ Free X (mu X S).
Proof. auto with free. Qed.

Hint Extern 0 (~ Free ?X (mu ?X _)) =>
  apply nonfree_inv_mu
: free.


Lemma free_inv_var : forall X Y, Free X (var Y) -> X = Y.
Proof. introv H; inverts H; auto. Qed.

Hint Extern 0 (?X1 = ?Y1) =>
  solve [apply free_inv_var; assumption]
: free.


Lemma nonfree_inv_var : forall X Y, X <> Y -> ~ Free X (var Y).
Proof. auto with free. Qed.

Hint Extern 0 (~ Free ?X (var ?Y)) =>
  solve [apply nonfree_inv_var; assumption]
: free.


Ltac free_inv_auto X S :=
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

Hint Extern 4 (Free ?X ?S) => free_inv_auto X S.


Hint Extern 3 (Free _ _) =>
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


Lemma Free_dec : forall S X, {Free X S} + {~ Free X S}.
Proof.
  intros S X. induction S;
    repeat (
      match goal with
      | H : {_} + {_} |- _ => decompose sum H; clear H
      end
    );
    auto with free;
    destruct (eq_var_dec X v); subst; auto with free.
Qed.


Lemma ok_checked_free :
  forall S X XS,
  ok XS S \/ checked XS S ->
  ~ env_mem X XS ->
  ~ Free X S.
Proof.
  induction S; introv Hok Henv; decompose_or_auto;
    auto with free;
    match goal with
    | |- context [var _]     => idtac
    | Hok : ok _ _      |- _ => inverts1 Hok
    | Hok : checked _ _ |- _ => inverts2 Hok
    end; eauto 6 with free.

    introv H; inverts H; eapply IHS; eauto with free;
    introv H; apply env_mem_add in H; auto.

    introv H; inverts H; eapply IHS; eauto with free;
    introv H; apply env_mem_add in H; auto.

    inverts1 Hok.

    inverts1 Hok.
      introv H. inverts1 H. auto.
      inverts Hok.
Qed.


Lemma ok_free :
  forall S X XS,
  ok XS S ->
  ~ env_mem X XS ->
  ~ Free X S.
Proof. intros. eapply ok_checked_free; eauto. Qed.


Lemma checked_free :
  forall S X XS,
  checked XS S ->
  ~ env_mem X XS ->
  ~ Free X S.
Proof. intros. eapply ok_checked_free; eauto. Qed.


Lemma wellformed_closed : forall S, wellformed S -> Closed S.
Proof.
  unfold wellformed. unfold Closed. intros S Hwf X. eapply ok_free;
    eauto with env.
Qed.
