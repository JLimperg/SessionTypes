Require Import Env Free Sty Subst Tac Var Wf.

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


Lemma Closed_shortcut :
  (forall S B, Closed (send B S) -> Closed S) /\
  (forall S B, Closed (recv B S) -> Closed S) /\
  (forall S1 S2, Closed (echoice S1 S2) -> Closed S1 /\ Closed S2) /\
  (forall S1 S2, Closed (ichoice S1 S2) -> Closed S1 /\ Closed S2).
Proof.
  splits; introv H; unfold Closed in *; try split; intro Y; specialize H with Y;
    contradict H; auto with free.
Qed.

Hint Extern 2 (Closed ?S) =>
  let solve_using H :=
    apply Closed_shortcut in H; try decompose_and H; assumption
  in
  match goal with
  | H : Closed (send _ S) |- _ => solve_using H
  | H : Closed (recv _ S) |- _ => solve_using H
  | H : Closed (echoice S _) |- _ => solve_using H
  | H : Closed (echoice _ S) |- _ => solve_using H
  | H : Closed (ichoice S _) |- _ => solve_using H
  | H : Closed (ichoice _ S) |- _ => solve_using H
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
    destruct (eq_var_dec X v); subst; auto with free.
Defined.


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
Hint Resolve wellformed_closed : free.


Lemma eta_irrelevant_helper :
  forall (P : Prop),
  (forall B S,
    (forall X, Free X (send B S) -> P) ->
    (forall X, Free X S -> P)) /\
  (forall B S,
    (forall X, Free X (recv B S) -> P) ->
    (forall X, Free X S -> P)) /\
  (forall S1 S2,
    (forall X, Free X (echoice S1 S2) -> P) ->
    (forall X, Free X S1 -> P) /\ (forall X, Free X S2 -> P)) /\
  (forall S1 S2,
    (forall X, Free X (ichoice S1 S2) -> P) ->
    (forall X, Free X S1 -> P) /\ (forall X, Free X S2 -> P)) /\
  (forall Y S,
    (forall X, Free X (mu Y S) -> P) ->
    (forall X, X <> Y -> Free X S -> P)).
Proof. intuition (eauto with free). Qed.
