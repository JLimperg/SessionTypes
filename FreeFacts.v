Require Import Env Free SessionTypes Tac Var Wellformed.


Hint Extern 2 =>
  let decomp H :=
    match type of H with
    | _ \/ _ =>
        decompose sum H; clear H
    | _ =>
        idtac
    end
  in
  match goal with
  | H : Free _ _ |- _ =>
      inverts1 H; decomp H
  end
: free.


Lemma Free_dec : forall S X, {Free X S} + {~ Free X S}.
Proof.
  intros S X. unfold not. induction S;
    repeat (
      match goal with
      | H : {_} + {_} |- _ => decompose sum H; clear H
      end
    ); auto with free.

    destruct (eq_var_dec X v); subst.
      right. introv H. inverts H. auto.
      auto with free.

    destruct (eq_var_dec X v); subst.
      auto with free.
      right. intro H. inverts H. exfalso; auto.
Qed.


(* TODO beautify *)
Lemma ok_checked_free :
  forall S X XS,
  ok XS S \/ checked XS S ->
  ~ env_mem X XS ->
  ~ Free X S.
Proof with (eauto with free).
  induction S; introv Hok Henv; unfold not in *.
    eauto with free.

    inverts1 Hok.
      inverts1 Hok. introv H. eapply IHS...
      inverts2 Hok. introv H. eapply IHS...
    inverts1 Hok.
      inverts1 Hok. introv H. eapply IHS...
      inverts2 Hok. introv H. eapply IHS...
    inverts1 Hok.
      inverts1 Hok. introv H. inverts2 H; [eapply IHS1 | eapply IHS2]...
      inverts2 Hok. introv H. inverts2 H; [eapply IHS1 | eapply IHS2]...
    inverts1 Hok.
      inverts1 Hok. introv H. inverts2 H; [eapply IHS1 | eapply IHS2]...
      inverts2 Hok. introv H. inverts2 H; [eapply IHS1 | eapply IHS2]...
    inverts1 Hok.
      inverts1 Hok. introv H. inverts H. eapply IHS...
      introv H. apply env_mem_add in H; auto.

      inverts2 Hok. introv H. inverts H. eapply IHS...
      introv H. apply env_mem_add in H; auto.
    inverts1 Hok.
      inverts1 Hok.
      inverts1 Hok.
        introv H. inverts1 H. auto.
        inverts1 Hok.
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
