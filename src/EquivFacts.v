Require Import Contractive ContractiveFacts CS CSFacts Equiv Free FreeFacts
  NonEquiv Sty StyInd Subst SubstFacts Shape Symmetry Tac Msg Var Wf.
Require Import TLC.LibRelation TLC.LibLogic.

(* --------------------------------------------------------------------------*)
(* Automation *)

Lemma Sequiv_var_absurd_l :
  forall S X,
  Contractive S ->
  ~ Sequiv (var X) S.
Proof.
  induction S using (well_founded_ind lt_Sty_mu_prefix_wf);
    introv Hcontr contra; inverts2 contra.
  - eapply H with (y := subst X0 (mu X0 S') S'); eauto with contractive subst.
Qed.

Hint Extern 4 =>
  match goal with
  | H : Sequiv (var ?X) ?S |- _ =>
      exfalso; apply (Sequiv_var_absurd_l S X); [|assumption]
  end
.


Lemma Sequiv_var_absurd_r :
  forall S X,
  Contractive S ->
  ~ Sequiv S (var X).
Proof. introv Hok contra. apply Sequiv_symmetric in contra. auto. Qed.

Hint Extern 4 =>
  match goal with
  | H : Sequiv ?S (var ?X) |- _ =>
      exfalso; apply (Sequiv_var_absurd_r S X); [|assumption]
  end
.


(* --------------------------------------------------------------------------*)
(* NSequiv -> ~ Sequiv *)


Lemma NSequiv_not_Sequiv :
  forall S S',
  Contractive S ->
  Contractive S' ->
  NSequiv S S' ->
  ~ Sequiv S S'.
Proof.
  introv Hok Hok' H. induction H; introv contra; try solve
    [ inverts2 contra; auto
    | inverts2 contra; inverts Hok; inverts Hok';
      unfold not in *; eauto with nsequiv
    ].
  - apply cs_preserves_Sequiv_r in contra; inverts2 contra;
    [apply IHNSequiv|..];
    auto using uncs_preserves_Sequiv_r with contractive subst.
  - apply cs_preserves_Sequiv_l in contra; inverts2 contra;
    [|apply IHNSequiv|..];
    auto using uncs_preserves_Sequiv_l with contractive subst.
Qed.


(* --------------------------------------------------------------------------*)
(* ~ NSequiv -> Sequiv *)


Inductive R_not_NSequiv_Sequiv : Sty -> Sty -> Prop :=
| R_not_NSequiv_Sequiv_intro :
    forall S S',
    Closed S ->
    Closed S' ->
    ~ NSequiv S S' ->
    R_not_NSequiv_Sequiv S S'
.
Hint Constructors R_not_NSequiv_Sequiv : nsequiv.


Lemma not_NSequiv_Sequiv' :
  forall S S',
  R_not_NSequiv_Sequiv S S' ->
  Sequiv_gen R_not_NSequiv_Sequiv S S'.
Proof.
  introv H. inverts H as Hcl Hcl' H. destruct S; destruct S'; try solve
    [ exfalso; apply H; constructor; intro; discriminate ];
    try match goal with
    | B : Msg, B' : Msg |- _ =>
      destruct (eq_Msg_dec B B'); [subst | exfalso; auto with nsequiv]
    end;
    auto 8 with free nsequiv.
Qed.

Lemma not_NSequiv_Sequiv :
  forall S S',
  Closed S ->
  Closed S' ->
  ~ NSequiv S S' ->
  Sequiv S S'.
Proof.
  intros. apply Sequiv_coind with (R := R_not_NSequiv_Sequiv);
  auto using not_NSequiv_Sequiv' with nsequiv.
Qed.


(* --------------------------------------------------------------------------*)
(* NSequiv <-> ~ Sequiv *)

Lemma NSequiv_iff_not_Sequiv :
  forall S S',
  Wf S ->
  Wf S' ->
  (NSequiv S S' <-> ~ Sequiv S S').
Proof.
  introv Hok Hok'. split; introv H; unfold Wf in *.
  + eapply NSequiv_not_Sequiv; eauto.
  + gen H. apply contrapose_elim. introv H. apply not_not_intro.
    apply not_NSequiv_Sequiv; auto.
Qed.
