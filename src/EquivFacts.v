Require Import Contractive ContractiveFacts CS CSFacts Equiv Free FreeFacts
  NonEquiv Sty StyInd Subst SubstFacts Shape Symmetry Tac Msg Var Wf.
Require Import TLC.LibRelation TLC.LibLogic.

(* --------------------------------------------------------------------------*)
(* Automation *)

Lemma sequiv_var_absurd_l :
  forall S X,
  Contractive S ->
  ~ sequiv (var X) S.
Proof.
  induction S using (well_founded_ind lt_Sty_mu_prefix_wf);
    introv Hcontr contra; inverts2 contra.
  - eapply H with (y := subst X0 (mu X0 S') S'); eauto with contractive subst.
Qed.

Hint Extern 4 =>
  match goal with
  | H : sequiv (var ?X) ?S |- _ =>
      exfalso; apply (sequiv_var_absurd_l S X); [|assumption]
  end
.


Lemma sequiv_var_absurd_r :
  forall S X,
  Contractive S ->
  ~ sequiv S (var X).
Proof. introv Hok contra. apply sequiv_symmetric in contra. auto. Qed.

Hint Extern 4 =>
  match goal with
  | H : sequiv ?S (var ?X) |- _ =>
      exfalso; apply (sequiv_var_absurd_r S X); [|assumption]
  end
.


(* --------------------------------------------------------------------------*)
(* nsequiv -> ~ sequiv *)


Lemma nsequiv_not_sequiv :
  forall S S',
  Contractive S ->
  Contractive S' ->
  nsequiv S S' ->
  ~ sequiv S S'.
Proof.
  introv Hok Hok' H. induction H; introv contra; try solve
    [ inverts2 contra; auto
    | inverts2 contra; inverts Hok; inverts Hok';
      unfold not in *; eauto with nsequiv
    ].
  - apply cs_preserves_sequiv_r in contra; inverts2 contra;
    [apply IHnsequiv|..];
    auto using uncs_preserves_sequiv_r with contractive subst.
  - apply cs_preserves_sequiv_l in contra; inverts2 contra;
    [|apply IHnsequiv|..];
    auto using uncs_preserves_sequiv_l with contractive subst.
Qed.


(* --------------------------------------------------------------------------*)
(* ~ nsequiv -> sequiv *)


Inductive R_not_nsequiv_sequiv : Sty -> Sty -> Prop :=
| R_not_nsequiv_sequiv_intro :
    forall S S',
    Closed S ->
    Closed S' ->
    ~ nsequiv S S' ->
    R_not_nsequiv_sequiv S S'
.
Hint Constructors R_not_nsequiv_sequiv : nsequiv.


Lemma not_nsequiv_sequiv' :
  forall S S',
  R_not_nsequiv_sequiv S S' ->
  sequiv_gen R_not_nsequiv_sequiv S S'.
Proof.
  introv H. inverts H as Hcl Hcl' H. destruct S; destruct S'; try solve
    [ exfalso; apply H; constructor; intro; discriminate ];
    try match goal with
    | B : Msg, B' : Msg |- _ =>
      destruct (eq_Msg_dec B B'); [subst | exfalso; auto with nsequiv]
    end;
    auto 8 with free nsequiv.
Qed.

Lemma not_nsequiv_sequiv :
  forall S S',
  Closed S ->
  Closed S' ->
  ~ nsequiv S S' ->
  sequiv S S'.
Proof.
  intros. apply sequiv_coind with (R := R_not_nsequiv_sequiv);
  auto using not_nsequiv_sequiv' with nsequiv.
Qed.


(* --------------------------------------------------------------------------*)
(* nsequiv <-> ~ sequiv *)

Lemma nsequiv_not_sequiv_iff :
  forall S S',
  wellformed S ->
  wellformed S' ->
  (nsequiv S S' <-> ~ sequiv S S').
Proof.
  introv Hok Hok'. split; introv H; unfold wellformed in *.
  + eapply nsequiv_not_sequiv; eauto.
  + gen H. apply contrapose_elim. introv H. apply not_not_intro.
    apply not_nsequiv_sequiv; auto.
Qed.