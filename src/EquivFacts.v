Require Import Contractive ContractiveFacts CS CSFacts Equiv Free FreeFacts
  NonEquiv Rel Sty StyInd Subst SubstFacts Shape Tac Msg Var Wf WfFacts.
Require Import TLC.LibRelation TLC.LibLogic.


(* ------------------------------------------------------------------------- *)
(* Reflexivity *)

Inductive R_Sequiv_reflexive : Sty -> Sty -> Prop :=
| R_Sequiv_reflexive_refl :
    forall S,
    Wf S ->
    R_Sequiv_reflexive S S
| R_Sequiv_reflexive_mu1 :
    forall X S,
    Wf (subst X (mu X S) S) ->
    R_Sequiv_reflexive (mu X S) (subst X (mu X S) S)
| R_Sequiv_reflexive_mu2 :
    forall X S,
    Wf (subst X (mu X S) S) ->
    R_Sequiv_reflexive (subst X (mu X S) S) (mu X S)
.

Theorem Sequiv_reflexive :
  forall S,
  Wf S ->
  Sequiv S S.
Proof.
  intros. apply Sequiv_coind with (R := R_Sequiv_reflexive);
    [|constructor; auto].
  clear. introv H. inverts1 H; [destruct S'|..];
    try (constructor; constructor); auto with wf.
Qed.


(* ------------------------------------------------------------------------- *)
(* Symmetry *)


Theorem Sequiv_symmetric : forall S S',
  Sequiv S S' -> Sequiv S' S.
Proof with auto.
  apply clos_sym_sym. unfold inclusion. apply Sequiv_coind.
  intros S S' H.
  inversion_clear H. inversion_clear H0.
  inversion H; constructor; subst; constructor...
Qed.


(* ------------------------------------------------------------------------- *)
(* Transitivity *)


Create HintDb sequiv_trans discriminated.
Hint Resolve Sequiv_reflexive : sequiv_trans.


Inductive R_Sequiv_transitive : Sty -> Sty -> Prop :=
| R_Sequiv_transitive_intro :
    forall S T U,
    Wf S ->
    Wf T ->
    Wf U ->
    Sequiv S T ->
    Sequiv T U ->
    R_Sequiv_transitive S U
.
Hint Constructors R_Sequiv_transitive : sequiv_trans.

Lemma R_Sequiv_transitive_reflexive :
  forall S,
  Wf S ->
  R_Sequiv_transitive S S.
Proof. eauto with sequiv_trans. Qed.

Lemma Sequiv_R_Sequiv_transitive :
  forall S T,
  Wf S ->
  Wf T ->
  Sequiv S T ->
  R_Sequiv_transitive S T.
Proof. eauto with sequiv_trans. Qed.


(* TODO beautify (a lot) *)
Theorem Sequiv_transitive :
  forall S T U,
  Wf S ->
  Wf T ->
  Wf U ->
  Sequiv S T ->
  Sequiv T U ->
  Sequiv S U.
Proof.
  intros. apply Sequiv_coind with (R := R_Sequiv_transitive);
    [|eauto with sequiv_trans].
  clear. introv H. rename S' into U. inverts H.
  assert (Sequiv S (cs T)) as HSeqT  by (
    eapply cs_preserves_Sequiv_r; eauto with wf
  ).
  assert (Sequiv (cs T) U) as HTeqU by (
    eapply cs_preserves_Sequiv_l; eauto with wf
  ).
  clear H3 H4. inverts2 HSeqT; inverts2 HTeqU; subst; try solve [false].

  (* unit *)
  - auto.

  - constructor. rewrite <- HSeqT in *.
    apply Sequiv_R_Sequiv_transitive; auto with wf.

  (* send *)
  - rewrite <- H4 in H3. injection H3; intros; subst.
    constructor. apply R_Sequiv_transitive_intro with (T := S); eauto with wf.
      apply cs_preserves_Wf in H1. rewrite <- H4 in H1.
      eauto with wf.

  - constructor. rewrite <- H3 in *.
    apply R_Sequiv_transitive_intro with (T := send B S'); eauto with wf.
      rewrite H3. eauto with wf.

  (* recv *)
  - rewrite <- H4 in H3. injection H3; intros; subst.
    constructor. apply R_Sequiv_transitive_intro with (T := S); eauto with wf.
      apply cs_preserves_Wf in H1. rewrite <- H4 in H1.
      eauto with wf.

  - constructor. rewrite <- H3 in *.
    apply R_Sequiv_transitive_intro with (T := recv B S'); eauto with wf.
      rewrite H3. eauto with wf.

  (* echoice *)
  - assert (Wf (echoice S1' S2')) by (rewrite H3; eauto with wf).
    rewrite <- H4 in H3. injection H3; intros; subst.
    constructor.
    * apply R_Sequiv_transitive_intro with (T := S0); eauto with wf.
    * apply R_Sequiv_transitive_intro with (T := S3); eauto with wf.

  - assert (Wf (echoice S1' S2')) by (rewrite H3; eauto with wf).
    constructor. rewrite <- H3 in *.
    apply R_Sequiv_transitive_intro with (T := echoice S1' S2'); eauto with wf.

  (* ichoice *)
  - assert (Wf (ichoice S1' S2')) by (rewrite H3; eauto with wf).
    rewrite <- H4 in H3. injection H3; intros; subst.
    constructor.
    * apply R_Sequiv_transitive_intro with (T := S0); eauto with wf.
    * apply R_Sequiv_transitive_intro with (T := S3); eauto with wf.

  - assert (Wf (ichoice S1' S2')) by (rewrite H3; eauto with wf).
    constructor. rewrite <- H3 in *.
    apply R_Sequiv_transitive_intro with (T := ichoice S1' S2'); eauto with wf.

  (* unit *)
  - rewrite <- HTeqU in *. constructor. apply Sequiv_R_Sequiv_transitive;
      auto with wf.

  (* send *)
  - constructor. rewrite <- H3 in *.
    apply R_Sequiv_transitive_intro with (T := send B S); auto with wf.
      rewrite H3; eauto with wf.

  (* recv *)
  - constructor. rewrite <- H3 in *.
    apply R_Sequiv_transitive_intro with (T := recv B S); auto with wf.
      rewrite H3; eauto with wf.

  (* echoice *)
  - constructor. rewrite <- H3 in *.
    apply R_Sequiv_transitive_intro with (T := echoice S1 S2); auto with wf.
      rewrite H3; eauto with wf.

  (* ichoice *)
  - constructor. rewrite <- H3 in *.
    apply R_Sequiv_transitive_intro with (T := ichoice S1 S2); auto with wf.
      rewrite H3; eauto with wf.

  (* mu 1 (impossible) *)
  - exfalso; eauto with subst wf.

  (* mu 2 *)
  - constructor.
    assert (Sequiv (cs T) (mu X0 S')) as HTeqU' by auto.
    apply R_Sequiv_transitive_intro with (T := cs T);
      eauto with wf.

  (* mu 3 (impossible) *)
  - exfalso; eauto with subst wf.

  (* mu 4 (impossible) *)
  - exfalso; eauto with subst wf.
Qed.


(* ------------------------------------------------------------------------- *)
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


(* ------------------------------------------------------------------------- *)
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


(* ------------------------------------------------------------------------- *)
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
