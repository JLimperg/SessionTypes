Require Import CompleteSubstitution CompleteSubstitutionFacts Equivalence Free
  FreeFacts LibRelation LibLogic NonEquivalence SessionTypes SessionTypesInd
  Substitution SubstitutionFacts Shape Symmetry Tac Msg Var Wellformed.

(* --------------------------------------------------------------------------*)
(* Automation *)

Lemma sequiv_var_absurd_l :
  forall S X,
  ok_some S ->
  ~ sequiv (var X) S.
Proof.
  induction S using (well_founded_ind lt_Sty_mu_prefix_wf); introv Hok contra;
    inverts2 contra.
  - eapply H with (y := subst X0 (mu X0 S') S'); eauto with subst.
Qed.

Hint Extern 4 =>
  match goal with
  | H : sequiv (var ?X) ?S |- _ =>
      exfalso; apply (sequiv_var_absurd_l S X); [|assumption]
  end
.


Lemma sequiv_var_absurd_r :
  forall S X,
  ok_some S ->
  ~ sequiv S (var X).
Proof.
  introv Hok contra. apply sequiv_symmetric in contra.
  apply sequiv_var_absurd_l in contra; auto.
Qed.

Hint Extern 4 =>
  match goal with
  | H : sequiv ?S (var ?X) |- _ =>
      exfalso; apply (sequiv_var_absurd_r S X); [|assumption]
  end
.


Lemma sequiv_var_absurd_both :
  forall X Y,
  ~ sequiv (var X) (var Y).
Proof. introv H; inverts2 H. Qed.

Hint Extern 2 =>
  match goal with
  | H : sequiv (var ?X) (var ?Y) |- _ =>
      apply sequiv_var_absurd_both in H; contradiction
  end
.


Lemma sequiv_checked_ok_l :
  forall S S' XS XS',
  checked XS S ->
  checked XS' S' ->
  sequiv S S' ->
  ok XS S.
Proof. introv Hch Hch' Heq. inverts Hch; inverts Hch'; eauto. Qed.
Hint Resolve sequiv_checked_ok_l : nsequiv.

Lemma sequiv_checked_ok_r :
  forall S S' XS XS',
  checked XS S ->
  checked XS' S' ->
  sequiv S S' ->
  ok XS' S'.
Proof.
  introv Hch Hch' Heq. apply sequiv_symmetric in Heq.
  eauto using sequiv_checked_ok_l.
Qed.

Hint Extern 4 (ok ?XS ?S) =>
  match goal with
  | Heq : sequiv S ?S', Hch : checked XS S, Hch' : checked _ ?S' |- _ =>
      refine (sequiv_checked_ok_l _ _ _ _ Hch Hch' Heq)
  end
: nsequiv.

Hint Extern 4 (ok ?XS' ?S') =>
  match goal with
  | Heq : sequiv ?S S', Hch' : checked XS' S', Hch : checked _ ?S |- _ =>
      refine (sequiv_checked_ok_r _ _ _ _ Hch Hch' Heq)
  end
: nsequiv.


(* --------------------------------------------------------------------------*)
(* nsequiv -> ~ sequiv *)


Lemma nsequiv_not_sequiv :
  forall S S' XS XS',
  ok XS S ->
  ok XS' S' ->
  nsequiv S S' ->
  ~ sequiv S S'.
Proof.
  introv Hok Hok' H. induction H; introv contra; try solve
    [ inverts2 contra; auto
    | inverts2 contra; inverts Hok; inverts Hok';
      unfold not in *; eauto with nsequiv
    ].
  - apply cs_preserves_sequiv_r in contra; eauto.
    inverts2 contra; [|eauto using cs_mu_absurd].
    + apply IHnsequiv; eauto using uncs_preserves_sequiv_r with subst.
  - apply cs_preserves_sequiv_l in contra; eauto.
    inverts2 contra; [eauto using cs_mu_absurd|].
    + apply IHnsequiv; eauto using uncs_preserves_sequiv_l with subst.
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
  introv Hok Hok'. split; introv H.
  + unfold wellformed in *; eapply nsequiv_not_sequiv; eauto.
  + gen H. apply contrapose_elim. introv H. apply not_not_intro.
    apply not_nsequiv_sequiv; auto using wellformed_closed.
Qed.