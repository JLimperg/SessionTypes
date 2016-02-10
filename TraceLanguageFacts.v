Require Import Relations.
Require Import Map Rel SessionTypes Substitution TraceLanguage Var Wellformed.

Inductive R_eq_tl_reflexive : relation Tl :=
| R_eq_tl_reflexive_intro : forall t, R_eq_tl_reflexive t t
.
Hint Constructors R_eq_tl_reflexive : tl.

Lemma eq_tl_refl : reflexive Tl eq_tl.
Proof with (auto with tl).
  unfold reflexive. intros t. apply eq_tl_coind with (R := R_eq_tl_reflexive)...
    clear t. intros t t' H. inversion_clear H. clear t. rename t' into t.
    destruct t...
Qed.

Lemma eq_tl_sym : symmetric Tl eq_tl.
Proof with (auto with tl rel).
  apply clos_sym_sym. unfold inclusion. apply eq_tl_coind. intros t t' H.
  inversion_clear H. inversion_clear H0. inversion_clear H...
Qed.

Lemma eq_tl_trans : transitive Tl eq_tl.
Proof with (eauto with tl rel).
  apply clos_trans_trans. unfold inclusion. apply eq_tl_coind. intros t t' H.
  induction H as [ | x y z H1 IH1 H2 IH2].
    inversion_clear H. inversion_clear H0...

    inversion IH1.
      rewrite <- H0 in IH2. inversion IH2...
      rewrite <- H3 in IH2. inversion IH2...
      rewrite <- H3 in IH2. inversion IH2...
      rewrite <- H4 in IH2. inversion IH2...
      rewrite <- H4 in IH2. inversion IH2...
Qed.

Add Relation Tl eq_tl
  reflexivity proved by eq_tl_refl
  symmetry proved by eq_tl_sym
  transitivity proved by eq_tl_trans
  as eq_tl'.

Inductive R_tl_deterministic : relation Tl :=
| R_tl_deterministic_intro :
    forall L L',
    (exists eta S, tl eta S L /\ tl eta S L') ->
    R_tl_deterministic L L'
.
Hint Constructors R_tl_deterministic : tl.

Lemma R_tl_deterministic_lemma :
  (forall L L', R_tl_deterministic L L' -> eq_tl_gen R_tl_deterministic L L') ->
  (forall eta S L L',
   tl eta S L ->
   tl eta S L' ->
   eq_tl L L').
Proof with (eauto with tl).
  intros. apply eq_tl_coind with (R := R_tl_deterministic)...
Qed.

Lemma tl_deterministic :
  forall eta S L L',
  tl eta S L ->
  tl eta S L' ->
  eq_tl L L'.
Proof with (eauto with tl).
  apply R_tl_deterministic_lemma. intros L L' H.
  inversion_clear H. inversion_clear H0. inversion_clear H.
  destruct H0 as [HL HL']. inversion_clear HL. inversion_clear HL'.
  rename H into HL. rename H0 into HL'. rename x into eta. rename x0 into S.
  generalize dependent L'. generalize dependent L. generalize dependent eta.
  induction S; intros eta L HL L' HL';
    try (solve [inversion_clear HL; inversion_clear HL'; constructor; eauto with tl]).

    inversion_clear HL. inversion_clear HL'. apply IHS with (eta := (eta_override eta v L)).
Abort.


Inductive R_subst_tl_1 (X : Var) (T : Sty) (LT : Tl) :
  (Var -> Tl) -> Sty -> Tl -> Prop :=
| R_subst_tl_1_intro :
    forall eta S L,
    (forall eta, tl eta T LT) ->
    tl (eta_override eta X LT) S L ->
    R_subst_tl_1 X T LT eta (subst X T S) L
.
Hint Constructors R_subst_tl_1 : tl.

Lemma R_subst_tl_1_lemma :
  forall X T LT,
  (forall eta S L,
   R_subst_tl_1 X T LT eta S L ->
   tl_gen (fun eta S L => (R_subst_tl_1 X T LT) eta S L \/ tl eta S L) eta S L)
  -> (forall eta S L,
      (forall eta, tl eta T LT) ->
      tl (eta_override eta X LT) S L ->
      tl eta (subst X T S) L).
Proof with (auto with tl).
  intros X T LT H eta S L H1 H2.
  apply tl_coind_ext with (R := R_subst_tl_1 X T LT) (R' := tl)...
    intros eta' S' L' H'. inversion H'...
Qed.

Inductive R_subst_tl_2 (X : Var) (T : Sty) (LT : Tl) :
  (Var -> Tl) -> Sty -> Tl -> Prop :=
| R_subst_tl_2_intro :
    forall eta S L,
    (forall eta, tl eta T LT) ->
    tl eta (subst X T S) L ->
    R_subst_tl_2 X T LT (eta_override eta X LT) S L
.
Hint Constructors R_subst_tl_2 : tl.

Lemma R_subst_tl_2_lemma :
  forall X T LT,
  (forall eta S L,
   R_subst_tl_2 X T LT eta S L ->
   tl_gen (fun eta S L => (R_subst_tl_2 X T LT) eta S L \/ tl eta S L) eta S L)
  -> (forall eta S L,
      (forall eta, tl eta T LT) ->
      tl eta (subst X T S) L ->
      tl (eta_override eta X LT) S L).
Proof with (auto with tl).
  intros X T LT H eta S L H1 H2.
  apply tl_coind_ext with (R := R_subst_tl_2 X T LT) (R' := tl)...
    intros eta' S' L' H'. inversion H'...
Qed.

Inductive R_tl_wf_eta_irrelevant : (Var -> Tl) -> Sty -> Tl -> Prop :=
| R_tl_wf_eta_irrelevant_intro1 :
    forall eta S L,
    wellformed S ->
    (exists eta, tl eta S L) ->
    R_tl_wf_eta_irrelevant eta S L
| R_tl_wf_eta_irrelevant_intro2 :
    forall X eta S L,
    (forall T, wellformed T -> wellformed (subst X T S)) ->
    (exists eta, tl eta (mu X S) L) ->
    R_tl_wf_eta_irrelevant eta S L
.
Hint Constructors R_tl_wf_eta_irrelevant : tl.

Lemma R_tl_wf_eta_irrelevant_lemma :
  (forall eta S L, R_tl_wf_eta_irrelevant eta S L -> tl eta S L) ->
  (forall eta S L,
   wellformed S ->
   (exists eta, tl eta S L) ->
   tl eta S L).
Proof. intros H eta S L Hwf Hex. auto with tl. Qed.

Lemma tl_wf_eta_irrelevant :
  forall eta S L,
  wellformed S ->
  (exists eta, tl eta S L) ->
  tl eta S L.
Proof with (eauto with tl wf).
Abort.

Lemma subst_tl :
  forall X T LT eta S L,
  (forall eta, tl eta T LT) ->
  (tl (eta_override eta X LT) S L <-> tl eta (subst X T S) L).
Proof with (auto with tl env).
  split; intros H1.
    (* -> *)
    apply R_subst_tl_1_lemma with (LT := LT)...
    clear eta S L H H1. intros eta S L H.
    inversion_clear H. inversion_clear H1. destruct S0; inversion_clear H; simpl...
      (* mu *)
      destruct (beq_var X v) eqn:HXv.
        rewrite override_overwrite in H1... rewrite beq_var_sym...

        constructor. constructor. constructor...
          rewrite override_exchange in H1...
          rewrite beq_var_sym...

      (* var *)
      destruct (beq_var X v) eqn:HXv; unfold override; rewrite beq_var_sym;
        rewrite HXv...
        specialize H0 with (eta := eta). inversion_clear H0.
        apply tl_expansion_2...

    (* <- *)
    apply R_subst_tl_2_lemma with (T := T)...
    clear eta S L H H1. intros eta S L H.
    inversion_clear H. inversion_clear H1. destruct S;
      simpl in H; try (solve [inversion_clear H; auto with tl env]).

      (* mu *)
      destruct (beq_var X v) eqn:HXv; constructor; inversion_clear H.
        right. rewrite override_overwrite... rewrite beq_var_sym...
        left. rewrite override_exchange... rewrite beq_var_sym...

      (* var *)
      destruct (beq_var X v) eqn:Hxv.
        unfold override.
        assert ((fun x : Var => if beq_var x X then LT else eta0 x) v = L) as H'.
          rewrite beq_var_sym. rewrite Hxv.
Abort.
