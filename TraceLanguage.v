Require Import SessionTypes Wellformed Relations.Relation_Definitions
  Relations.Relation_Operators Rel Logic.FunctionalExtensionality Msg Var.
Require Setoid.

Create HintDb tl discriminated.

CoInductive Tl :=
| tl_unit : Tl                (* {epsilon} *)
| tl_send : Msg -> Tl -> Tl   (* {!B} . L *)
| tl_recv : Msg -> Tl -> Tl   (* {?B} . L *)
| tl_echoice : Tl -> Tl -> Tl (* {?0} . L_1 \union {?1} . L_2 *)
| tl_ichoice : Tl -> Tl -> Tl (* {!0} . L_1 \union {!1} . L_2 *)
.
Hint Constructors Tl : tl.

Inductive eq_tl_gen (R : Tl -> Tl -> Prop) : Tl -> Tl -> Prop :=
| eq_tl_gen_unit :
    eq_tl_gen R tl_unit tl_unit
| eq_tl_gen_send :
    forall B tl tl',
    R tl tl' ->
    eq_tl_gen R (tl_send B tl) (tl_send B tl')
| eq_tl_gen_recv :
    forall B tl tl',
    R tl tl' ->
    eq_tl_gen R (tl_recv B tl) (tl_recv B tl')
| eq_tl_gen_echoice :
    forall tl1 tl2 tl1' tl2',
    R tl1 tl1' ->
    R tl2 tl2' ->
    eq_tl_gen R (tl_echoice tl1 tl2) (tl_echoice tl1' tl2')
| eq_tl_gen_ichoice :
    forall tl1 tl2 tl1' tl2',
    R tl1 tl1' ->
    R tl2 tl2' ->
    eq_tl_gen R (tl_ichoice tl1 tl2) (tl_ichoice tl1' tl2')
.
Hint Constructors eq_tl_gen : tl.

CoInductive eq_tl : relation Tl :=
| eq_tl_fold : forall t t', eq_tl_gen eq_tl t t' -> eq_tl t t'.
Hint Constructors eq_tl : tl.

Lemma eq_tl_coind :
  forall (R : Tl -> Tl -> Prop),
  (forall t t', R t t' -> eq_tl_gen R t t') ->
  (forall t t', R t t' -> eq_tl t t').
Proof with eauto.
  cofix CIH. intros R HRfp t t' HRtt'. apply HRfp in HRtt'.
  inversion HRtt'; constructor; constructor; eapply CIH...
Qed.

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

Definition override {a b : Type} (beq : a -> a -> bool) (f : a -> b) (y : a) (y' : b) :=
  fun x => if beq x y then y' else f x.
Hint Unfold override : tl.

Notation eta_override := (override beq_var).

Lemma override_exchange :
  forall A B beq f (y z : A) (y' z' : B),
  (forall a b : A, a = b <-> beq a b = true) ->
  beq y z = false ->
  override beq (override beq f z z') y y' =
  override beq (override beq f y y') z z'.
Proof with auto.
  intros A B beq f y y' z z' Hbeq Hyneqz. unfold not in Hyneqz. unfold override.
  apply functional_extensionality. intros x.
  destruct (beq x y) eqn:Hxy.
    apply Hbeq in Hxy. rewrite Hxy. rewrite Hyneqz...
    destruct (beq x y')...
Qed.

Lemma override_overwrite :
  forall A B beq f (y z : A) (y' z' : B),
  (forall a b : A, a = b <-> beq a b = true) ->
  beq y z = true ->
  override beq (override beq f z z') y y' = override beq f y y'.
Proof with auto.
  intros A B beq f y z y' z' Hbeq Hyeqz. unfold override.
  apply functional_extensionality. intros x. destruct (beq x y) eqn:Hxy...
    apply Hbeq in Hyeqz. rewrite <- Hyeqz. rewrite Hxy...
Qed.

(*
Justification for this definition:

(eta, S, L) in tl :<-> L_eta(S) = L.

Thus:
  - (eta, unit, {epsilon}) in tl forall eta
  - (eta, !B.S, {!B} . L) in tl iff (eta, S, L) in tl
  - (eta, ?B.S, {?B} . L) in tl iff (eta, S, L) in tl
  - (eta, S1 echoice S2, {?0} . L1 union {?1} . L2) in tl
      iff (eta, S1, L1) in tl and (eta, S2, L2) in tl
  - (eta, S1 ichoice S2, {!0} . L1 union {!1} . L2) in tl
      iff (eta, S1, L1) in tl and (eta, S2, L2) in tl
  - (eta, mu X.S, L) in tl
      iff L = L_eta(mu X.S)
      iff L = L_eta[X -> L_eta(mu X.S)](S)
      iff L = L_eta[X -> L](S)
      iff (eta[X -> L], S, L) in lt
  - (eta, X, eta(X)) in tl

The derivation rule for mu is the only one that may lead to an infinite
derivation; for all others, S is decreasing.

By taking the gfp of tl_gen, we get
L_eta(mu X.S) = gfp(LX => L_eta[X -> LX](S)). (??)
*)
Inductive tl_gen tl : (Var -> Tl) -> Sty -> Tl -> Prop :=
| tl_gen_unit :
    forall eta,
    tl_gen tl eta unit tl_unit
| tl_gen_send :
    forall eta S B L,
    tl eta S L ->
    tl_gen tl eta (send B S) (tl_send B L)
| tl_gen_recv :
    forall eta S B L,
    tl eta S L ->
    tl_gen tl eta (recv B S) (tl_recv B L)
| tl_gen_echoice :
    forall eta S1 S2 L1 L2,
    tl eta S1 L1 ->
    tl eta S2 L2 ->
    tl_gen tl eta (echoice S1 S2) (tl_echoice L1 L2)
| tl_gen_ichoice :
    forall eta S1 S2 L1 L2,
    tl eta S1 L1 ->
    tl eta S2 L2 ->
    tl_gen tl eta (ichoice S1 S2) (tl_ichoice L1 L2)
| tl_gen_mu :
    forall eta X S L,
    tl (eta_override eta X L) S L ->
    tl_gen tl eta (mu X S) L
| tl_gen_var :
    forall eta X,
    tl_gen tl eta (var X) (eta X)
.
Hint Constructors tl_gen : tl.

CoInductive tl : (Var -> Tl) -> Sty -> Tl -> Prop :=
| tl_fold : forall eta S L, tl_gen tl eta S L -> tl eta S L
.
Hint Constructors tl : tl.

Lemma tl_coind : forall R,
  (forall eta S L, R eta S L -> tl_gen R eta S L) ->
  (forall eta S L, R eta S L -> tl eta S L).
Proof with eauto.
  cofix CIH. intros R H eta S L HR. apply H in HR.
  inversion HR; subst; constructor; constructor; eapply CIH...
Qed.

Lemma tl_coind_ext_aux : forall (R R' : (Var -> Tl) -> Sty -> Tl -> Prop),
  (forall eta S L, R' eta S L -> tl_gen R' eta S L) ->
  (forall eta S L, R eta S L -> tl_gen (fun eta S L => R eta S L \/ R' eta S L) eta S L) ->
  (forall eta S L, R eta S L \/ R' eta S L -> tl eta S L).
Proof with eauto.
  cofix CIH. intros R R' HR' Hor eta S L HR.
  inversion HR.
    apply Hor in H. inversion_clear H; constructor; constructor; eapply CIH...
    eapply tl_coind...
Qed.

Lemma tl_coind_ext : forall (R R' : (Var -> Tl) -> Sty -> Tl -> Prop),
  (forall eta S L, R' eta S L -> tl_gen R' eta S L) ->
  (forall eta S L, R eta S L -> tl_gen (fun eta S L => R eta S L \/ R' eta S L) eta S L) ->
  (forall eta S L, R eta S L -> tl eta S L).
Proof with eauto. intros. eapply tl_coind_ext_aux... Qed.

Lemma tl_expansion_1 : forall (R R' : (Var -> Tl) -> Sty -> Tl -> Prop) eta S L,
  tl_gen R eta S L ->
  tl_gen (fun eta S L => R eta S L \/ R' eta S L) eta S L.
Proof. intros R R' eta S L HR. inversion_clear HR; auto with tl. Qed.

Lemma tl_expansion_2 : forall (R R' : (Var -> Tl) -> Sty -> Tl -> Prop) eta S L,
  tl_gen R' eta S L ->
  tl_gen (fun eta S L => R eta S L \/ R' eta S L) eta S L.
Proof. intros R R' eta S L HR. inversion_clear HR; auto with tl. Qed.

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
Admitted.


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
  apply R_tl_wf_eta_irrelevant_lemma. apply tl_coind. intros eta S L H.
  inversion_clear H. destruct S.
    inversion_clear H1. inversion_clear H. inversion_clear H1. constructor.

    apply wellformed_inversion_send in H0. inversion_clear H1.
    inversion_clear H. inversion_clear H1...

    apply wellformed_inversion_recv in H0. inversion_clear H1.
    inversion_clear H. inversion_clear H1...

    inversion_clear H1. inversion_clear H. inversion_clear H1.
    apply wellformed_inversion_echoice in H0. destruct H0. constructor;
    constructor...

    inversion_clear H1. inversion_clear H. inversion_clear H1.
    apply wellformed_inversion_ichoice in H0. destruct H0. constructor;
    constructor...

    inversion_clear H1. inversion_clear H. inversion_clear H1.
    constructor. constructor 2 with (X := v).
      apply wellformed_inversion_mu in H0. intros T HwfT.
      apply subst_preserves_wellformedness...

    inversion H0.

  (*
  destruct S.
    inversion_clear H1. inversion_clear H. inversion_clear H1.
    inversion_clear H. inversion_clear H1. constructor.

    inversion_clear H1. inversion_clear H. inversion_clear H1. inversion_clear
    H. inversion_clear H1. constructor. constructor 2 with (X := X). simpl in H0.
  *)
Admitted.

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
Admitted.
