Require Import Map Msg Rel SessionTypes Var.

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
