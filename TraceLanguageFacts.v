Require Import Free FreeFacts Map Rel SessionTypes Substitution Tac
  TraceLanguage Var Wellformed.

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
Hint Resolve eq_tl_refl : tl.

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


Lemma tl_m_eq_tl_eta_override :
  forall S eta X LX LX' L,
  eq_tl LX LX' ->
  tl (eta_override eta X LX) S L ->
  tl (eta_override eta X LX') S L.
Proof.
  induction S; introv Heq H; inverts2 H; eauto with tl;
    do 2 constructor.
  - destruct (eq_var_dec v X).
    + rewrite eta_override_overwrite in *; auto.
    + rewrite eta_override_exchange in *; eauto.
  - unfold override in *. destruct (eq_var_dec v X).
    + symmetry in Heq. transitivity LX; auto.
    + auto with tl.
Qed.


Lemma tl_m_eq_tl :
  forall S eta L L',
  eq_tl L L' ->
  tl eta S L ->
  tl eta S L'.
Proof.
  induction S; introv Heq H; inverts2 H; try solve
    [inverts2 Heq; eauto with tl];
    do 2 constructor.
  - apply IHS with (L := L); eauto using tl_m_eq_tl_eta_override.
  - transitivity L; auto.
Qed.


(* TODO beautify *)
Lemma tl_eta_irrelevant_Free :
  forall S L eta eta',
  (forall X, Free X S -> eq_tl (eta X) (eta' X)) ->
  tl eta S L ->
  tl eta' S L.
Proof.
  induction S; introv Hfree H; inverts2 H; eauto 6 with free tl.
  - do 2 constructor.
    + apply IHS1 with (eta := eta); auto with free.
    + apply IHS2 with (eta := eta); auto with free.
  - do 2 constructor.
    + apply IHS1 with (eta := eta); auto with free.
    + apply IHS2 with (eta := eta); auto with free.
  - do 2 constructor. apply IHS with (eta := eta_override eta v L); [|auto].
    + introv Hfree'. unfold override in *. destruct (eq_var_dec X v).
      * reflexivity.
      * auto with free.
  - do 2 constructor. specialize Hfree with (X := v). transitivity (eta v).
    + symmetry. auto with free.
    + auto.
Qed.


Lemma tl_eta_irrelevant :
  forall S L eta eta',
  wellformed S ->
  tl eta S L ->
  tl eta' S L.
Proof.
  introv Hwf H. apply tl_eta_irrelevant_Free with (eta := eta); [|auto].
  introv Hfree. exfalso.
  assert (~ Free X S) by eauto using ok_free with env wf.
  auto.
Qed.
