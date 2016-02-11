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
