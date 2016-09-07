Require Import Tac.
Require Export Relations.
Require TLC.LibRelation.

Create HintDb rel discriminated.
Hint Unfold inclusion : rel.
Hint Unfold symmetric : rel.
Hint Unfold transitive : rel.

Inductive clos_sym A (R : relation A) : relation A :=
| clos_sym_intro : forall x y : A, R x y -> clos_sym A R y x
.
Hint Constructors clos_sym : rel.
Hint Constructors clos_trans : rel.

Lemma clos_sym_sym :
  forall A (R : relation A),
  inclusion A (clos_sym A R) R ->
  symmetric A R.
Proof. auto with rel. Qed.

Lemma clos_trans_trans :
  forall A (R : relation A),
  inclusion A (clos_trans A R) R ->
  transitive A R.
Proof.
  unfold inclusion. unfold transitive. eauto with rel.
Qed.

Inductive clos_trans' {A} (R : relation A) : relation A :=
| clos_trans'_intro :
    forall x y z,
    R x y -> R y z -> clos_trans' R x z
.
Hint Constructors clos_trans' : rel.

Lemma clos_trans'_trans :
  forall A R,
  inclusion A (clos_trans' R) R ->
  transitive A R.
Proof. eauto with rel. Qed.

(* -------------------------------------------------------------------------- *)
(* Conversion between LibRelation and Coq standard library *)

Ltac solve_LibRelation_conversion :=
  let H := fresh in
  intros; split; introv H; red in H; red; eauto.

Lemma reflexive_refl_iff {A} {R} :
  reflexive A R <-> TLC.LibRelation.refl R.
Proof. solve_LibRelation_conversion. Qed.

Lemma refl_reflexive {A} {R} :
  TLC.LibRelation.refl R -> reflexive A R.
Proof. intros; apply reflexive_refl_iff; auto. Qed.

Lemma symmetric_sym_iff {A} {R} :
  symmetric A R <-> TLC.LibRelation.sym R.
Proof. solve_LibRelation_conversion. Qed.

Lemma sym_symmetric {A} {R} :
  TLC.LibRelation.sym R -> symmetric A R.
Proof. intros; apply symmetric_sym_iff; auto. Qed.

Lemma transitive_trans_iff {A} {R} :
  transitive A R <-> TLC.LibRelation.trans R.
Proof. solve_LibRelation_conversion. Qed.

Lemma trans_transitive {A} {R} :
  TLC.LibRelation.trans R -> transitive A R.
Proof. intros; apply transitive_trans_iff; auto. Qed.
