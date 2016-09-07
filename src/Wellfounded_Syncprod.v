Require Import Tac.
Require Import Relations Wellfounded.

Inductive syncprod {A B} (RA : A -> A -> Prop) (RB : B -> B -> Prop) :
  (A * B) -> (A * B) -> Prop :=
| syncprod_intro :
    forall a a' b b',
    RA a a' ->
    RB b b' ->
    syncprod RA RB (a, b) (a', b')
.


Lemma wf_syncprod :
  forall (A B : Type) RA RB,
  well_founded RA ->
  well_founded (@syncprod A B RA RB).
Proof.
  introv HwfA. unfolds. intro p. destruct p as [x y]. gen x y.
  induction x using (well_founded_ind HwfA). intros.
  constructor. introv H'. inverts H'. auto.
Defined.
