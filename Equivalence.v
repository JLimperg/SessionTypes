Require Import SessionTypes.

Inductive sequiv_gen sequiv : Sty -> Sty -> Prop :=
| sequiv_gen_end : sequiv_gen sequiv unit unit
| sequiv_gen_send : forall B S S',
    sequiv S S' ->
    sequiv_gen sequiv (send B S) (send B S')
| sequiv_gen_recv : forall B S S',
    sequiv S S' ->
    sequiv_gen sequiv (recv B S) (recv B S')
| sequiv_gen_echoice : forall S1 S2 S1' S2',
    sequiv S1 S1' ->
    sequiv S2 S2' ->
    sequiv_gen sequiv (echoice S1 S2) (echoice S1' S2')
| sequiv_gen_ichoice : forall S1 S2 S1' S2',
    sequiv S1 S1' ->
    sequiv S2 S2' ->
    sequiv_gen sequiv (ichoice S1 S2) (ichoice S1' S2')
| sequiv_gen_mu1 : forall X S S',
    sequiv (subst X (mu X S) S) S' ->
    sequiv_gen sequiv (mu X S) S'
| sequiv_gen_mu2 : forall X S S',
    sequiv S (subst X (mu X S') S') ->
    sequiv_gen sequiv S (mu X S')
.
Hint Constructors sequiv_gen.

CoInductive sequiv : Sty -> Sty -> Prop :=
| sequiv_fold : forall S S', sequiv_gen sequiv S S' -> sequiv S S'.
Hint Constructors sequiv.

Lemma sequiv_coind : forall R,
  (forall S S', R S S' -> sequiv_gen R S S')
  -> (forall S S', R S S' -> sequiv S S').
Proof.
  cofix CIH. intros R H S S' HR. apply H in HR.
  inversion HR; subst; constructor; constructor; apply CIH with (R := R); assumption.
Qed.
