Require Import Env Sty Shape Subst Tac Var.

Inductive Sequiv_gen Sequiv : Sty -> Sty -> Prop :=
| Sequiv_gen_end : Sequiv_gen Sequiv unit unit
| Sequiv_gen_send : forall B S S',
    Sequiv S S' ->
    Sequiv_gen Sequiv (send B S) (send B S')
| Sequiv_gen_recv : forall B S S',
    Sequiv S S' ->
    Sequiv_gen Sequiv (recv B S) (recv B S')
| Sequiv_gen_echoice : forall S1 S2 S1' S2',
    Sequiv S1 S1' ->
    Sequiv S2 S2' ->
    Sequiv_gen Sequiv (echoice S1 S2) (echoice S1' S2')
| Sequiv_gen_ichoice : forall S1 S2 S1' S2',
    Sequiv S1 S1' ->
    Sequiv S2 S2' ->
    Sequiv_gen Sequiv (ichoice S1 S2) (ichoice S1' S2')
| Sequiv_gen_mu1 : forall X S S',
    Sequiv (subst X (mu X S) S) S' ->
    Sequiv_gen Sequiv (mu X S) S'
| Sequiv_gen_mu2 : forall X S S',
    Sequiv S (subst X (mu X S') S') ->
    Sequiv_gen Sequiv S (mu X S')
.
Hint Constructors Sequiv_gen.

CoInductive Sequiv : Sty -> Sty -> Prop :=
| Sequiv_fold : forall S S', Sequiv_gen Sequiv S S' -> Sequiv S S'.
Hint Constructors Sequiv.


Lemma Sequiv_coind : forall R,
  (forall S S', R S S' -> Sequiv_gen R S S')
  -> (forall S S', R S S' -> Sequiv S S').
Proof. cofix CIH. introv H HR. apply H in HR. inverts HR; eauto. Qed.
