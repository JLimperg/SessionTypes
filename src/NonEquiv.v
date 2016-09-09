Require Import Sty Subst Shape Msg Var.

Create HintDb nsequiv discriminated.

Inductive NSequiv : Sty -> Sty -> Prop :=
| NSequiv_send_S :
    forall B S S',
    NSequiv S S' ->
    NSequiv (send B S) (send B S')
| NSequiv_send_B :
    forall B B' S S',
    B <> B' ->
    NSequiv (send B S) (send B' S')
| NSequiv_recv_S :
    forall B S S',
    NSequiv S S' ->
    NSequiv (recv B S) (recv B S')
| NSequiv_recv_B :
    forall B B' S S',
    B <> B' ->
    NSequiv (recv B S) (recv B' S')
| NSequiv_echoice_l :
    forall S1 S2 S1' S2',
    NSequiv S1 S1' ->
    NSequiv (echoice S1 S2) (echoice S1' S2')
| NSequiv_echoice_r :
    forall S1 S2 S1' S2',
    NSequiv S2 S2' ->
    NSequiv (echoice S1 S2) (echoice S1' S2')
| NSequiv_ichoice_l :
    forall S1 S2 S1' S2',
    NSequiv S1 S1' ->
    NSequiv (ichoice S1 S2) (ichoice S1' S2')
| NSequiv_ichoice_r :
    forall S1 S2 S1' S2',
    NSequiv S2 S2' ->
    NSequiv (ichoice S1 S2) (ichoice S1' S2')
| NSequiv_mu_l :
    forall X S S',
    NSequiv (subst X (mu X S) S) S' ->
    NSequiv (mu X S) S'
| NSequiv_mu_r :
    forall X S S',
    NSequiv S (subst X (mu X S') S') ->
    NSequiv S (mu X S')
| NSequiv_shape :
    forall S S',
    shape S  <> muS ->
    shape S' <> muS ->
    shape S <> shape S' ->
    NSequiv S S'
.
Hint Constructors NSequiv : nsequiv.
