Require Import Sty Subst Shape Msg Var.

Create HintDb nsequiv discriminated.

Inductive nsequiv : Sty -> Sty -> Prop :=
| nsequiv_send_S :
    forall B S S',
    nsequiv S S' ->
    nsequiv (send B S) (send B S')
| nsequiv_send_B :
    forall B B' S S',
    B <> B' ->
    nsequiv (send B S) (send B' S')
| nsequiv_recv_S :
    forall B S S',
    nsequiv S S' ->
    nsequiv (recv B S) (recv B S')
| nsequiv_recv_B :
    forall B B' S S',
    B <> B' ->
    nsequiv (recv B S) (recv B' S')
| nsequiv_echoice_l :
    forall S1 S2 S1' S2',
    nsequiv S1 S1' ->
    nsequiv (echoice S1 S2) (echoice S1' S2')
| nsequiv_echoice_r :
    forall S1 S2 S1' S2',
    nsequiv S2 S2' ->
    nsequiv (echoice S1 S2) (echoice S1' S2')
| nsequiv_ichoice_l :
    forall S1 S2 S1' S2',
    nsequiv S1 S1' ->
    nsequiv (ichoice S1 S2) (ichoice S1' S2')
| nsequiv_ichoice_r :
    forall S1 S2 S1' S2',
    nsequiv S2 S2' ->
    nsequiv (ichoice S1 S2) (ichoice S1' S2')
| nsequiv_mu_l :
    forall X S S',
    nsequiv (subst X (mu X S) S) S' ->
    nsequiv (mu X S) S'
| nsequiv_mu_r :
    forall X S S',
    nsequiv S (subst X (mu X S') S') ->
    nsequiv S (mu X S')
| nsequiv_shape :
    forall S S',
    shape S  <> muS ->
    shape S' <> muS ->
    shape S <> shape S' ->
    nsequiv S S'
.
Hint Constructors nsequiv : nsequiv.
