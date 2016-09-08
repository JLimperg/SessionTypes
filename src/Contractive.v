Require Import Msg Sty Shape Var.

Create HintDb contractive discriminated.

Inductive Contractive : Sty -> Prop :=
| Contractive_unit :
    Contractive unit
| Contractive_send :
    forall S B,
    Contractive S ->
    Contractive (send B S)
| Contractive_recv :
    forall S B,
    Contractive S ->
    Contractive (recv B S)
| Contractive_echoice :
    forall S1 S2,
    Contractive S1 ->
    Contractive S2 ->
    Contractive (echoice S1 S2)
| Contractive_ichoice :
    forall S1 S2,
    Contractive S1 ->
    Contractive S2 ->
    Contractive (ichoice S1 S2)
| Contractive_mu :
    forall S X,
    Contractive S ->
    shape S <> varS ->
    Contractive (mu X S)
| Contractive_var :
    forall X,
    Contractive (var X)
.
Hint Constructors Contractive : contractive.