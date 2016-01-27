Require Import Equivalence Reflexivity SessionTypes Tac Wellformed.

Theorem sequiv_transitive :
  forall S T U,
  wellformed S ->
  wellformed T ->
  wellformed U ->
  sequiv S T ->
  sequiv T U ->
  sequiv S U.
Proof. Admitted.
