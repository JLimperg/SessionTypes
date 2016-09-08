Require Import Contractive Free Sty.
Require Import Morphisms Program.Basics.


Create HintDb wf discriminated.


Definition wellformed (S : Sty) := Contractive S /\ Closed S.


Definition wellformed_Contractive {S} (Swf : wellformed S) : Contractive S :=
  proj1 Swf
.

Definition wellformed_Closed {S} (Swf : wellformed S) : Closed S :=
  proj2 Swf
.