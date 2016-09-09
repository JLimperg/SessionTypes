Require Import Contractive Free Sty.
Require Import Morphisms Program.Basics.


Create HintDb wf discriminated.


Definition Wf (S : Sty) := Contractive S /\ Closed S.


Definition Wf_Contractive {S} (Swf : Wf S) : Contractive S :=
  proj1 Swf
.

Definition Wf_Closed {S} (Swf : Wf S) : Closed S :=
  proj2 Swf
.
