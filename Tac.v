Require Export TLC.LibTactics.


Ltac invertsN n H := do n (inverts H as H).
Ltac inverts1 := invertsN ltac:1.
Ltac inverts2 := invertsN ltac:2.


Ltac decompose_ex H :=
  match type of H with
  | @ex _ (fun x => _) =>
      let x := fresh x in
      destruct H as [x H]; try (decompose_ex H)
  end
.

Ltac decompose_ex_auto :=
  match goal with
  | H : @ex _ _ |- _ => decompose_ex H
  end;
  try decompose_ex_auto
.

Ltac decompose_and H :=
  match type of H with
  | _ /\ _ => decompose [and] H; clear H
  end
.

Ltac decompose_and_auto :=
  match goal with
  | H : _ /\ _ |- _ => decompose_and H
  end;
  try decompose_and_auto
.


Ltac decompose_or H :=
  match type of H with
  | _ \/ _ => destruct H as [H | H]; try (decompose_or H)
  end
.

Ltac decompose_or_auto :=
  match goal with
  | H : _ \/ _ |- _ => decompose_or H
  end;
  try decompose_or_auto
.

Ltac norm_hyp_auto :=
  (decompose_ex_auto || decompose_and_auto || decompose_or_auto);
  try norm_hyp_auto
.

Hint Extern 0 => decompose_and_auto.
Hint Extern 1 => decompose_ex_auto.
