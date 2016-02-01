Require Export TLC.LibTactics.

Ltac decompose_ex H :=
  match type of H with
  | @ex _ (fun x => _) =>
      let x := fresh x in
      destruct H as [x H]; try (decompose_ex H)
  end
.

Ltac invertsN n H := do n (inverts H as H).
Ltac inverts1 := invertsN ltac:1.
Ltac inverts2 := invertsN ltac:2.
