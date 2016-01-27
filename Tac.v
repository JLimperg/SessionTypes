Require Export TLC.LibTactics.

Ltac decompose_ex H :=
  match type of H with
  | @ex _ (fun x => _) =>
      let x := fresh x in
      destruct H as [x H]; try (decompose_ex H)
  end
.

