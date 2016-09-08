Require Import Contractive Env Free FreeFacts Msg Shape Sty Tac Var Wf.

Definition wellformed' (S : Sty) := Contractive S /\ Closed S.


Lemma wellformed_wellformed' :
  forall S,
  wellformed S -> wellformed' S.
Proof.
  introv H. unfolds. split;
  auto using wellformed_Contractive, wellformed_closed.
Qed.


Lemma free_contractive_checked_ok :
  forall S XS,
  (forall X, Free X S -> env_mem X XS) ->
  Contractive S ->
  checked XS S /\ (shape S <> varS -> ok XS S).
Proof.
  intros S XS. gen XS. induction S; introv H; (
    let finish :=
      constructor; first [apply IHS | apply IHS1 | apply IHS2];
      auto with free contractive in
    split;
    [ try solve [constructor; finish]
    | introv Hsh; try solve [finish]
    ]
  ).
  - constructor. constructor. apply IHS; [|auto with contractive..].
    * introv Hfree. destruct (eq_var_dec X v) as [Heq | Hneq].
      + subst. apply env_add_mem'.
      + apply env_add_mem. auto with free.
  - constructor. apply IHS; [|auto with contractive..].
    * introv Hfree. destruct (eq_var_dec X v) as [Heq | Hneq].
      + subst. apply env_add_mem'.
      + apply env_add_mem. auto with free.
  - constructor. auto with free.
  - exfalso. apply Hsh. reflexivity.
Qed.


Lemma wellformed'_wellformed :
  forall S,
  wellformed' S -> wellformed S.
Proof.
  introv H. inversion H as [Hcontractive Hclosed].
  apply free_contractive_checked_ok.
  - introv Hfree. contradict Hfree. auto with free.
  - assumption.
  - destruct S; simpl; try autodiscriminate; auto with free.
Qed.


Lemma wellformed'_iff_wellformed : 
  forall S,
  wellformed S <-> wellformed' S.
Proof.
  intros. split.
  - apply wellformed_wellformed'.
  - apply wellformed'_wellformed.
Qed.