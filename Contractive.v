Require Import Env Free FreeFacts SessionTypes Shape ShapeFacts Tac Var
  Wellformed.

Create HintDb contract discriminated.

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
Hint Constructors Contractive : contract.


Lemma ok_checked_Contractive :
  forall S,
  (forall XS, ok XS S -> Contractive S) /\
  (forall XS, checked XS S -> Contractive S).
Proof.
  induction S; split; introv H; try (decompose_and IHS); constructor; inverts1 H;
    repeat match goal with
    | H : checked _ _ |- _ => inverts H
    end;
    eauto with wf contract.
  - introv contra. shape_inv_auto. auto with wf.
  - inverts H. eauto.
  - inverts1 H. introv contra. shape_inv_auto. auto with wf.
  Unshelve. all: exact (mkVar 0). (* Not sure why this hack is necessary. *)
Qed.

Lemma ok_Contractive :
  forall S,
  ok_some S ->
  Contractive S.
Proof. introv H. pose proof (ok_checked_Contractive S). jauto. Qed.

Lemma checked_Contractive :
  forall S XS,
  checked XS S ->
  Contractive S.
Proof. introv H. pose proof (ok_checked_Contractive S). jauto. Qed.

Lemma wellformed_Contractive :
  forall S,
  wellformed S ->
  Contractive S.
Proof. unfold wellformed. intros. eauto using ok_Contractive. Qed.