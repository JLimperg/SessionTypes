Require Import Contractive Sty Map Msg Tac Var.


Create HintDb tl discriminated.


CoInductive Tl :=
| Tl_unit : Tl
| Tl_send : Msg -> Tl -> Tl
| Tl_recv : Msg -> Tl -> Tl
| Tl_echoice : Tl -> Tl -> Tl
| Tl_ichoice : Tl -> Tl -> Tl
.
Hint Constructors Tl : tl.


Inductive Tl_bisim_gen Tl_bisim : Tl -> Tl -> Prop :=
| Tl_bisim_gen_unit :
    Tl_bisim_gen Tl_bisim Tl_unit Tl_unit
| Tl_bisim_gen_send :
    forall l l' B,
    Tl_bisim l l' ->
    Tl_bisim_gen Tl_bisim (Tl_send B l) (Tl_send B l')
| Tl_bisim_gen_recv :
    forall l l' B,
    Tl_bisim l l' ->
    Tl_bisim_gen Tl_bisim (Tl_recv B l) (Tl_recv B l')
| Tl_bisim_gen_echoice :
    forall l1 l1' l2 l2',
    Tl_bisim l1 l1' ->
    Tl_bisim l2 l2' ->
    Tl_bisim_gen Tl_bisim (Tl_echoice l1 l2) (Tl_echoice l1' l2')
| Tl_bisim_gen_ichoice :
    forall l1 l1' l2 l2',
    Tl_bisim l1 l1' ->
    Tl_bisim l2 l2' ->
    Tl_bisim_gen Tl_bisim (Tl_ichoice l1 l2) (Tl_ichoice l1' l2')
.
Hint Constructors Tl_bisim_gen : tl.

CoInductive Tl_bisim : Tl -> Tl -> Prop :=
| Tl_bisim_fold : forall l l', Tl_bisim_gen Tl_bisim l l' -> Tl_bisim l l'.
Hint Constructors Tl_bisim.


Lemma Tl_bisim_coind : forall R,
  (forall l l', R l l' -> Tl_bisim_gen R l l')
  -> forall l l', R l l' -> Tl_bisim l l'.
Proof. cofix CIH. introv H HR. apply H in HR. inverts HR; eauto with tl. Qed.


(*
The following lemmae are used in the definition of tl below. We introduce
them in order to prevent the unfolding of contractiveness proofs used in tl,
which would otherwise lead to large and confusing goals.
*)

Ltac Contractive_inv :=
  let H := fresh in
  intro H; inversion H; auto
.

Lemma Contractive_inv_send {S B} :
  Contractive (send B S) -> Contractive S.
Proof. Contractive_inv. Qed.

Lemma Contractive_inv_recv {S B} :
  Contractive (recv B S) -> Contractive S.
Proof. Contractive_inv. Qed.

Lemma Contractive_inv_echoice1 {S1 S2} :
  Contractive (echoice S1 S2) -> Contractive S1.
Proof. Contractive_inv. Qed.

Lemma Contractive_inv_echoice2 {S1 S2} :
  Contractive (echoice S1 S2) -> Contractive S2.
Proof. Contractive_inv. Qed.

Lemma Contractive_inv_ichoice1 {S1 S2} :
  Contractive (ichoice S1 S2) -> Contractive S1.
Proof. Contractive_inv. Qed.

Lemma Contractive_inv_ichoice2 {S1 S2} :
  Contractive (ichoice S1 S2) -> Contractive S2.
Proof. Contractive_inv. Qed.

Lemma Contractive_inv_mu {S X} :
  Contractive (mu X S) -> Contractive S.
Proof. Contractive_inv. Qed.


(*
The following two axioms are used exclusively in the definition of tl below. We
justify their use here:

tl_fix is used to circumvent the productivity checker, which doesn't consider
tl productive due to the case for (mu X S). This is correct insofar as tl is
only productive if the input S is contractive, therefore we require a proof
of contractiveness for every application of tl.

With S contractive, productivity follows:

  For S in {unit, send _ _, recv _ _, echoice _ _, ichoice _ _}, we produce a
  constructor before recursing into tl.

  For S = var _, we don't recurse at all.

  For S = mu X S', S' <> var _ due to S contractive. Thus, the recursive call
  (tl _ S' _) produces at least one constructor before potentially recursing
  further.

Thus, the use of tl_fix is safe. tl_fix_fix merely stipulates that tl_fix
behaves like a fixpoint combinator.
*)

Axiom tl_fix : (Tl -> Tl) -> Tl.

Axiom tl_fix_fix :
  forall F,
  tl_fix F = F (tl_fix F).

Fixpoint tl (eta : Var -> Tl) (S : Sty) (Scontr : Contractive S) : Tl :=
  match S return Contractive S -> Tl with
  | unit => fun _ =>
      Tl_unit
  | send B S' => fun c =>
      Tl_send B (tl eta S' (Contractive_inv_send c))
  | recv B S' => fun c =>
      Tl_recv B (tl eta S' (Contractive_inv_recv c))
  | echoice S1 S2 => fun c =>
      Tl_echoice
        (tl eta S1 (Contractive_inv_echoice1 c))
        (tl eta S2 (Contractive_inv_echoice2 c))
  | ichoice S1 S2 => fun c =>
      Tl_ichoice
        (tl eta S1 (Contractive_inv_ichoice1 c))
        (tl eta S2 (Contractive_inv_ichoice2 c))
  | mu X S' => fun c =>
      tl_fix (fun lx => tl (eta_override eta X lx) S' (Contractive_inv_mu c))
  | var X => fun _ =>
      eta X
  end
  Scontr
.
