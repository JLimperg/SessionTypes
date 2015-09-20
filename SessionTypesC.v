Require Import Env List List1 Morphisms Msg Relations.Relation_Definitions
  Relations.Relation_Operators Shape Var.
Require Setoid.

Create HintDb styc discriminated.

Module StyC.

Inductive Sty : Type :=
| unit : Sty
| send : Msg -> Sty -> Sty
| recv : Msg -> Sty -> Sty
| echoice : Sty -> Sty -> Sty
| ichoice : Sty -> Sty -> Sty
| mu : Env -> Sty -> Sty
| var : Var -> Sty
.

Fixpoint subst (x : Var) (r orig : Sty) : Sty :=
  match orig with
  | unit => unit
  | send msg tail => send msg (subst x r tail)
  | recv msg tail => recv msg (subst x r tail)
  | echoice tail1 tail2 => echoice (subst x r tail1) (subst x r tail2)
  | ichoice tail1 tail2 => ichoice (subst x r tail1) (subst x r tail2)
  | mu ys tail => if env_memb x ys then orig else mu ys (subst x r tail)
  | var y => if beq_var x y then r else orig
  end
.

Definition shape (S : Sty) : Shape :=
  match S with
  | unit => unitS
  | send _ _ => sendS
  | recv _ _ => recvS
  | echoice _ _ => echoiceS
  | ichoice _ _ => ichoiceS
  | mu _ _ => muS
  | var _ => varS
  end
.

Inductive eq_syn : Sty -> Sty -> Prop :=
| eq_syn_unit : eq_syn unit unit
| eq_syn_send :
    forall B S S',
    eq_syn S S' ->
    eq_syn (send B S) (send B S')
| eq_syn_recv :
    forall B S S',
    eq_syn S S' ->
    eq_syn (recv B S) (recv B S')
| eq_syn_echoice :
    forall S1 S2 S1' S2',
    eq_syn S1 S1' ->
    eq_syn S2 S2' ->
    eq_syn (echoice S1 S2) (echoice S1' S2')
| eq_syn_ichoice :
    forall S1 S2 S1' S2',
    eq_syn S1 S1' ->
    eq_syn S2 S2' ->
    eq_syn (ichoice S1 S2) (ichoice S1' S2')
| eq_syn_mu :
    forall xs xs' S S',
    env_eq xs xs' ->
    eq_syn S S' ->
    eq_syn (mu xs S) (mu xs' S')
| eq_syn_var :
    forall X X',
    X = X' ->
    eq_syn (var X) (var X')
.
Hint Constructors eq_syn : styc.

Local Hint Constructors eq_syn : tmp.
Local Hint Resolve env_eq_refl env_eq_sym env_eq_trans : tmp.

Lemma eq_syn_refl : reflexive Sty eq_syn.
Proof. unfold reflexive. intros S. induction S; auto with tmp. Qed.

Lemma eq_syn_sym : symmetric Sty eq_syn.
Proof. unfold symmetric. intros S T HST. induction HST; auto with tmp. Qed.

Lemma eq_syn_trans : transitive Sty eq_syn.
Proof.
  unfold transitive. intros S1 S2 S3 H12. generalize dependent S3. induction H12;
  intros S3 H23; inversion_clear H23; subst; eauto with tmp.
Qed.

Add Relation Sty eq_syn
  reflexivity proved by eq_syn_refl
  symmetry proved by eq_syn_sym
  transitivity proved by eq_syn_trans
  as eq_syn'.

Lemma eq_syn_shape :
  forall S S',
  eq_syn S S' ->
  shape S = shape S'.
Proof. intros S S' H. induction H; auto with styc. Qed.

Hint Resolve eq_syn_shape : styc.

Instance shape_m : Proper (eq_syn ==> eq) shape.
Proof. unfold Proper. unfold respectful. apply eq_syn_shape. Qed.

End StyC.
