Require Import Var MSetList MSetProperties.

Module S := MSetList.Make VarOrder.
Module SF := MSetProperties.WPropertiesOn VarOrder S.

Notation Env := S.t.

Notation env_empty := S.empty.
Notation env_add := S.add.
Notation env_mem := S.In.
Notation env_memb := SF.In_dec.
Notation env_eq := S.Equal.
Notation env_union := S.union.
Notation env_singleton x := (env_add x env_empty).
Notation env_fold := S.fold.

Definition env_add_all (xs : list Var) (ys : Env) : Env :=
  fold_left (fun x y => env_add y x) xs ys.

Definition env_add_exchange :
  forall XS X Y,
  env_eq (env_add X (env_add Y XS)) (env_add Y (env_add X XS))
  := SF.add_add.

Lemma env_add_twice :
  forall X XS,
  env_eq (env_add X (env_add X XS)) (env_add X XS).
Proof. intros. apply SF.add_equal. apply S.add_spec; auto. Qed.

Lemma env_add_eq :
  forall e e' x,
  env_eq e e' ->
  env_eq (env_add x e) (env_add x e').
Proof. intros e e' x eqee'. apply SF.Dec.F.add_m; auto. Qed.

Lemma env_add_mem :
  forall e x y,
  env_mem x e ->
  env_mem x (env_add y e).
Proof. intros e x y H. apply S.add_spec; auto. Qed.

Lemma env_mem_add :
  forall e x y,
  x <> y ->
  env_mem y (env_add x e) ->
  env_mem y e.
Proof. apply SF.Dec.F.add_3. Qed.

Lemma env_mem_empty : forall x, not (env_mem x env_empty).
Proof. unfold not. apply SF.FM.empty_iff. Qed.
Hint Resolve env_mem_empty : env.

Lemma env_eq_spec :
  forall e e',
  env_eq e e' <-> (forall x, env_mem x e <-> env_mem x e').
Proof with auto. intros; split; intros H; auto. Qed.

Definition env_eq_refl :
  forall e,
  env_eq e e
  := SF.equal_refl.

Definition env_eq_sym :
  forall e e',
  env_eq e e' ->
  env_eq e' e
  := SF.equal_sym.

Definition env_eq_trans :
  forall e1 e2 e3,
  env_eq e1 e2 ->
  env_eq e2 e3 ->
  env_eq e1 e3
  := SF.equal_trans.

Lemma env_add_union_singleton :
  forall e X,
  env_eq (env_union e (env_singleton X)) (env_add X e).
Proof.
  intros e X. symmetry. rewrite SF.union_sym. apply SF.add_union_singleton.
Qed.

Lemma env_add_union1 :
  forall X e e',
  env_eq (env_add X (env_union e e')) (env_union (env_add X e) e').
Proof. intros. symmetry. apply SF.union_add. Qed.

Lemma env_add_union2 :
  forall X e e',
  env_eq (env_add X (env_union e e')) (env_union e (env_add X e')).
Proof.
  intros. rewrite SF.union_sym. rewrite env_add_union1. rewrite SF.union_sym.
  apply env_eq_refl.
Qed.

Lemma env_union_add :
  forall X X' e e',
  env_eq (env_union (env_add X e) (env_add X' e')) (env_union e (env_add X (env_add X' e'))).
Proof.
  intros. rewrite <- env_add_union1. rewrite env_add_union2. reflexivity.
Qed.

Lemma env_add_union_singleton2 :
  forall X e,
  env_eq (env_add X e) (env_union e (env_singleton X)).
Proof. auto with set. Qed.

Lemma env_union_neutral :
  forall e,
  env_eq (env_union e env_empty) e.
Proof. auto with set. Qed.

Lemma env_union_assoc :
  forall e e' e'',
  env_eq (env_union (env_union e e') e'') (env_union e (env_union e' e'')).
Proof. auto with set. Qed.
