Require Import Tac Var.
Require Import MSetWeakList MSetProperties Program.Basics.

Module S := MSetWeakList.Make VarEq.
Module SF := MSetProperties.WPropertiesOn VarEq S.

Notation Env := S.t.

Notation env_empty := S.empty.
Notation env_add := S.add.
Notation env_mem := S.In.


Lemma env_mem_add :
  forall e x y,
  x <> y ->
  env_mem y (env_add x e) ->
  env_mem y e.
Proof. apply SF.Dec.F.add_3. Qed.


Lemma env_add_mem :
  forall e x y,
  env_mem x e ->
  env_mem x (env_add y e).
Proof. intros e x y H. apply S.add_spec; auto. Qed.


Lemma env_add_mem' :
  forall e x,
  env_mem x (env_add x e).
Proof. intros. apply SF.Dec.F.add_1. auto. Qed.


Lemma env_mem_empty :
  forall x,
  ~ (env_mem x env_empty).
Proof. unfold not. apply SF.FM.empty_iff. Qed.