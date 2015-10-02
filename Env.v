(* TODO This file could probably do with a little more structure, consistent
   naming and such. *)

Require Import List1 MSetList MSetProperties Program.Basics TLC.LibTactics Var
  Vars.

Module S := MSetList.Make VarOrder.
Module SF := MSetProperties.WPropertiesOn VarOrder S.

Notation Env := S.t.

Notation env_empty := S.empty.
Notation env_add := S.add.
Notation env_mem := S.In.
Notation env_memb := SF.In_dec.
Notation env_eq := S.Equal.
Notation env_subset := S.Subset.
Notation env_union := S.union.
Notation env_singleton x := (env_add x env_empty).
Notation env_fold := S.fold.
Notation list_to_env := SF.of_list.

Lemma env_mem_spec_subset :
  forall x e e',
  env_subset e e' ->
  env_mem x e ->
  env_mem x e'.
Proof. intros. eapply SF.in_subset; eauto. Qed.

Definition env_add_all (xs : list Var) (ys : Env) : Env :=
  fold_left (fun x y => env_add y x) xs ys.
Definition env_subset_equal :
  forall XS YS,
  env_eq XS YS ->
  env_subset XS YS
  := SF.subset_equal.

Definition env_add_assoc :
  forall XS X Y,
  env_eq (env_add X (env_add Y XS)) (env_add Y (env_add X XS))
  := SF.add_add.

Instance env_add_m_subset (x : Var) : Proper (env_subset ==> env_subset) (env_add x).
Proof. solve_proper. Qed.

Definition env_union_list (xs : Env) (ys : list Var) : Env :=
  fold_left (flip env_add) ys xs.

Lemma env_union_list_neutral :
  forall xs,
  env_union_list xs nil = xs.
Proof. auto. Qed.

Definition env_union_vars (xs : Env) (ys : Vars) : Env :=
  fold_left1 (fun x y => env_add y x) ys xs.

Instance env_union_vars_m_subset :
  Proper (env_subset ==> eq ==> env_subset) env_union_vars.
Proof.
  unfold Proper. unfold respectful. introv Hsub Heq. subst.
  rename y0 into xs. gen x y. induction xs using list1_ind'; introv Hsub.
    unfold env_union_vars. simpl. rewrite Hsub. reflexivity.

    unfold env_union_vars in *. unfold cons1. destruct xs as [xs HxsNE].
    simpl in *. apply IHxs. rewrite Hsub. reflexivity.
Qed.

Instance env_union_vars_m_env_eq :
  Proper (env_eq ==> eq ==> env_eq) env_union_vars.
Proof.
  unfold Proper. unfold respectful. intros xs ys Hxsys xs' ys' Hxs'ys'.
  subst. unfold env_union_vars. gen ys xs. destruct ys' as [ys' Hys'nonempty].

  unfold fold_left1. simpl. clear Hys'nonempty. induction ys'; auto.
  introv Hxsys. simpl in *. apply IHys'. rewrite Hxsys. reflexivity.
Qed.

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
Proof. intros; split; intros H; auto. Qed.

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

Lemma env_subset_add :
  forall XS X,
  env_subset XS (env_add X XS).
Proof. intros. rewrite env_add_union_singleton2. apply SF.union_subset_1. Qed.

Definition env_subset_union1 :
  forall e e',
  env_subset e (env_union e e')
  := SF.union_subset_1.

Definition env_subset_union2 :
  forall e e',
  env_subset e' (env_union e e')
  := SF.union_subset_2.

Lemma env_union_vars_spec :
  forall xs ys,
  env_eq (env_union_vars xs ys) (env_union xs (list_to_env ys)).
Proof.
  unfold SF.of_list. unfold env_union_vars. unfold fold_left1. intros. gen xs.
  induction ys using list1_ind'; intros.
    simpl. rewrite env_add_union_singleton2. reflexivity.

    destruct ys as [ys HysNE]. simpl in *. rewrite IHys.
    rewrite <- env_add_union1. rewrite env_add_union2. reflexivity.
Qed.

Lemma env_union_list_spec :
  forall xs ys,
  env_eq (env_union_list xs ys) (env_union xs (list_to_env ys)).
Proof.
  unfold SF.of_list. unfold env_union_list. unfold flip. intros. gen xs.
  induction ys; intros.
    simpl. rewrite env_union_neutral. reflexivity.
    simpl in *. rewrite IHys. rewrite <- env_add_union2.
    rewrite env_add_union1. reflexivity.
Qed.

Lemma list_to_env_cons :
  forall x xs,
  env_eq (list_to_env (x :: xs)) (env_add x (list_to_env xs)).
Proof. intros. unfold SF.of_list. simpl. reflexivity. Qed.
