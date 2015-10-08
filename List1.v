Require Import List Logic.ProofIrrelevance TLC.LibTactics.
Import ListNotations.

Create HintDb list1 discriminated.

(*****************************************************************************)
(* Facts about regular nonempty lists                                        *)

Definition nonempty {A} (xs : list A) : Prop := (xs <> []).

Lemma nonempty_inv :
  forall A (xs : list A),
  nonempty xs ->
  exists y ys, xs = y :: ys.
Proof.
  introv HxsNE. destruct (destruct_list xs) as [Hcons | Hnil].
    destruct Hcons as [x Hcons]. destruct Hcons as [xs' Hcons].
    rewrite Hcons. eauto.

    unfold nonempty in *. rewrite Hnil in HxsNE. exfalso; auto.
Qed.

Lemma cons_not_nil :
  forall A (x : A) xs,
  nonempty (x :: xs).
Proof. intros. unfold not; discriminate. Qed.

Lemma nonempty_app :
  forall A (xs ys : list A),
  nonempty ys ->
  nonempty (xs ++ ys).
Proof. intro. induction xs; auto. intros. simpl. apply cons_not_nil. Qed.

(*****************************************************************************)
(* The type of nonempty lists                                                *)

Definition list1 (A : Type) := { xs : list A & nonempty xs }.

Definition inj_list1_list (A : Type) (xs : list1 A) : list A :=
  @proj1_sig (list A) nonempty xs.

Coercion inj_list1_list : list1 >-> list.

(*****************************************************************************)
(* Construction                                                              *)

Definition mkList1 {A} (xs : list A) (P : xs <> []) : list1 A :=
  existT nonempty xs P.
Hint Unfold mkList1 : list1.

Definition list_to_list1 {A} (x : A) (xs : list A) : list1 A :=
  mkList1 (x :: xs) (cons_not_nil A x xs).
Arguments list_to_list1 / _ _ _.
Hint Unfold list_to_list1 : list1.

Definition singleton1 {A} (x : A) := mkList1 [x] (cons_not_nil A x []).

Definition cons1 {A} (x : A) (xs : list1 A) : list1 A :=
  match xs with
  | existT xs' _ => mkList1 (x :: xs') (cons_not_nil A x xs')
  end
.

(*****************************************************************************)
(* Equality                                                                  *)

Definition eq_list1_compat :
  forall A (xs ys : list A),
  xs = ys ->
  forall xsnonempty ysnonempty, mkList1 xs xsnonempty = mkList1 ys ysnonempty.
Proof. unfold mkList1. intros. apply subsetT_eq_compat. assumption. Defined.
Hint Resolve eq_list1_compat : list1.

Lemma eq_list1_dec {A} :
  (forall (x y : A), {x = y} + {x <> y}) ->
  forall (xs ys : list1 A),
  {xs = ys} + {xs <> ys}.
Proof.
  introv Hdec. destruct xs as [xs Hxs]. destruct ys as [ys Hys].
  destruct (list_eq_dec Hdec xs ys) as [Heq | Hneq].
    left. apply eq_list1_compat. assumption.
    right. unfold not. intros. inverts H. apply Hneq. trivial.
Qed.
Hint Resolve eq_list1_dec : list1.

Lemma cons1_inv :
  forall A (x y : A) xs ys Hys,
  cons1 x xs = mkList1 (y :: ys) Hys ->
  x = y /\
  exists Hys', xs = mkList1 ys Hys'.
Proof.
  introv H. destruct xs as [xs Hxs]. simpl in *. injection H. intros. split;
    auto.
    clear H Hys. remember Hxs as Hys. clear HeqHys. rewrite H0 in Hxs.
    exists Hxs. apply eq_list1_compat. auto.
Defined.

(*****************************************************************************)
(* Destruction                                                               *)

Inductive sig3 {A B C : Type} (P : A -> B -> C -> Prop) : Type :=
| exist3 : forall a b c, P a b c -> sig3 P.

Definition destruct_list1 {A} (xs : list1 A) :
  A + sig3 (fun x y zs => xs = cons1 x (list_to_list1 y zs)).
Proof.
  destruct xs as [xs HxsNE]. destruct xs as [_ | x xs'].
    exfalso. auto.
    destruct xs' as [_ | y zs].
      left. exact x.
      right. refine (exist3 _ x y zs _). simpl. apply eq_list1_compat. trivial.
Defined.
Hint Unfold destruct_list1 : list1.

Definition destruct_list1_weak {A} (xs : list1 A) : A + (A * A * list A).
  destruct (destruct_list1 xs) as [l | r]; [left | right; inverts r]; auto.
Defined.
Hint Unfold destruct_list1_weak : list1.

Definition head1 {A} (xs : list1 A) : A :=
  match destruct_list1_weak xs with
  | inl x => x
  | inr (x, _, _) => x
  end
.

(*****************************************************************************)
(* Membership                                                                *)

Definition In1 := In.
Hint Unfold In1 : list1.

Lemma In1_dec {A} :
  (forall (x y : A), {x = y} + {x <> y}) ->
  forall (x : A) (xs : list1 A),
  {In1 A x xs} + {~In1 A x xs}.
Proof with auto.
  introv Hdec. intros. destruct xs as [xs Hxs]. destruct (in_dec Hdec x xs)...
Defined.
Hint Resolve In1_dec : list1.

(*****************************************************************************)
(* Folding                                                                   *)

Definition fold_left1 {A B} (f : B -> A -> B) (xs : list1 A) (b0 : B) :=
  fold_left f (proj1_sig xs) b0.
Hint Unfold fold_left1 : list1.
Arguments fold_left1 / _ _ _ _ _.

(*****************************************************************************)
(* Misc. operations                                                          *)

Definition app1 {A} (xs : list1 A) (ys : list A) : list1 A.
  refine (
    match xs with
    | (existT xs' _) => existT _ (xs' ++ ys) _
    end
  ).
  destruct xs' as [_ | x xs'].
    exfalso; auto.
    simpl. apply cons_not_nil.
Defined.

Definition rev1 {A} (xs : list1 A) : list1 A.
  refine (
    match xs with
    | existT xs' _ => existT _ (rev xs') _
    end
  ).
  destruct xs' as [_ | x xs']; auto.
    simpl. apply nonempty_app.
    unfold nonempty; unfold not; intros; discriminate.
Defined.

(*****************************************************************************)
(* Well-founded induction                                                    *)

Definition lt_list1 {A} (xs ys : list1 A) :=
  exists x, x :: projT1 xs = projT1 ys.

Definition lt_list1_sub {A B} (xs ys : {_ : list1 A & B}) :=
  exists x, x :: projT1 (projT1 xs) = projT1 (projT1 ys).

Lemma lt_list1_sub_wf' :
  forall A B (xs : list A) (x : A) (ys : {_ : list1 A & B}),
  (exists x, projT1 (projT1 ys) = (x :: xs)) ->
  Acc lt_list1_sub ys.
Proof.
  intro. induction xs.
    intros x ys H. constructor. intros xs Hsub. exfalso.
    destruct ys as [ys bys]. destruct ys as [ys HysNE].
    destruct xs as [xs bxs]. destruct xs as [xs HxsNE].
    unfold lt_list1_sub in *. simpl in *. destruct H as [y Hys].
    destruct Hsub as [a Hys']. subst. inverts Hys'. auto.

    intros y ys H. destruct H as [x Hx]. constructor. intros y' Hsub.
    apply IHxs. assumption. clear IHxs. inverts Hsub. rewrite Hx in H.
    injection H. eauto.
Defined.

Lemma lt_list1_sub_wf :
  forall A B,
  well_founded (lt_list1_sub (A := A) (B := B)).
Proof.
  unfold well_founded. intros. destruct a as [a b]. destruct a as [a HaNE].
  destruct a as [_ | x xs].
    exfalso; auto.
    eapply lt_list1_sub_wf'.
      assumption.
      simpl. eauto.
Defined.

Lemma lt_list1_wf' :
  forall A (xs : list A) (x : A) (ys : list1 A),
  (exists x, projT1 ys = (x :: xs)) ->
  Acc lt_list1 ys.
Proof.
  intro. induction xs.
    intros x ys H. constructor. intros xs Hsub. exfalso.
    destruct ys as [ys HysNE].
    destruct xs as [xs HxsNE].
    unfold lt_list1_sub in *. simpl in *. destruct H as [y Hys].
    destruct Hsub as [a Hys']. subst. inverts Hys'. auto.

    intros y ys H. destruct H as [x Hx]. constructor. intros y' Hsub.
    apply IHxs. assumption. clear IHxs. inverts Hsub. rewrite Hx in H.
    injection H. eauto.
Defined.

Lemma lt_list1_wf :
  forall A,
  well_founded (lt_list1 (A := A)).
Proof.
  unfold well_founded. intros. destruct a as [a HaNE].
  destruct a as [_ | x xs].
    exfalso; auto.
    eapply lt_list1_wf'.
      assumption.
      simpl. eauto.
Defined.

Lemma Acc_eta :
  forall A (R : A -> A -> Prop) x,
  Acc R x ->
  Acc (fun x y => R x y) x.
Proof. introv Hacc. induction Hacc. constructor. auto. Defined.

Lemma wf_eta :
  forall A (R : A -> A -> Prop),
  well_founded R ->
  well_founded (fun x y => R x y).
Proof.
  introv Hwf. constructor. introv HRya. apply Acc_eta. unfolds in Hwf. auto.
Defined.

(* TODO my lord, that proof... *)
Lemma list1_ind' :
  forall A (P : list1 A -> Prop),
  (forall x, P (singleton1 x)) ->
  (forall x xs, P xs -> P (cons1 x xs)) ->
  forall xs, P xs.
Proof.
  introv Hsingle Hcons. apply well_founded_induction with (R := lt_list1).
    apply lt_list1_wf.
    introv H. destruct x as [xs HxsNE].
    remember HxsNE as HxsNE'. clear HeqHxsNE'.
    apply nonempty_inv in HxsNE. destruct HxsNE as [y HxsNE].
    destruct HxsNE as [ys Hxs].
    assert (existT (fun xs0 => nonempty xs0) xs HxsNE' =
            existT (fun xs0 => nonempty xs0) (y :: ys) (cons_not_nil A y ys)) as H0.
      apply eq_list1_compat. auto.
    rewrite H0. destruct ys.
      unfold singleton1 in Hsingle. apply Hsingle.
      assert (existT (fun xs => nonempty xs) (y :: a :: ys) (cons_not_nil A y (a :: ys)) =
              cons1 y (list_to_list1 a ys)) as H1.
        apply eq_list1_compat. trivial.
      rewrite H1. apply Hcons. simpl. apply H. unfold mkList1. unfold lt_list1.
      assert (existT (fun xs0 => nonempty xs0) xs HxsNE' =
              existT nonempty (y :: a :: ys) (cons_not_nil A y (a :: ys))) as H2.
        apply eq_list1_compat. trivial.
      rewrite H2. exists y. simpl. trivial.
Qed.
