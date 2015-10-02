Require Import List Logic.ProofIrrelevance TLC.LibTactics.
Import ListNotations.

Create HintDb list1 discriminated.

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

Definition list1 (A : Type) := { xs : list A & nonempty xs }.

Definition inj_list1_list (A : Type) (xs : list1 A) : list A :=
  @proj1_sig (list A) nonempty xs.

Coercion inj_list1_list : list1 >-> list.

Definition mkList1 {A} (xs : list A) (P : xs <> []) : list1 A :=
  existT nonempty xs P.
Hint Unfold mkList1 : list1.

Lemma cons_not_nil :
  forall A (x : A) xs,
  nonempty (x :: xs).
Proof. intros. unfold not; discriminate. Qed.

Definition list_to_list1 {A} (x : A) (xs : list A) : list1 A :=
  mkList1 (x :: xs) (cons_not_nil A x xs).
Arguments list_to_list1 / _ _ _.
Hint Unfold list_to_list1 : list1.

Definition eq_list1_compat :
  forall A (xs ys : list A),
  xs = ys ->
  forall xsnonempty ysnonempty, mkList1 xs xsnonempty = mkList1 ys ysnonempty.
Proof. unfold mkList1. intros. apply subsetT_eq_compat. assumption. Qed.
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

Definition In1 := In.
Hint Unfold In1 : list1.

Lemma In1_dec {A} :
  (forall (x y : A), {x = y} + {x <> y}) ->
  forall (x : A) (xs : list1 A),
  {In1 A x xs} + {~In1 A x xs}.
Proof with auto.
  introv Hdec. intros. destruct xs as [xs Hxs]. destruct (in_dec Hdec x xs)...
Qed.
Hint Resolve In1_dec : list1.

Definition fold_left1 {A B} (f : B -> A -> B) (xs : list1 A) (b0 : B) :=
  fold_left f (proj1_sig xs) b0.
Hint Unfold fold_left1 : list1.
Arguments fold_left1 / _ _ _ _ _.

Definition head1 {A} (xs : list1 A) : A.
destruct xs as [xs HxsNE]. apply nonempty_inv in HxsNE. destruct xs.
  exfalso. destruct HxsNE as [x HxsNE]. destruct HxsNE. discriminate.
  apply a.
Qed.

Definition singleton1 {A} (x : A) := mkList1 [x] (cons_not_nil A x []).

Definition cons1 {A} (x : A) (xs : list1 A) : list1 A :=
  match xs with
  | existT xs' _ => mkList1 (x :: xs') (cons_not_nil A x xs')
  end
.

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
Qed.

Definition lt_list1 {A} (xs ys : list1 A) := exists x, (cons1 x xs) = ys.

Lemma lt_list1_wf' :
  forall A (xs : list A) (x : A) (ys : list1 A),
  (exists x, ys = mkList1 (x :: xs) (cons_not_nil A x xs)) ->
  Acc lt_list1 ys.
Proof.
  intro. induction xs.
    intros x ys H. inverts H. constructor. intros. destruct y. inverts H.
    inverts H0. unfold not in *. exfalso. auto.

    intros x ys H. inverts H. constructor. intros y Hy. apply IHxs; auto.
    exists a. inverts Hy. apply cons1_inv in H. destruct H. destruct H0.
    rewrite H0. auto with list1.
Qed.

(* TODO refactor the remember; clear; destruct; destruct dance into a
   custom tactic. *)
Lemma lt_list1_wf : forall A, well_founded (lt_list1 (A := A)).
Proof.
  unfold well_founded. intros. destruct a as [a HaNE].
  remember HaNE as HaNE'. clear HeqHaNE'. apply nonempty_inv in HaNE.
  destruct HaNE as [x HaNE]. destruct HaNE as [xs Ha].
  apply lt_list1_wf' with (xs := xs).
    assumption.
    exists x. apply eq_list1_compat. assumption.
Qed.

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

(* TODO the following is currently unused *)

Definition length1 {A} (xs : list1 A) := length xs.

Definition length_order {A} (xs ys : list1 A) := length1 xs < length1 ys.

Lemma length_order_wf' :
  forall A len (xs : list1 A),
  length1 xs < len ->
  Acc length_order xs.
Proof.
  unfold length_order. induction len; introv H.
    contradict H. auto with arith.
    constructor. intros. eauto with arith.
Defined.

Lemma length_order_wf : forall A, well_founded (length_order (A := A)).
Proof. red. intros. eapply length_order_wf'. eauto. Defined.
