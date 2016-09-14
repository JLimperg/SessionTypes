Require Import Classical Ensembles Msg Sty Tac TL TLFacts Var.

Create HintDb tlsets discriminated.


Inductive Letter : Set :=
| LEchoice0 : Letter
| LEchoice1 : Letter
| LIchoice0 : Letter
| LIchoice1 : Letter
| LSend : Msg -> Letter
| LRecv : Msg -> Letter
.


CoInductive CoList A :=
| Nil : CoList A
| Cons : A -> CoList A -> CoList A
.

Arguments Nil [_].
Arguments Cons [_] _ _.


Definition Trace := CoList Letter.

Definition epsilon : Trace := Nil.


Definition TlSet := Ensemble Trace.


Inductive Cons_Ens {A} (x : A) (U : Ensemble (CoList A)) : Ensemble (CoList A) :=
| Cons_Ens_intro :
    forall t,
    U t ->
    Cons_Ens x U (Cons x t)
.


Lemma Cons_Ens_injective :
  forall A x y (U U' : Ensemble (CoList A)),
  Inhabited U ->
  Same_set (Cons_Ens x U) (Cons_Ens y U') ->
  x = y /\ Same_set U U'.
Proof.
  introv Hinhab. apply contrapositive. introv H Hcontra. apply not_and_or in H.
  unfold Same_set in *. norm_hyp_auto.
  - unfold Included, In in H0. contradict H0. apply not_forall__exists_not.
    inversion_clear Hinhab as [xs ?]. exists (Cons x xs). introv Hcontra.
    apply imply_to_or in Hcontra. destruct Hcontra.
    * apply H2. constructor. auto.
    * inverts H2. false.
  - apply not_and_or in H. norm_hyp_auto.
    * apply not_Included__counterexample in H. norm_hyp_auto. contradict H0.
      apply not_Included__counterexample. unfold In in *. eexists. split.
      + constructor. eauto.
      + introv Hcontra. inverts Hcontra. auto.
    * apply not_Included__counterexample in H. norm_hyp_auto. contradict H1.
      apply not_Included__counterexample. unfold In in *. eexists. split.
      + constructor. eauto.
      + introv Hcontra. inverts Hcontra. auto.
Qed.


Lemma Cons_Ens__Disjoint :
  forall U a b (A B : Ensemble (CoList U)),
  a <> b ->
  Disjoint (Cons_Ens a A) (Cons_Ens b B).
Proof.
  introv Hneq. constructor. introv Hcontra.
  inversion_clear Hcontra as [? Hc1 Hc2]; inverts Hc1; inverts Hc2; false.
Qed.


CoInductive tlset : Tl -> TlSet :=
| tlset_unit :
    tlset Tl_unit epsilon
| tlset_send :
    forall l B t,
    tlset l t ->
    tlset (Tl_send B l) (Cons (LSend B) t)
| tlset_recv :
    forall l B t,
    tlset l t ->
    tlset (Tl_recv B l) (Cons (LRecv B) t)
| tlset_echoice0 :
    forall l0 l1 t0,
    tlset l0 t0 ->
    tlset (Tl_echoice l0 l1) (Cons LEchoice0 t0)
| tlset_echoice1 :
    forall l0 l1 t1,
    tlset l1 t1 ->
    tlset (Tl_echoice l0 l1) (Cons LEchoice1 t1)
| tlset_ichoice0 :
    forall l0 l1 t0,
    tlset l0 t0 ->
    tlset (Tl_ichoice l0 l1) (Cons LIchoice0 t0)
| tlset_ichoice1 :
    forall l0 l1 t1,
    tlset l1 t1 ->
    tlset (Tl_ichoice l0 l1) (Cons LIchoice1 t1)
.


CoFixpoint tlset_member (l : Tl) : Trace :=
  match l with
  | Tl_unit => epsilon
  | Tl_send B l' => Cons (LSend B) (tlset_member l')
  | Tl_recv B l' => Cons (LRecv B) (tlset_member l')
  | Tl_echoice l0 l1 => Cons (LEchoice0) (tlset_member l0)
  | Tl_ichoice l0 l1 => Cons (LIchoice0) (tlset_member l0)
  end
.


Definition id_CoList {A} (xs : CoList A) : CoList A :=
  match xs with
  | Nil => Nil
  | Cons x xs' => Cons x xs'
  end
.

Lemma id_CoList_id :
  forall A (xs : CoList A),
  xs = id_CoList xs.
Proof. intros. destruct xs; auto. Qed.


Lemma tlset_member_member :
  forall l,
  In (tlset l) (tlset_member l).
Proof.
  unfold In. cofix CIH. intros; destruct l;
    rewrite id_CoList_id; simpl; constructor; apply CIH.
Qed.


Lemma tlset_Inhabited :
  forall l,
  Inhabited (tlset l).
Proof.
  intros. apply Inhabited_intro with (tlset_member l).
  apply tlset_member_member.
Qed.


Lemma tlset_inv_unit :
  tlset Tl_unit = Singleton epsilon.
Proof.
  apply Extensionality_Ensembles. unfold Same_set, Included, In. split;
    introv H; inverts H; constructor.
Qed.


Lemma tlset_inv_send :
  forall l B,
  tlset (Tl_send B l) = Cons_Ens (LSend B) (tlset l).
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set, Included, In. split;
    introv H; inverts H; constructor; assumption.
Qed.


Lemma tlset_inv_recv :
  forall l B,
  tlset (Tl_recv B l) = Cons_Ens (LRecv B) (tlset l).
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set, Included, In. split;
    introv H; inverts H; constructor; assumption.
Qed.


Lemma tlset_inv_echoice :
  forall l0 l1,
  tlset (Tl_echoice l0 l1) =
    Union (Cons_Ens LEchoice0 (tlset l0)) (Cons_Ens LEchoice1 (tlset l1)).
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set, Included, In. split;
    introv H.
  - inverts H; solve [constructor; constructor; assumption].
  - inverts2 H; constructor; assumption.
Qed.


Lemma tlset_inv_ichoice :
  forall l0 l1,
  tlset (Tl_ichoice l0 l1) =
    Union (Cons_Ens LIchoice0 (tlset l0)) (Cons_Ens LIchoice1 (tlset l1)).
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set, Included, In. split;
    introv H.
  - inverts H; solve [constructor; constructor; assumption].
  - inverts2 H; constructor; assumption.
Qed.


Lemma tlset_echoice_injective :
  forall l0 l1 l0' l1',
  Same_set (tlset (Tl_echoice l0 l1)) (tlset (Tl_echoice l0' l1')) ->
  Same_set (tlset l0) (tlset l0') /\ Same_set (tlset l1) (tlset l1').
Proof.
  introv H. rewrite_strat (subterms tlset_inv_echoice) in H.
  apply disjoint_union__Same_set__inv in H. destruct H as [H H'].
  apply Cons_Ens_injective in H. apply Cons_Ens_injective in H'.
  destruct H, H'.
  - auto.
  - apply tlset_Inhabited.
  - apply tlset_Inhabited.
  - apply Cons_Ens__Disjoint; autodiscriminate.
  - apply Cons_Ens__Disjoint; autodiscriminate.
Qed.


Lemma tlset_ichoice_injective :
  forall l0 l1 l0' l1',
  Same_set (tlset (Tl_ichoice l0 l1)) (tlset (Tl_ichoice l0' l1')) ->
  Same_set (tlset l0) (tlset l0') /\ Same_set (tlset l1) (tlset l1').
Proof.
  introv H. rewrite_strat (subterms tlset_inv_ichoice) in H.
  apply disjoint_union__Same_set__inv in H. destruct H as [H H'].
  apply Cons_Ens_injective in H. apply Cons_Ens_injective in H'.
  destruct H, H'.
  - auto.
  - apply tlset_Inhabited.
  - apply tlset_Inhabited.
  - apply Cons_Ens__Disjoint; autodiscriminate.
  - apply Cons_Ens__Disjoint; autodiscriminate.
Qed.


Section Bisim_tlset.


Hint Constructors tlset.


Lemma tl_bisim_tlset_inclusion :
  forall l l',
  Tl_bisim l l' ->
  Included (tlset l) (tlset l').
Proof using.
  unfold Included, In. cofix CIH. introv Hbisim Hl.
  inverts1 Hl; inverts2 Hbisim; solve [econstructor; eapply CIH; eassumption].
Qed.


Lemma Tl_bisim__tlset_eq :
  forall l l',
  Tl_bisim l l' ->
  Same_set (tlset l) (tlset l').
Proof using.
  introv H. unfold Same_set. split; apply tl_bisim_tlset_inclusion.
  - assumption.
  - symmetry. assumption.
Qed.


(* TODO beautify *)
Lemma tlset_eq__Tl_bisim :
  forall l l',
  Same_set (tlset l) (tlset l') ->
  Tl_bisim l l'.
Proof.
  Ltac contradict_Same_set H counter_example :=
    let Hcontra := fresh in
    contradict H;
    apply counterexample__not_Same_set__l with (x := counter_example);
    split;
    [ constructor; apply tlset_member_member
    | introv Hcontra; inverts2 Hcontra
    ]
  .

  apply Tl_bisim_coind. introv H. destruct l, l'.
  - constructor.
  - contradict_Same_set H epsilon.
  - contradict_Same_set H epsilon.
  - contradict_Same_set H epsilon.
  - contradict_Same_set H epsilon.

  - contradict_Same_set H (Cons (LSend m) (tlset_member l)).
  - rewrite_all tlset_inv_send in H. apply Cons_Ens_injective in H.
    * inversion_clear H as [Heq ?]. inverts Heq. constructor. assumption.
    * apply tlset_Inhabited.
  - contradict_Same_set H (Cons (LSend m) (tlset_member l)).
  - contradict_Same_set H (Cons (LSend m) (tlset_member l)).
  - contradict_Same_set H (Cons (LSend m) (tlset_member l)).

  - contradict_Same_set H (Cons (LRecv m) (tlset_member l)).
  - contradict_Same_set H (Cons (LRecv m) (tlset_member l)).
  - rewrite_all tlset_inv_recv in H. apply Cons_Ens_injective in H.
    * inversion_clear H as [Heq ?]. inverts Heq. constructor. assumption.
    * apply tlset_Inhabited.
  - contradict_Same_set H (Cons (LRecv m) (tlset_member l)).
  - contradict_Same_set H (Cons (LRecv m) (tlset_member l)).

  - contradict_Same_set H (Cons LEchoice0 (tlset_member l1)).
  - contradict_Same_set H (Cons LEchoice0 (tlset_member l1)).
  - contradict_Same_set H (Cons LEchoice0 (tlset_member l1)).
  - apply tlset_echoice_injective in H. constructor; auto.
  - contradict_Same_set H (Cons LEchoice0 (tlset_member l1)).

  - contradict_Same_set H (Cons LIchoice0 (tlset_member l1)).
  - contradict_Same_set H (Cons LIchoice0 (tlset_member l1)).
  - contradict_Same_set H (Cons LIchoice0 (tlset_member l1)).
  - contradict_Same_set H (Cons LIchoice0 (tlset_member l1)).
  - apply tlset_ichoice_injective in H. constructor; auto.
Qed.


End Bisim_tlset.