Require Import Classical Tac.
Require Import Coq.Classes.RelationClasses Coq.Classes.Morphisms
  Coq.Classes.SetoidTactics Coq.Program.Basics.
Require Export Coq.Sets.Classical_sets.

Import ProperNotations.


Create HintDb ens discriminated.


Arguments In {_} _ _.
Arguments Included {_} _ _.
Arguments Empty_set {_} _.
Arguments Full_set {_} _.
Arguments Singleton {_} _ _.
Arguments Union {_} _ _ _.
Arguments Add {_} _ _ _.
Arguments Intersection {_} _ _ _.
Arguments Couple {_} _ _ _.
Arguments Triple {_} _ _ _ _.
Arguments Complement {_} _ _.
Arguments Setminus {_} _ _ _.
Arguments Subtract {_} _ _ _.
Arguments Disjoint {_} _ _.
Arguments Inhabited {_} _.
Arguments Strict_Included {_} _ _.
Arguments Same_set {_} _ _.


Hint Unfold In Included Add Complement Setminus Subtract Strict_Included
  Same_set : ens.
Hint Constructors Full_set Singleton Union Intersection Couple Triple Disjoint
  Inhabited : ens.


(* -------------------------------------------------------------------------- *)
(* Properties of Same_set *)


Instance Same_set_reflexive {U} : Reflexive (@Same_set U).
Proof. red. auto with ens. Qed.


Instance Same_set_symmetric {U} : Symmetric (@Same_set U).
Proof. red. auto with ens. Qed.


Instance Same_set_transitive {U} : Transitive (@Same_set U).
Proof. red. unfold Same_set. intuition (auto with ens). Qed.


Instance Same_set_Equivalence {U} : Equivalence (@Same_set U).
Proof. typeclass. Qed.


Instance subrelation__Same_set__Included U :
  subrelation (@Same_set U) (@Included U).
Proof. red. unfold Same_set. auto. Qed.


Instance subrelation__Same_set__flip_Included U :
  subrelation (@Same_set U) (flip (@Included U)).
Proof. red. unfold Same_set. auto. Qed.


(* -------------------------------------------------------------------------- *)
(* Properties of Strict_Included *)


Instance Strict_Included_irreflexive {U} : Irreflexive (@Strict_Included U).
Proof. red. red. unfold complement. introv Hcontra. inverts Hcontra. false. Qed.


Instance Strict_Included_transitive {U} : Transitive (@Strict_Included U).
Proof.
  red. unfold Same_set. unfold Strict_Included. introv Hxy Hyz. norm_hyp_auto.
  split.
  - intuition (auto with ens).
  - intro. subst.
    assert (y = z) by (apply Extensionality_Ensembles; auto with ens). false.
Qed.


Instance Strict_Included_Strict_Order {U} : StrictOrder (@Strict_Included U).
Proof. typeclass. Qed.


(* -------------------------------------------------------------------------- *)
(* Properties of Included *)


Instance subrelation__Strict_Included__Included {U} :
  subrelation (@Strict_Included U) (@Included U).
Proof. red. auto with ens. Qed.


Instance Included_reflexive {U} : Reflexive (@Included U).
Proof. auto with ens. Qed.


Instance Included_transitive {U} : Transitive (@Included U).
Proof. red. unfold Same_set. intuition (auto with ens). Qed.


Instance Included_antisymmetric {U} :
  Antisymmetric (Ensemble U) (@Same_set U) (@Included U).
Proof. red. unfold Same_set; auto. Qed.


Instance Included_PreOrder {U} : PreOrder (@Included U).
Proof. typeclass. Qed.


Instance Included_PartialOrder {U} : PartialOrder (@Same_set U) (@Included U).
Proof. typeclass. Qed.


(* -------------------------------------------------------------------------- *)
(* Properties of Union *)


Lemma Union_sym :
  forall U (A B : Ensemble U),
  Same_set (Union A B) (Union B A).
Proof. split; red; introv H; inverts H; auto with ens. Qed.


Lemma Union_neutral_r :
  forall U (A : Ensemble U),
  Same_set (Union A Empty_set) A.
Proof.
  split; red; introv H.
  - inverts1 H; [assumption | inverts H].
  - auto with ens.
Qed.


Lemma Union_neutral_l :
  forall U (A : Ensemble U),
  Same_set (Union Empty_set A) A.
Proof. intros. rewrite Union_sym. apply Union_neutral_r. Qed.


Lemma Union_absorption_r :
  forall U (A : Ensemble U),
  Same_set (Union A Full_set) Full_set.
Proof. split; red; introv H; [inverts H|]; auto with ens. Qed.


Lemma Union_absorption_l :
  forall U (A : Ensemble U),
  Same_set (Union Full_set A) Full_set.
Proof. intros. rewrite Union_sym. apply Union_absorption_r. Qed.


Lemma Union_same :
  forall U (A : Ensemble U),
  Same_set (Union A A) A.
Proof. split; red; introv H; [inverts H|]; auto with ens. Qed.


(* -------------------------------------------------------------------------- *)
(* Properties of Intersection *)


Lemma Intersection_sym :
  forall U (A B : Ensemble U),
  Same_set (Intersection A B) (Intersection B A).
Proof. split; introv H; inverts H; auto with ens. Qed.


Lemma Intersection_neutral_r :
  forall U (A : Ensemble U),
  Same_set (Intersection A Full_set) A.
Proof. split; red; introv H; [inverts H|]; auto with ens. Qed.


Lemma Intersection_neutral_l :
  forall U (A : Ensemble U),
  Same_set (Intersection Full_set A) A.
Proof. intros. rewrite Intersection_sym. apply Intersection_neutral_r. Qed.


Lemma Intersection_absorption_r :
  forall U (A : Ensemble U),
  Same_set (Intersection A Empty_set) Empty_set.
Proof. split; red; introv H; inverts H; auto. Qed.


Lemma Intersection_absorption_l :
  forall U (A : Ensemble U),
  Same_set (Intersection Empty_set A) Empty_set.
Proof. intros. rewrite Intersection_sym. apply Intersection_absorption_r. Qed.


Lemma Intersection_same :
  forall U (A : Ensemble U),
  Same_set (Intersection A A) A.
Proof. split; red; introv H; [inverts H|]; auto with ens. Qed.


(* -------------------------------------------------------------------------- *)
(* Properties of Disjoint *)


Instance Disjoint_symmetric {U} : Symmetric (@Disjoint U).
Proof.
  introv H. inverts1 H. constructor. intro a. specialize H with a.
  contradict H. inverts H; auto with ens.
Qed.


(* -------------------------------------------------------------------------- *)
(* Morphisms *)


Instance morph__In__Same_set {U} :
  Proper (Same_set ==> eq ==> iff) (@In U).
Proof.
  unfold Proper, respectful. introv Heqset Heq. subst. inverts Heqset.
  intuition (auto with ens).
Qed.


Instance morph__Included__Same_set {U} :
  Proper (eq ==> Same_set ==> iff) (@Included U).
Proof.
  unfold Proper, respectful. introv Heq Heqset. subst. inverts Heqset.
  intuition.
Qed.


Instance morph__Union__Included {U} :
  Proper (Included ==> Included ==> Included) (@Union U).
Proof. unfold Proper, respectful. introv H1 H2 H. inverts H; auto with ens. Qed.


Instance morph__Union__Same_set {U} :
  Proper (Same_set ==> Same_set ==> Same_set) (@Union U).
Proof.
  unfold Proper, respectful. introv H1 H2.
  inversion H1 as [H11 H12]; inversion H2 as [H21 H22]; split.
  - rewrite H11, H21. reflexivity.
  - rewrite H12, H22. reflexivity.
Qed.


Instance morph__Add__Included {U} :
  Proper (Included ==> eq ==> Included) (@Add U).
Proof. unfold Add. solve_proper. Qed.


Instance morph__Add__Same_set {U} :
  Proper (Same_set ==> eq ==> Same_set) (@Add U).
Proof. unfold Add. solve_proper. Qed.


Instance morph__Intersection__Same_set {U} :
  Proper (Same_set ==> Same_set ==> Same_set) (@Intersection U).
Proof.
  unfold Proper, respectful, Same_set, Included. split; introv tmp;
    inverts tmp; intuition (auto with ens).
Qed.


Instance morph__Complement__Same_set {U} :
  Proper (Same_set ==> Same_set) (@Complement U).
Proof.
  unfold Proper, respectful. repeat autounfold with ens. iauto.
Qed.


Instance morph__Setminus__Same_set {U} :
  Proper (Same_set ==> Same_set ==> Same_set) (@Setminus U).
Proof.
  unfold Proper, respectful. repeat autounfold with ens. iauto.
Qed.


Instance morph__Subtract__Same_set {U} :
  Proper (Same_set ==> eq ==> Same_set) (@Subtract U).
Proof. unfold Subtract. solve_proper. Qed.


Instance morph__Disjoint__Same_set {U} :
  Proper (Same_set ==> Same_set ==> iff) (@Disjoint U).
Proof.
  unfold Proper, respectful.
  split; introv tmp; inverts tmp; constructor; intros;
    [rewrite <- H, <- H0 | rewrite H, H0]; auto.
Qed.


Instance morph__Inhabited__Same_set {U} :
  Proper (Same_set ==> iff) (@Inhabited U).
Proof.
  unfold Proper, respectful. split; introv tmp; inverts tmp; econstructor;
    [rewrite <- H | rewrite H]; eassumption.
Qed.


(* -------------------------------------------------------------------------- *)
(* Misc. Lemmas *)


Lemma not_Included__counterexample :
  forall U (A B : Ensemble U),
  ~ Included A B <->
  exists x, In A x /\ ~ In B x.
Proof.
  split.
  - introv Hnincl. unfold Included in Hnincl.
    rewrite not_forall__exists_not in Hnincl. inverts Hnincl.
    apply imply_to_and in H. eauto.
  - introv Hex Hcontra. norm_hyp_auto. auto with sets.
Qed.


Lemma not_Same_set__not_Included :
  forall U (A B : Ensemble U),
  ~ Same_set A B <->
  ~ Included A B \/ ~ Included B A.
Proof.
  split; introv H.
  - rewrite <- not_and__or. eauto.
  - rewrite <- not_and__or in H. auto with ens.
Qed.


Lemma not_Same_set__counterexample :
  forall U (A B : Ensemble U),
  ~ Same_set A B <->
  exists x, (In A x /\ ~ In B x) \/ (~ In A x /\ In B x).
Proof.
  split; introv H.
  - apply not_Same_set__not_Included in H. destruct H;
      apply not_Included__counterexample in H; eauto 10.
  - introv Hcontra. inverts1 Hcontra. destruct H as [? H]. destruct H; eauto.
Qed.


Lemma counterexample__not_Same_set__l :
  forall U (A B : Ensemble U) x,
  In A x /\ ~ In B x ->
  ~ Same_set A B.
Proof. introv H. apply not_Same_set__counterexample; eauto. Qed.


Lemma counterexample__not_Same_set__r :
  forall U (A B : Ensemble U) x,
  In B x /\ ~ In A x ->
  ~ Same_set A B.
Proof. introv H. apply not_Same_set__counterexample; eauto 10. Qed.


Lemma in_disjoint_union_inv :
  forall U (A B : Ensemble U) x,
  Disjoint A B ->
  In (Union A B) x ->
  (In A x /\ ~ In B x) \/ (~ In A x /\ In B x).
Proof.
  introv Hdis Hin. inverts1 Hdis. specialize Hdis with x.
  destruct (classic (In A x)); destruct (classic (In B x)); auto.
  - contradict Hdis. auto with ens.
  - inverts Hin; auto.
Qed.


Lemma disjoint_union__Setminus__r :
  forall U (A B : Ensemble U),
  Disjoint A B ->
  Same_set (Setminus (Union A B) B) A.
Proof.
  introv Hdis. inverts Hdis. split; red; introv Hin.
  - inversion Hin as [Hunion HB]. inverts Hunion; [assumption | false].
  - constructor.
    * auto with ens.
    * specialize H with x. contradict H. auto with ens.
Qed.


Lemma disjoint_union__Setminus__l :
  forall U (A B : Ensemble U),
  Disjoint A B ->
  Same_set (Setminus (Union A B) A) B.
Proof.
  intros. rewrite Union_sym. apply disjoint_union__Setminus__r.
  symmetry. assumption.
Qed.


Lemma disjoint_union_injective_r :
  forall U (A B B' : Ensemble U),
  Disjoint A B ->
  Disjoint A B' ->
  Same_set (Union A B) (Union A B') ->
  Same_set B B'.
Proof.
  introv Hdis Hdis' Heq.
  rewrite <- (disjoint_union__Setminus__l _ A B),
          <- (disjoint_union__Setminus__l _ A B'); [|assumption..].
  rewrite Heq. reflexivity.
Qed.


Lemma disjoint_union_injective_l :
  forall U (A A' B : Ensemble U),
  Disjoint A B ->
  Disjoint A' B ->
  Same_set (Union A B) (Union A' B) ->
  Same_set A A'.
Proof.
  introv Hdis Hdis' H. rewrite_strat (subterms Union_sym) in H.
  symmetry in Hdis, Hdis'. eapply disjoint_union_injective_r; eauto.
Qed.


Lemma Empty_or_Inhabited :
  forall U (A : Ensemble U),
  Same_set A Empty_set \/ Inhabited A.
Proof.
  intros. destruct (classic (exists x, In A x)) as [H | H].
  - right. inverts H. econstructor; eassumption.
  - left. unfold Same_set. split.
    * unfold Included. introv Hcontra. contradict H. eauto.
    * apply Included_Empty.
Qed.


Lemma disjoint_union__Same_set__inv_l :
  forall U (A A' B B' : Ensemble U),
  Disjoint A B' ->
  Disjoint B A' ->
  Same_set (Union A B) (Union A' B') ->
  Same_set A A'.
Proof.
  introv Hdis Hdis' Heq. split; red; introv H.
  * assert (In (Union A' B') x) as tmp by (rewrite <- Heq; auto with ens).
    inverts1 tmp.
    + assumption.
    + inverts1 Hdis. contradict Hdis; eauto with ens.
  * assert (In (Union A B) x) as tmp by (rewrite Heq; auto with ens).
    inverts1 tmp.
    + assumption.
    + inverts1 Hdis'. contradict Hdis'; eauto with ens.
Qed.


Lemma disjoint_union__Same_set__inv_r :
  forall U (A A' B B' : Ensemble U),
  Disjoint A B' ->
  Disjoint B A' ->
  Same_set (Union A B) (Union A' B') ->
  Same_set B B'.
Proof.
  intros until 0. intros ? ? Heq. rewrite_strat (subterms Union_sym) in Heq.
  eapply disjoint_union__Same_set__inv_l; eauto.
Qed.


Lemma disjoint_union__Same_set__inv :
  forall U (A A' B B' : Ensemble U),
  Disjoint A B' ->
  Disjoint B A' ->
  Same_set (Union A B) (Union A' B') ->
  Same_set A A' /\ Same_set B B'.
Proof.
  split; eauto using disjoint_union__Same_set__inv_l,
    disjoint_union__Same_set__inv_r.
Qed.