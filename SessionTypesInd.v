Require Import Arith.Wf_nat Relations.Relation_Operators
  Wellfounded.Lexicographic_Product.
Require Import SessionTypes Substitution Tac Var Wellformed.

(*****************************************************************************)
(* Construction order *)


Inductive lt_Sty : Sty -> Sty -> Prop :=
| lt_Sty_send :
    forall S B, lt_Sty S (send B S)
| lt_Sty_recv :
    forall S B, lt_Sty S (recv B S)
| lt_Sty_echoice_l :
    forall S1 S2, lt_Sty S1 (echoice S1 S2)
| lt_Sty_echoice_r :
    forall S1 S2, lt_Sty S2 (echoice S1 S2)
| lt_Sty_ichoice_l :
    forall S1 S2, lt_Sty S1 (ichoice S1 S2)
| lt_Sty_ichoice_r :
    forall S1 S2, lt_Sty S2 (ichoice S1 S2)
| lt_Sty_mu :
    forall S X, lt_Sty S (mu X S)
.


Lemma lt_Sty_wf : well_founded lt_Sty.
Proof. red. induction a; constructor; introv H; inverts H; auto. Defined.


Definition lt_Sty2 : Sty * Sty -> Sty * Sty -> Prop
  := symprod Sty Sty lt_Sty lt_Sty.


Lemma lt_Sty2_wf : well_founded lt_Sty2.
Proof. apply wf_symprod; apply lt_Sty_wf. Defined.


(*****************************************************************************)
(* Order by length of longest prefix consisting only of mu constructors *)


Fixpoint mu_prefix_count (x : Sty) : nat :=
  match x with
  | mu _ x' => S (mu_prefix_count x')
  | _ => 0
  end
.


Definition lt_Sty_mu_prefix : Sty -> Sty -> Prop :=
  ltof Sty mu_prefix_count.
Hint Unfold lt_Sty_mu_prefix.
Hint Unfold ltof.


Lemma lt_Sty_mu_prefix_wf : well_founded lt_Sty_mu_prefix.
Proof. apply well_founded_ltof. Defined.


Lemma lt_Sty_mu_prefix_subst :
  forall S X R,
  ok_some S ->
  lt_Sty_mu_prefix (subst X R S) (mu X S).
Proof.
  intros S X R; induction S; introv Hok; try solve [constructor].
    simpl. destruct (beq_var X v).
      constructor.

      decompose_ex Hok. inverts Hok. unfold lt_Sty_mu_prefix in *.
      unfold ltof in *. simpl in *. apply Lt.lt_n_S. eauto.

    inverts2 Hok.
Qed.


(*****************************************************************************)
(* The same for symmetric products *)


Definition lt_Sty_mu_prefix2 : Sty * Sty -> Sty * Sty -> Prop :=
  symprod Sty Sty lt_Sty_mu_prefix lt_Sty_mu_prefix.
Hint Unfold lt_Sty_mu_prefix2.
Hint Constructors symprod.


Lemma lt_Sty_mu_prefix2_wf : well_founded lt_Sty_mu_prefix2.
Proof. apply wf_symprod; apply lt_Sty_mu_prefix_wf. Defined.


Lemma Sty_ind_mu_prefix2 :
  forall (P : Sty -> Sty -> Prop),
  (forall S S',
    (forall T T', lt_Sty_mu_prefix2 (T, T') (S, S') -> P T T') ->
    P S S') ->
  forall S S', P S S'.
Proof.
  intro P. apply (well_founded_induction_type_2 P lt_Sty_mu_prefix2_wf).
Qed.
