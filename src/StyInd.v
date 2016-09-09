Require Import Sty Tac Var Wellfounded_Syncprod.
Require Import Arith.Wf_nat Relations.Relation_Operators
  Wellfounded.Lexicographic_Product.

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
