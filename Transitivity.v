Require Import Equivalence Reflexivity SessionTypes SessionTypesInd
  Substitution SubstitutionFacts Tac Wellformed.

Create HintDb trans discriminated.
Hint Resolve sequiv_reflexive : trans.


Inductive trans_helper : Sty -> Sty -> Prop :=
| trans_helper_trans :
    forall S T U,
    wellformed S ->
    wellformed T ->
    wellformed U ->
    sequiv S T ->
    sequiv T U ->
    trans_helper S U
.
Hint Constructors trans_helper : trans.

Lemma trans_helper_refl :
  forall S,
  wellformed S ->
  trans_helper S S.
Proof. eauto with trans. Qed.

Lemma sequiv_impl_trans_helper :
  forall S T,
  wellformed S ->
  wellformed T ->
  sequiv S T ->
  trans_helper S T.
Proof. eauto with trans. Qed.

Lemma trans_helper_transitive :
  (forall S T, trans_helper S T -> sequiv S T) ->
  (forall S T U,
    wellformed S ->
    wellformed T ->
    wellformed U ->
    sequiv S T ->
    sequiv T U ->
    sequiv S U
  ).
Proof. eauto with trans. Qed.


(* TODO beautify (a lot) *)
Theorem sequiv_transitive :
  forall S T U,
  wellformed S ->
  wellformed T ->
  wellformed U ->
  sequiv S T ->
  sequiv T U ->
  sequiv S U.
Proof.
  assert (
    forall X S,
    wellformed (mu X S) ->
    wellformed (subst X (mu X S) S)
  ) as L1 by skip.

  apply trans_helper_transitive. apply sequiv_coind.
  introv H. rename S' into U. inverts H.
  assert (exists csT, cs T csT) as HcsT by eauto using cs_ex.
  decompose_ex_auto.
  assert (sequiv S csT) as HSeqT by (
    eapply cs_preserves_sequiv_r with (S := S) (S' := T);
    eauto using cs_preserves_sequiv_l
  ).
  assert (sequiv csT U) as HTeqU by (
    eapply cs_preserves_sequiv_l with (S := T) (S' := U);
    eauto using cs_preserves_sequiv_r
  ).
  clear H3 H4. inverts2 HSeqT; inverts2 HTeqU.

  (* unit *)
  - auto.

  - constructor. apply sequiv_impl_trans_helper; auto.

  (* send *)
  - constructor. apply trans_helper_trans with (T := S'); eauto with wf.
      assert (wellformed (send B S')) by
        (eapply cs_preserves_wellformedness; eauto with wf).
      eauto with wf.

  - constructor. apply trans_helper_trans with (T := send B S'); eauto with wf.
      eapply cs_preserves_wellformedness; eauto with wf.

  (* recv *)
  - constructor. apply trans_helper_trans with (T := S'); eauto with wf.
      assert (wellformed (recv B S')) by
        (eapply cs_preserves_wellformedness; eauto with wf).
      eauto with wf.

  - constructor. apply trans_helper_trans with (T := recv B S'); eauto with wf.
      eapply cs_preserves_wellformedness; eauto with wf.

  (* echoice *)
  - assert (wellformed (echoice S1' S2')) by
      (eapply cs_preserves_wellformedness; eauto with wf).
    constructor.
    * apply trans_helper_trans with (T := S1'); eauto with wf.
    * apply trans_helper_trans with (T := S2'); eauto with wf.

  - assert (wellformed (echoice S1' S2')) by
      (eapply cs_preserves_wellformedness; eauto with wf).
    constructor. apply trans_helper_trans with (T := echoice S1' S2');
      eauto with wf.

  (* ichoice *)
  - assert (wellformed (ichoice S1' S2')) by
      (eapply cs_preserves_wellformedness; eauto with wf).
    constructor.
    * apply trans_helper_trans with (T := S1'); eauto with wf.
    * apply trans_helper_trans with (T := S2'); eauto with wf.

  - assert (wellformed (ichoice S1' S2')) by
      (eapply cs_preserves_wellformedness; eauto with wf).
    constructor. apply trans_helper_trans with (T := ichoice S1' S2');
      eauto with wf.

  (* unit *)
  - constructor. apply sequiv_impl_trans_helper; auto.

  (* send *)
  - constructor. apply trans_helper_trans with (T := send B S); auto.
      eauto using cs_preserves_wellformedness with wf.

  (* recv *)
  - constructor. apply trans_helper_trans with (T := recv B S); auto.
      eauto using cs_preserves_wellformedness with wf.

  (* echoice *)
  - constructor. apply trans_helper_trans with (T := echoice S1 S2); auto.
      eauto using cs_preserves_wellformedness with wf.

  (* ichoice *)
  - constructor. apply trans_helper_trans with (T := ichoice S1 S2); auto.
      eauto using cs_preserves_wellformedness with wf.

  (* mu 1 (impossible) *)
  - exfalso; eauto using cs_mu_absurd.

  (* mu 2 *)
  - constructor.
    assert (sequiv csT (mu X0 S')) as HTeqU' by auto.
    apply trans_helper_trans with (T := csT); eauto with wf.
      eauto using cs_preserves_wellformedness.

  (* mu 3 (impossible) *)
  - exfalso; eauto using cs_mu_absurd.

  (* mu 4 (impossible) *)
  - exfalso; eauto using cs_mu_absurd.
Qed.
