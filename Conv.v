Require Import Env List ListAux List1 Morphisms Msg Program.Basics SessionTypes
  SessionTypesC Shape TLC.LibTactics Var Vars Wellformed WellformedC.
Import ListNotations.

Module R := Sty.
Module C := StyC.

(*****************************************************************************)
(* Conversion                                                                *)

Fixpoint sty_styC_aux (xs : list Var) (S : R.Sty) : C.Sty :=
  match S with
  | R.unit => C.unit
  | R.send B S' => C.send B (sty_styC_aux [] S')
  | R.recv B S' => C.recv B (sty_styC_aux [] S')
  | R.echoice S1 S2 => C.echoice (sty_styC_aux [] S1) (sty_styC_aux [] S2)
  | R.ichoice S1 S2 => C.ichoice (sty_styC_aux [] S1) (sty_styC_aux [] S2)
  | R.mu x S' =>
    match S' with
    | R.mu _ _ => sty_styC_aux (x :: xs) S' (* [Note rev-variable-order] *)
    | _        => C.mu (list_to_list1 x xs) (sty_styC_aux [] S')
    end
  | R.var X => C.var X
  end
.
Arguments sty_styC_aux xs S : simpl nomatch.

(* [Note rev-variable-order]
Note that the variable ordering is reversed here: The regular session type

  mu X. mu Y. S

becomes the contracted session type

  mu [Y, X]. S

This makes no difference semantically since variable ordering in a chain of
binders is irrelevant, but it's easier to define. We'll see if the proofs
become more difficult as a result.
*)

Notation sty_styC := (sty_styC_aux []).

Fixpoint styC_sty (S : C.Sty) : R.Sty :=
  match S with
  | C.unit => R.unit
  | C.send B S' => R.send B (styC_sty S')
  | C.recv B S' => R.recv B (styC_sty S')
  | C.echoice S1 S2 => R.echoice (styC_sty S1) (styC_sty S2)
  | C.ichoice S1 S2 => R.ichoice (styC_sty S1) (styC_sty S2)
  | C.mu xs S' => fold_left1 (fun S X => R.mu X S) xs (styC_sty S')
    (* [Note fold-left-not-right] *)
  | C.var X => R.var X
  end
.

(* [Note fold-left-not-right]
The left fold reverses the variable ordering again to make sty_styC and
styC_sty inverses of each other (modulo some technicalities).
*)

(* TODO beautify *)
Lemma styC_sty_inverse_sty_styC_aux :
  forall S,
  (R.shape S <> muS ->
    forall xs, styC_sty (sty_styC_aux xs S) = S) /\
  (R.shape S = muS ->
    styC_sty (sty_styC_aux [] S) = S /\
    forall x xs,
    styC_sty (sty_styC_aux (xs ++ [x]) S) =
    R.mu x (styC_sty (sty_styC_aux xs S))).
Proof.
  induction S; split; introv Hshape; try discriminate; intros.
    simpl. trivial.

    simpl in *. destruct IHS as [IHSnomu IHSmu].
    destruct (R.shape_dec S muS) as [HSmu | HSnomu].
      apply IHSmu in HSmu. destruct HSmu as [H _]. rewrite H. trivial.
      rewrite IHSnomu; auto.

    simpl in *. destruct IHS as [IHSnomu IHSmu].
    destruct (R.shape_dec S muS) as [HSmu | HSnomu].
      apply IHSmu in HSmu. destruct HSmu as [H _]. rewrite H. trivial.
      rewrite IHSnomu; auto.

    simpl in *.
    destruct IHS1 as [IHS1nomu IHS1mu]. destruct IHS2 as [IHS2nomu IHS2mu].
      destruct (R.shape_dec S1 muS) as [HS1mu | HS1nomu];
      destruct (R.shape_dec S2 muS) as [HS2mu | HS2nomu].
        apply IHS1mu in HS1mu. destruct HS1mu as [H1 _]. rewrite H1.
        apply IHS2mu in HS2mu. destruct HS2mu as [H2 _]. rewrite H2.
        trivial.

        apply IHS1mu in HS1mu. destruct HS1mu as [H1 _]. rewrite H1.
        rewrite IHS2nomu; auto.

        rewrite IHS1nomu; auto.
        apply IHS2mu in HS2mu. destruct HS2mu as [H2 _]. rewrite H2. trivial.

        rewrite IHS1nomu; auto.
        rewrite IHS2nomu; auto.

    simpl in *.
    destruct IHS1 as [IHS1nomu IHS1mu]. destruct IHS2 as [IHS2nomu IHS2mu].
      destruct (R.shape_dec S1 muS) as [HS1mu | HS1nomu];
      destruct (R.shape_dec S2 muS) as [HS2mu | HS2nomu].
        apply IHS1mu in HS1mu. destruct HS1mu as [H1 _]. rewrite H1.
        apply IHS2mu in HS2mu. destruct HS2mu as [H2 _]. rewrite H2.
        trivial.

        apply IHS1mu in HS1mu. destruct HS1mu as [H1 _]. rewrite H1.
        rewrite IHS2nomu; auto.

        rewrite IHS1nomu; auto.
        apply IHS2mu in HS2mu. destruct HS2mu as [H2 _]. rewrite H2. trivial.

        rewrite IHS1nomu; auto.
        rewrite IHS2nomu; auto.

    unfold not in Hshape. exfalso. auto.

    destruct IHS as [IHSnomu IHSmu]. split.
      destruct S; simpl in *; try solve
        [trivial | rewrite IHSnomu; unfold not; try discriminate; auto; constructor].

        destruct IHSmu. auto. specialize H0 with (x := v) (xs := nil).
        simpl in H0. rewrite H in H0. assumption.

     intros. gen x. destruct S; intros; try solve
       [simpl; rewrite fold_left_snoc; trivial].

       destruct IHSmu. auto. simpl. specialize H0 with (x := x) (xs := (v :: xs)).
       assumption.

    auto.
Qed.

Lemma styC_sty_inverse_sty_styC :
  forall S,
  styC_sty (sty_styC S) = S.
Proof.
  intros. remember styC_sty_inverse_sty_styC_aux as H.
  edestruct H as [Hnomu Hmu]. destruct (R.shape_dec S muS);
    [apply Hmu | apply Hnomu]; auto.
Qed.

Lemma sty_styC_aux_mu_chain1 :
  forall xs ys x S,
  sty_styC_aux xs (fold_left1 (flip R.mu) ys (R.mu x S)) =
  sty_styC_aux (projT1 (app1 ys xs)) (R.mu x S).
Proof.
  intros. destruct ys as [ys HysNE]. simpl. unfold flip.
  rewrite <- fold_left_rev_right. gen x xs S. clear HysNE.
  induction ys; intros; auto.
    simpl in *. rewrite fold_right_app. simpl. rewrite IHys. auto.
Qed.

Lemma sty_styC_mu_chain2 :
  forall xs ys x S,
  R.shape S <> muS ->
  sty_styC_aux xs (fold_left1 (fun S X => R.mu X S) ys (R.mu x S)) =
  C.mu (cons1 x (app1 ys xs)) (sty_styC S).
Proof.
  assert (
    forall A (x : A) xs ys HxsNE,
    mkList1 (x :: projT1 (app1 xs ys)) HxsNE = cons1 x (app1 xs ys)
  ) as H.
    intros; destruct xs; destruct ys; simpl; apply eq_list1_compat; auto.

  introv Hsh. rewrite sty_styC_aux_mu_chain1.
  destruct S; try solve [simpl; rewrite H; auto]. exfalso; auto.
Qed.

Lemma sty_styC_inverse_styC_sty :
  forall S e,
  WfC.ok e S ->
  sty_styC (styC_sty S) = S.
Proof.
  induction S; introv H; simpl; trivial; try solve
    [inverts H; first [ erewrite IHS; eauto
                      | erewrite IHS1; eauto; erewrite IHS2; eauto
                      ]].

    induction l using list1_ind'.
      destruct S; simpl in *; trivial; inverts H; solve
        [erewrite IHS; eauto | exfalso; auto].

      destruct l. simpl in *.
      asserts_rewrite (
        fold_left (fun S X => R.mu X S) x0 (R.mu x (styC_sty S)) =
        fold_left1 (fun S X => R.mu X S) (mkList1 x0 n) (R.mu x (styC_sty S))
      ).
        auto.
      rewrite sty_styC_mu_chain2. simpl.
      asserts_rewrite (
        mkList1 (x :: x0 ++ []) (cons_not_nil Var x (x0 ++ [])) =
        mkList1 (x :: x0)       (cons_not_nil Var x x0)
      ).
        apply eq_list1_compat. simpl_list. auto.
      inverts H. erewrite IHS; eauto.
      inverts H. destruct S; auto.
Qed.

(*****************************************************************************)
(* Wellformedness                                                            *)

Lemma sty_styC_aux_ok_assoc :
  forall S e xs ys x y,
  WfC.ok e (sty_styC_aux (xs ++ x :: y :: ys) S) ->
  WfC.ok e (sty_styC_aux (xs ++ y :: x :: ys) S).
Proof.
  assert (
    forall e v xs x y ys HxsNE,
    env_eq (env_union_vars e (mkList1 (v :: xs ++ x :: y :: ys) HxsNE))
           (env_union_vars e (mkList1 (v :: xs ++ y :: x :: ys)
                               (cons_not_nil Var v (xs ++ y :: x :: ys))))
  ) as Hcomm.
    intros. repeat (rewrite env_union_vars_spec). simpl.
    asserts_rewrite (env_eq (list_to_env (xs ++ x :: y :: ys))
                            (list_to_env (xs ++ y :: x :: ys))).
      unfold env_eq. intro. repeat (rewrite SF.of_list_1).
      repeat (rewrite SetoidList.InA_app_iff); auto with typeclass_instances.
      repeat (rewrite SetoidList.InA_cons); auto with typeclass_instances.
      iauto.
    reflexivity.
  induction S; introv H; try solve [simpl; constructor; inverts H; auto].
    destruct S; simpl in *; try solve
      [ simpl in *; constructor; unfold not; try discriminate
      ; solve [constructor | inverts H; rewrite Hcomm; auto ]
      ].

      simpl in *. specialize IHS with (e := e) (xs := v :: xs). apply IHS.
      auto.

      inverts H. contradict H2. auto.
Qed.

Lemma sty_styC_aux_ok_assoc' :
  forall S e x y zs,
  WfC.ok e (sty_styC_aux (x :: y :: zs) S) ->
  WfC.ok e (sty_styC_aux (y :: x :: zs) S).
Proof.
  introv H. asserts_rewrite (y :: x :: zs = [] ++ y :: x :: zs). auto.
  apply sty_styC_aux_ok_assoc. auto.
Qed.

Lemma sty_styC_aux_ok_expansion :
  forall S e e' X,
  R.shape S = muS ->
  WfC.ok (env_add X e) (sty_styC_aux e' S) ->
  WfC.ok e (sty_styC_aux (X :: e') S).
Proof.
  assert (
    forall X e v e',
    env_eq (env_union_vars (env_add X e) (mkList1 (v :: e') (cons_not_nil Var v e')))
           (env_union_vars e (mkList1 (v :: X :: e') (cons_not_nil Var v (X :: e'))))
  ) as Heq.
    intros. repeat (rewrite env_union_vars_spec). simpl.
    rewrite env_union_add. rewrite env_add_assoc. reflexivity.

  induction S; introv Hsh H; try discriminate.
    destruct S; try solve
      [ simpl in *; constructor; unfold not; try discriminate
      ; first [solve [constructor] | inverts H; rewrite <- Heq; auto]
      ].

      simpl in *. apply sty_styC_aux_ok_assoc'. apply IHS; auto.

      simpl in *. inverts H. exfalso. auto.
Qed.

(* TODO extract the "unfold not; discriminate" dance into a tactic ("ineq"?) *)
(* TODO why is "auto with wf" not working? *)
Lemma sty_styC_aux_checked :
  forall S e e',
  Wf.checked e S ->
  WfC.ok e (sty_styC_aux e' S).
Proof.
  assert (
    forall v e e',
    env_subset (env_add v e)
               (env_union_vars e (mkList1 (v :: e') (cons_not_nil Var v e')))
  ) as Hsub.
    intros. rewrite env_union_vars_spec. unfold SF.of_list. simpl.
    rewrite <- env_add_union2. apply env_add_m_subset. auto with set.
  induction S; introv H; try solve
    [ auto with wf
    | simpl; do 2 (inverts H as H); asserts_rewrite (e = env_union_list e [])
    ; auto with wf
    ].

    destruct S; simpl in *;
      try solve
        [ constructor; unfold not; try discriminate; do 3 (inverts H as H)
        ; apply IHS; auto; rewrite <- Hsub; constructor; constructor; auto
        ].

      do 3 (inverts H as H). apply sty_styC_aux_ok_expansion; [auto | idtac].
      apply IHS. constructor. constructor. auto.

    simpl. constructor. inverts H as H; [auto | inverts H].
Qed.

Lemma sty_styC_aux_ok :
  forall S e e',
  Wf.ok e S ->
  WfC.ok (env_union_list e e') (sty_styC_aux e' S).
Proof.
  assert (
    forall v e e',
    env_subset (env_union_list (env_add v e) e')
               (env_union_vars (env_union_list e e')
                 (mkList1 (v :: e') (cons_not_nil Var v e')))
  ) as Hsub.
    intros. rewrite env_union_vars_spec. rewrite env_union_list_spec.
    simpl. rewrite <- env_add_union2. rewrite env_add_union1.
    apply SF.union_subset_4. rewrite env_union_list_spec. (* TODO *)
    apply env_add_m_subset. apply env_subset_union1.
  (* TODO move to Env.v? *)
  assert (
    forall e e',
    env_subset (env_union_list e []) (env_union_list e e')
  ) as Hsub'.
    intros. repeat (rewrite env_union_list_spec). simpl.
    rewrite env_union_neutral. apply env_subset_union1.
  induction S; introv H; try solve
    [ simpl; constructor; inverts H; rewrite <- Hsub'; simpl
    ; apply sty_styC_aux_checked; auto
    ].

    destruct S; try solve
      [ simpl in *; constructor; unfold not; try discriminate; auto
      ; inverts H; rewrite <- Hsub; auto
      ].

      simpl in *. apply sty_styC_aux_ok_expansion; [auto | idtac].
      rewrite env_union_list_spec. rewrite env_add_union1.
      rewrite <- env_union_list_spec. apply IHS. inverts H. assumption.

      inverts H as H. inverts H.
Qed.

Lemma sty_styC_ok :
  forall e S,
  Wf.ok e S ->
  WfC.ok e (sty_styC S).
Proof.
  introv H. rewrite <- env_union_list_neutral with (xs := e).
  apply sty_styC_aux_ok. auto.
Qed.

Lemma sty_styC_wf :
  forall S,
  Wf.wellformed S ->
  WfC.wellformed (sty_styC S).
Proof. apply sty_styC_ok. Qed.

Lemma fold_right_env_add_snoc :
  forall e x xs,
  env_eq (fold_right env_add e (xs ++ [x])) (env_add x (fold_right env_add e xs)).
Proof.
  assert (
    forall xs ys,
    fold_left (fun S X => env_add X S) ys xs = env_union_list xs ys
  ) as env_union_list_inv by auto.

  intros.
  rewrite <- rev_involutive with (l := xs) at 2.
  rewrite <- rev_involutive with (l := xs ++ [x]).
  do 2 (rewrite fold_left_rev_right; rewrite env_union_list_inv;
  rewrite env_union_list_spec). rewrite rev_app_distr. simpl.
  rewrite env_add_union2. reflexivity.
Qed.

Lemma checked_mu_chain :
  forall xs e S,
  R.shape S <> varS ->
  Wf.checked (env_union_vars e xs) S ->
  Wf.checked e (fold_left1 (flip R.mu) xs S).
Proof.
  introv Hsh H. destruct xs as [xs HxsNE]. unfold env_union_vars in *.
  simpl in *. rewrite <- fold_left_rev_right in *. simpl in *.
  gen e S. clear HxsNE.
  induction xs; introv Hsh H; [auto |].
    simpl. rewrite fold_right_app. simpl in *. apply IHxs; [discriminate |].
      inverts H as H; [exfalso; auto |].
        constructor. constructor.
        rewrite <- fold_right_env_add_snoc. auto.
Qed.

Lemma styC_sty_checked :
  forall e S,
  WfC.ok e S ->
  Wf.checked e (styC_sty S).
Proof.
  intros e S. gen e. induction S; introv H; simpl; try solve
    [inverts H; constructor; auto; constructor; auto].

    apply checked_mu_chain.
      destruct S; simpl; try discriminate; inverts H; exfalso; auto.
      inverts H. auto.
Qed.

Lemma ok_mu_chain :
  forall xs e S,
  Wf.ok (env_union_vars e xs) S ->
  Wf.ok e (fold_left1 (flip R.mu) xs S).
Proof.
  introv H. destruct xs as [xs HxsNE]. unfold env_union_vars in *.
  simpl in *. rewrite <- fold_left_rev_right in *. simpl in *.
  gen e S. clear HxsNE.
  induction xs; introv H; [auto |].
    simpl. rewrite fold_right_app. simpl in *. apply IHxs.
      constructor.
      rewrite <- fold_right_env_add_snoc. auto.
Qed.

Lemma styC_sty_ok :
  forall S e,
  C.shape S <> varS ->
  WfC.ok e S ->
  Wf.ok e (styC_sty S).
Proof.
  induction S; introv Hsh H; simpl; try solve
    [inverts H; constructor; apply styC_sty_checked; auto].

    inverts H. apply ok_mu_chain. apply IHS; auto.

    exfalso; auto.
Qed.

Lemma styC_sty_wf :
  forall S,
  WfC.wellformed S ->
  Wf.wellformed (styC_sty S).
Proof.
  introv H. destruct S; try (apply styC_sty_ok; [discriminate | auto]).
    inverts H as H. inverts H.
Qed.
