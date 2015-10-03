Require Import Env List ListAux List1 Morphisms Msg SessionTypes
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
styC_sty inverses of each other.
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
Hint Resolve sty_styC_aux_ok : wf.

Lemma sty_styC_ok :
  forall e S,
  Wf.ok e S ->
  WfC.ok e (sty_styC S).
Proof.
  introv H. rewrite <- env_union_list_neutral with (xs := e). auto with wf.
Qed.
Hint Resolve sty_styC_ok : wf.
