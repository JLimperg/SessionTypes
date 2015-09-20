Require Import Env Morphisms Msg SessionTypes SessionTypesC Shape Var
  Wellformed WellformedC.

Module R := Sty.
Module C := StyC.

Fixpoint sty_styC_aux (xs : Env) (S : R.Sty) : C.Sty :=
  match S with
  | R.unit => C.unit
  | R.send B S' => C.send B (sty_styC_aux env_empty S')
  | R.recv B S' => C.recv B (sty_styC_aux env_empty S')
  | R.echoice S1 S2 => C.echoice (sty_styC_aux env_empty S1) (sty_styC_aux env_empty S2)
  | R.ichoice S1 S2 => C.ichoice (sty_styC_aux env_empty S1) (sty_styC_aux env_empty S2)
  | R.mu x S' =>
    match S' with
    | R.mu _ _ => sty_styC_aux (env_add x xs) S'
    | _        => C.mu (env_add x xs) (sty_styC_aux env_empty S')
    end
  | R.var X => C.var X
  end
.
Arguments sty_styC_aux xs S : simpl nomatch.

Instance sty_styC_aux_m : Proper (env_eq ==> eq ==> C.eq_syn) sty_styC_aux.
Proof.
  unfold Proper. unfold respectful. intros e e' Hee' x y Hxy. subst.
  rename y into S. generalize dependent e'. generalize dependent e.
  induction S; intros e e' Hee'; simpl in *; try solve
    [ constructor; auto; first [apply IHS | apply IHS1 | apply IHS2]
    ; reflexivity
    ].

    destruct S; simpl in *; try solve
      [constructor; [rewrite Hee'; reflexivity | eauto]].
      eapply IHS. rewrite Hee'. reflexivity.
Qed.

Notation sty_styC := (sty_styC_aux env_empty).

Fixpoint styC_sty (S : C.Sty) : R.Sty :=
  match S with
  | C.unit => R.unit
  | C.send B S' => R.send B (styC_sty S')
  | C.recv B S' => R.recv B (styC_sty S')
  | C.echoice S1 S2 => R.echoice (styC_sty S1) (styC_sty S2)
  | C.ichoice S1 S2 => R.ichoice (styC_sty S1) (styC_sty S2)
  | C.mu xs S' => env_fold (fun X S'' => R.mu X S'') xs (styC_sty S')
  | C.var X => R.var X
  end
.

Section Wf.

(* TODO beautify *)
Lemma sty_styC_aux_ok :
  forall S e e' e'',
  WfC.ok e (sty_styC_aux (env_union e' e'') S) ->
  (R.shape S = muS -> WfC.ok (env_union e e') (sty_styC_aux e''       S)) /\
  (R.shape S <> muS -> WfC.ok e               (sty_styC_aux env_empty S)).
Proof.
  induction S; intros e e' e'' H; simpl in *; split; intro HsS;
    try (discriminate || auto).

    destruct S; simpl in *.
      constructor; unfold not; try discriminate. constructor.

      constructor; unfold not; try discriminate;
      apply IHS; unfold not; auto; try discriminate;
      inversion_clear H; rewrite env_union_assoc; rewrite <- env_add_union2; assumption.

      constructor; unfold not; try discriminate;
      apply IHS; unfold not; auto; try discriminate;
      inversion_clear H; rewrite env_union_assoc; rewrite <- env_add_union2; assumption.

      constructor; unfold not; try discriminate;
      apply IHS; unfold not; auto; try discriminate;
      inversion_clear H; rewrite env_union_assoc; rewrite <- env_add_union2; assumption.

      constructor; unfold not; try discriminate;
      apply IHS; unfold not; auto; try discriminate;
      inversion_clear H; rewrite env_union_assoc; rewrite <- env_add_union2; assumption.

      apply IHS; auto. rewrite <- env_add_union2. assumption.

      inversion_clear H. exfalso; unfold not; eapply H0; eauto.

    unfold not in *; exfalso; apply HsS; trivial.
Qed.

Lemma sty_styC_aux_mu :
  forall S X e e',
  WfC.ok e (sty_styC_aux e' (R.mu X S)) ->
  WfC.ok (env_union e e') (sty_styC (R.mu X S)).
Proof with auto.
  intros. apply sty_styC_aux_ok... rewrite env_union_neutral...
Qed.

(* TODO beautify *)
Lemma sty_styC_ok_checked :
  forall S e,
  WfC.ok e (sty_styC S) ->
  (Wf.checked e S /\
   ((forall X, S <> R.var X) ->
    Wf.ok e S)
  ).
Proof with (auto with wf).
  induction S; intros e H; split; intros.
    constructor. constructor.
    constructor.
    constructor. constructor. inversion_clear H. edestruct IHS; eauto.
    constructor. inversion_clear H. edestruct IHS; eauto.
    constructor. constructor. inversion_clear H. edestruct IHS; eauto.
    constructor. inversion_clear H. edestruct IHS; eauto.
    constructor; constructor; inversion_clear H; [edestruct IHS1 | edestruct IHS2]; eauto.
    constructor; inversion_clear H; [edestruct IHS1 | edestruct IHS2]; eauto.
    constructor; constructor; inversion_clear H; [edestruct IHS1 | edestruct IHS2]; eauto.
    constructor; inversion_clear H; [edestruct IHS1 | edestruct IHS2]; eauto.

    destruct S; simpl in *.
      constructor. constructor. constructor.

      constructor. constructor. inversion_clear H. rewrite <- env_add_union_singleton.
      edestruct IHS; eauto. eapply H3. unfold not. discriminate.

      constructor. constructor. inversion_clear H. rewrite <- env_add_union_singleton.
      edestruct IHS; eauto. eapply H3. unfold not. discriminate.

      constructor; constructor; inversion_clear H; rewrite <- env_add_union_singleton;
      edestruct IHS; eauto; eapply H3; unfold not; discriminate.

      constructor; constructor; inversion_clear H; rewrite <- env_add_union_singleton;
      edestruct IHS; eauto; eapply H3; unfold not; discriminate.

      destruct IHS with (e := env_add v e); eauto.
        rewrite <- env_add_union_singleton. apply sty_styC_aux_mu. assumption.
      constructor. constructor. eapply H1. unfold not; discriminate.

      constructor. constructor. inversion_clear H. edestruct IHS. eauto.
      rewrite <- env_add_union_singleton. eapply H3. unfold not in *; intros.
      eapply H0. eexists.

    destruct S; simpl in *.
      constructor. constructor.

      constructor. inversion_clear H. edestruct IHS; eauto.
      rewrite <- env_add_union_singleton. eapply H4. unfold not; discriminate.

      constructor. inversion_clear H. edestruct IHS; eauto.
      rewrite <- env_add_union_singleton. eapply H4. unfold not; discriminate.

      constructor; inversion_clear H; edestruct IHS; eauto;
      rewrite <- env_add_union_singleton; eapply H4; unfold not; discriminate.

      constructor; inversion_clear H; edestruct IHS; eauto;
      rewrite <- env_add_union_singleton; eapply H4; unfold not; discriminate.

      constructor. destruct IHS with (e := env_add v e).
        rewrite <- env_add_union_singleton. apply sty_styC_aux_mu. assumption.
      eapply H2. unfold not; discriminate.

      inversion_clear H. unfold not in *. exfalso. eapply H1. eexists.

    inversion_clear H. constructor...

    unfold not in *; exfalso; eauto.
Qed.

Lemma sty_styC_wf :
  forall S,
  WfC.wellformed (sty_styC S) ->
  Wf.wellformed S.
Proof.
  intros. apply sty_styC_ok_checked; auto.
    unfold not; intros; destruct S; inversion_clear H; try discriminate.
    contradict H1. apply env_mem_empty.
Qed.

End Wf.
