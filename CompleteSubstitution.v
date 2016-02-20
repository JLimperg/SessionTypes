Require Import Env SessionTypes SessionTypesInd Substitution SubstitutionFacts
  Tac LibFix Var Wellformed.

Definition Cs cs S :=
  match S with
  | mu X S' => cs (subst X (mu X S') S')
  | _       => S
  end
.

Definition cs := FixFun Cs.

Lemma cs_fix :
  forall S,
  ok_some S ->
  cs S = Cs cs S.
Proof.
  applys (FixFun_fix_partial (lt_Sty_mu_prefix)).
  - auto.
  - unfolds. apply lt_Sty_mu_prefix_wf.
  - unfolds. introv Hok H. destruct x; eauto with subst.
Qed.


Ltac cs_simpl :=
  let ensure_constructor S :=
    match S with
    | unit => idtac
    | send _ _ => idtac
    | recv _ _ => idtac
    | echoice _ _ => idtac
    | ichoice _ _ => idtac
    | mu _ _ => idtac
    | var _ => idtac
    end
  with repl S :=
    rewrite (cs_fix S) in *;
    simpl (Cs cs S) in *
  in
  match goal with
  | |- context [cs ?S] => ensure_constructor S; repl S
  | H : context [cs ?S] |- _ => ensure_constructor S; repl S
  end; [ try cs_simpl | eauto with subst wf .. ]
.
