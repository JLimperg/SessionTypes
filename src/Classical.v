Require Import Tac.
Require Export Coq.Logic.Classical.


Definition excluded_middle := classic.


Lemma double_neg :
  forall P,
  ~~ P <-> P.
Proof. intuition tauto. Qed.


Lemma contrapositive :
  forall P Q,
  (~ Q -> ~ P) ->
  P -> Q.
Proof. intros. pose proof (excluded_middle Q) as HQ. inverts1 HQ; tauto. Qed.


Lemma not_iff :
  forall P Q,
  (P <-> Q) <-> (~ P <-> ~ Q).
Proof. intuition tauto. Qed.


Lemma not_and__or :
  forall P Q,
  ~ (P /\ Q) <-> ~ P \/ ~ Q.
Proof. intuition tauto. Qed.


Lemma not_or__and :
  forall P Q,
  ~ (P \/ Q) <-> ~ P /\ ~ Q.
Proof. intuition tauto. Qed.


Lemma imply__or :
  forall (P Q : Prop),
  (P -> Q) <-> (~ P \/ Q).
Proof. intuition tauto. Qed.


Lemma not_imply__and :
  forall (P Q : Prop),
  ~ (P -> Q) <-> (P /\ ~ Q).
Proof. intuition tauto. Qed.


Lemma not_forall__exists_not :
  forall A (P : A -> Prop),
  ~ (forall x, P x) <-> (exists x, ~ P x).
Proof.
  intros. split.
  - apply contrapositive. rewrite double_neg. intros. destruct (classic (P x)).
    * assumption.
    * exfalso. eauto.
  - iauto.
Qed.


Lemma forall_not__exists :
  forall A (P : A -> Prop),
  (forall x, P x) <-> ~ (exists x, ~ P x).
Proof.
  intros. rewrite not_iff. rewrite double_neg. apply not_forall__exists_not.
Qed.