Require Import Coq.Logic.Classical_Prop.
About classic.
(*Axiom LEM : forall P:Prop, P \/ ~ P.*)

Theorem NDRid1 : forall (p q : Prop), q -> (p \/ q).
Proof. 
intros.
right. exact H. Show Proof.
Qed.

Theorem NDRid2 : forall (p q : Prop), p -> (p \/ q).
Proof. 
intros.
left. exact H.
Qed.


Theorem Conversion: forall (p q: Prop),(p -> q) -> (~ p \/ q).
Proof.
  intros p q.
  intros p_implies_q.
  destruct (classic p) as [p_true | p_not_true].
  - apply p_implies_q in p_true as q_true. apply NDRid1. exact q_true. Show Proof. (* prove ~p \/ q using p *)
  - apply NDRid2. exact p_not_true. Show Proof. (* prove ~p \/ q using ~p *)
Qed.
(*demostracion demorgan*)
Lemma morgan : forall P Q : Prop, ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  unfold not.
  intros P Q PorQ_false.
    split.
    intros P_holds.
    apply PorQ_false.
    left.
      exact P_holds.
      intros Q_holds.
      apply PorQ_false.
    right.
      exact Q_holds.
Qed.

(*Double negation*)
Theorem double_neg : forall (P : Prop),
  P -> ~~P.
Proof.
  unfold not.
  intros.
  destruct (H0 H).
Qed.

(*distributes_law*)
Theorem distributes_law: forall (P Q R : Prop),
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  split.
  - intros [HP | [HQ HR]].
    + split.
      * left. apply HP.
      * left. apply HP.
    + split.
      * right. apply HQ.
      * right. apply HR.
  - intros [[HP | HQ] [HP' | HR]].
    + left. apply HP.
    + left. apply HP.
    + left. apply HP'.
    + right.
      split.
      * apply HQ.
      * apply HR.
Qed.