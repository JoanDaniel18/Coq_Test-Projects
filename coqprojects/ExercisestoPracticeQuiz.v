Require Import Classical_Prop.

Lemma double_negation_elimination: 
forall a: Prop, ~~a->a.
intros A DNA.
tauto.
Qed.

Theorem com: forall P Q, 
P\/Q -> Q\/P.
Proof.
intros P Q [HP | HQ].
-right.
apply HP.
-left.
apply HQ.
Qed.

Theorem exer1: forall p,
p->p.
intros P HP.
apply HP.
Qed.

Theorem exer2: forall p q:
Prop, p->q->p.
intros. 
exact H.
Qed.

Theorem exer3: forall p q:
Prop, ~p ->p->q.
intros.
contradiction.
Qed.

Theorem exer4: forall p q r:
Prop, (p->(q/\r))->(p->q).
intros.
apply H in H0 as  H1.
destruct H1.
apply H1.
Qed.

Theorem exer5: forall p q:
Prop, (p/\(q->~p))->(p/\~q).
intros.
destruct H.
split.
apply H.
unfold not.
intro.
apply H0 in H1 as H2.
apply H2.
exact H.
Qed.

Theorem exer6: forall p q r:
Prop, p\/q->p\/r->p\/(q/\r).
intros.
destruct H.
+left.
apply H.
+destruct H0.
-left.
apply H0.
-right.
split.
apply H.
apply H0.
Qed.

Theorem exer7: forall p q:
Prop, ((p->q)->p)->p.
intros.
destruct (classic p).
+apply H0.
+apply H.
intro.
contradiction.
Qed.

Require Import Classical.
Theorem exer8: forall p q:
Prop, ~(p/\q)->~p\/~q.
intros.
(*tauto.*)
destruct(classic (~p\/~q)).
+ apply H0.
+ right.
destruct(classic (~p)).
-intro.
apply H0.
left.
apply H1.
-apply NNPP in H1.
intro.
apply H.
split.
apply H1.
apply H2.
Qed.

Require Import Classical.
Theorem exer9: forall p q r:
Prop, ~r->p\/((p\/r)->q).
intros.
apply NNPP.
intro.
apply H0.
right.
apply NNPP.
intro.
apply H1.
intro.
destruct H2.
+exfalso.
apply H0.
left.
apply H2.
+exfalso.
apply H.
apply H2.
Qed.

Theorem exer11: forall p q:
Prop, (p/\~p)->q.
intros.
destruct H.
exfalso.
apply H0.
apply H.
Qed.

Theorem exer12: forall p q:
Prop, p->p\/q.
intros.
left.
apply H.
Qed.

Theorem exer13: forall p q:
Prop, (p->q)->(~q->~p).
intros.
intro.
apply H0.
apply H.
apply H1.
Qed.

Theorem exer14: forall p q:
Prop, p/\q ->q/\p.
intros.
destruct H.
split.
apply H0.
apply H.
Qed.


Theorem exer15: forall p q:
Prop, p/\q->p->p/\q.
intros.
destruct H.
split.
apply H.
apply H1.
Qed.

Theorem exer22: forall p q r:
Prop, (p->q)->(p->q->r)->(p->r).
intros.
apply H0 in H.
apply H.
apply H1.
apply H1.
Qed.

Theorem exer22_2: forall p q r:
Prop, (p->q)->(p->q->r)->(p->r).
intros.
apply H0.
apply H1.
apply H.
exact H1.
Qed.

Theorem exer29: forall p q r:
Prop, (p->q)->(r->~q)->(p->~r).
intros.
intro.
apply H0.
exact H2.
apply H.
exact H1.
Qed.

Theorem exer36: forall p q:
Prop, (p->q)->p->q.
intros.
apply H.
exact H0.
Qed.

Theorem exer37: forall p q r:
Prop, p\/q->~p\/~r->r->q.
intros.
destruct H.
+destruct H0.
-contradiction.
-contradiction.
+exact H.
Qed.
Require Import Coq.Logic.Classical_Prop.
Lemma HS1 : forall p q r : 
Prop, (q -> r) -> ((p -> q) -> (p -> r)).
intros.
apply H.
apply H0.
exact H1.
(*
apply H0 in H1.
apply H in H1.
exact H1.
*)
Qed.
Lemma HS2 : forall p q r : 
Prop, (p -> q) -> ((q -> r) -> (p -> r)).
Proof.
intros.
apply H0.
apply H.
exact H1.
Qed.

Lemma proj1: forall p q:
Prop, p/\q->q.
Proof.
intros.
destruct H.
exact H0.
Qed.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
intros P Q [HP | HQ].
-right.
apply HP.
-left.
apply HQ.







