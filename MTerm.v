(* Each ? must be replaced by 1 tactic, hypotheis or reserved character *)
Variable term:Type.
Variable P : term -> term -> Prop.
Hypothesis Hqd : forall a b : term, P a b <-> (exists c : term, (P a c \/ P c a) /\ (P c b \/ P b c)).
Hypothesis Hrd : forall a : term, P a a.
Variable d0 : term.
(*ex1*)
Lemma QAL1 : forall a b : term, P a b <-> P b a.
Proof.
intros.
split.
intros.
apply Hqd.
exists a.
split.
- right. apply H.
- left. apply Hrd.
- intros.
apply Hqd.
exists a.
split.
left. apply Hrd.
right. apply H.
Qed.
Print QAL1.
(*ex2*)
Theorem QAL2: forall a b c : term, exists d : term, (P a d /\ P b d /\ P c d) -> (P a b /\ P b c /\ P a c).
Proof.
intros.
exists d0.
intros.
(* In the following line of code each ? must be replaced by 1 character or one hypothesis *)
destruct H as [ d [ l e ] ].
split.
- apply Hqd. exists d0. split. left. exact d. right. exact l.   
- split. apply Hqd. exists d0. split. left. exact l. right. exact e.
apply Hqd.
exists d0.
split.
left.
apply d.
right.
apply e.
Qed.
Print QAL2.

