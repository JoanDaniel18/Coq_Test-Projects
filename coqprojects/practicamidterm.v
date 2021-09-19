Variable S : Set.
Variable P : S -> S -> Prop.
Variable Q : S -> S -> Prop.
Hypothesis LHSC : forall x y : S, P x y <-> (forall z : S, Q z x -> Q z y).
Print LHSC.
Hypothesis RHS1C : exists y : S, forall x : S, P x y.
Print RHS1C.
Lemma Formula1 : (((forall x y : S, P x y <-> (forall z : S, Q z x -> Q z y))->((exists y : S, forall x : S, P x y)->(exists y : S, forall x : S, Q x y))) -> (exists t : S, Q t t)).
Proof.
intros.
edestruct H.
intros.
apply LHSC.
apply RHS1C.
exists x.
apply H0.
Qed.
Print Formula1.

Lemma Formula2 : ((forall x y : S, P x y <-> (forall z :S, Q z x -> Q z y))->((exists y:S, forall x:S, Q x y)->(exists y:S, forall x:S, P x y))).
Proof.
intros.
elim H0.
intros x H1.
exists x.
intro x0.
apply H.
intro z.
intros.
apply H1.
Qed.
Print Formula2.
