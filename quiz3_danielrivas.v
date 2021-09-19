(*Daniel Rivas*)
Variables A : Set.
Variables P Q : A -> A -> Prop.
(*first validation*)
Lemma proof1: (forall y x:A, P x y) -> (forall z x y:A, Q z x ->
Q z y) -> (forall x:A, P x x).
Proof.
intros.
apply H.
Qed.
(*second validation*)
Lemma proof2: (forall z x y:A, Q z x -> Q z y) -> 
(forall y x:A, P x y) ->  (forall x:A, P x x).
Proof.
intros.
apply H0.
Qed.


