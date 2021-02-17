Variable U : Set.
Variable In : U -> U -> Prop.

Variable extension_axiom : forall A B: U, (forall x: U, In x A -> In x B) -> A = B.

Theorem extension_revert : forall A B: U, A = B -> (forall x: U, In x A -> In x B).
Proof.
  intros A B H x H1.
  rewrite H in H1.
  trivial.
Qed.

Definition is_empty (A: U) := forall x: U, ~(In x A).

Variable empty_axiom : exists A: U, is_empty(A).

Theorem empty_equal: forall A B: U, is_empty(A) -> is_empty(B) -> A = B.
Proof.
  intros A B HA HB.
  apply extension_axiom.
  intros x H.
  unfold is_empty in HA.
  pose (H0 := HA x).
  contradiction.
Qed.

Theorem exist_unique_empty : exists! A: U, is_empty(A).
Proof.
  induction empty_axiom.
  exists x.
  unfold unique.
  split.
  - trivial.
  - intros b.
    apply empty_equal.
    trivial.
Qed.

Definition is_pair_set (C A B: U) := forall x: U, In x C <-> x = A \/ x = B.

Variable pairing_axiom : forall A B: U, exists C: U, is_pair_set C  A  B.

Theorem pair_set_unique : forall A B C D: U, is_pair_set C A B -> is_pair_set D A B -> C = D.
Proof.
  intros A B C D.
  intros H1 H2.
  apply extension_axiom.
  intros x H.
  unfold is_pair_set in H1, H2.
  induction (H1 x) as [H3 _].
  induction (H2 x) as [_ H4].
  apply H4.
  apply H3.
  trivial.
Qed.

Theorem or_sym : forall A B : Prop, A \/ B -> B \/ A.
Proof.
  intros A B H.
  elim H.
  - intros H1. right. trivial.
  - intros H1. left. trivial.
Qed.

Theorem pair_set_sym : forall A B C: U, is_pair_set C A B -> is_pair_set C B A.
Proof.
  intros A B C H.
  unfold is_pair_set.
  unfold is_pair_set in H.
  intros x.
  induction (H x) as [H1 H2].
  split.
  - intros H3.
    apply or_sym.
    apply H1.
    trivial.
  - intros H3.
    apply H2.
    apply or_sym.
    trivial.
Qed.

Theorem or_duplicate : forall A: Prop, A \/ A -> A.
Proof.
  intros A H.
  destruct H.
  trivial. trivial.
Qed.

Theorem simple_equal : forall a : U, a = a.
Proof.
  intros a. reflexivity.
Qed.

Theorem pair_set_single_equal : forall a b c T: U, is_pair_set T a a -> is_pair_set T b c -> a = b.
Proof.
  intros a b c T H1 H2.
  unfold is_pair_set in H1, H2.
  induction (H1 b) as [H3 _].
  induction (H2 b) as [_ H4].
  pose (H5 := simple_equal b).
  pose (H6 
  .
Qed.

Definition is_pair (t a b: U) := exists u v: U, is_pair_set u a a /\ is_pair_set v a b /\ is_pair_set t u v.

Theorem pair_same : forall a b x y t: U, is_pair t a b -> is_pair t x y -> (a = b \/ x = y) -> a = x /\ b = y.
Proof.
  intros a b x y t.
  intros H1 H2 H.
  unfold is_pair in H1, H2.

  induction H1 as [u1 H1].
  induction H1 as [v1 H1].
  induction H2 as [u2 H2].
  induction H2 as [v2 H2].

  destruct H.
  



