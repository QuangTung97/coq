Variable excluded_middle : forall P: Prop, P \/ ~P.

Variable U : Set.
Variable In : U -> U -> Prop.

Variable extension_axiom : forall A B: U, (forall x: U, In x A <-> In x B) -> A = B.

Definition is_empty (A: U) := forall x: U, ~(In x A).

Definition is_subset (A B: U) := forall x: U, In x A -> In x B.

Variable empty_axiom : exists A: U, is_empty(A).

Definition is_pair_set (C A B: U) := forall x: U, In x C <-> x = A \/ x = B.

Variable pairing_axiom : forall A B: U, exists C: U, is_pair_set C A B.

Variable subset_axiom : forall P: U -> Prop, forall A: U, exists S: U, forall x: U, In x S <-> In x A /\ P x.

Variable union_axiom : forall F: U, exists A: U, forall x, In x A <-> exists C, In x C /\ In C F.

Variable power_set_axiom : forall A: U, exists P: U, forall x, In x P <-> is_subset x A.

Definition is_intersect (S A B: U) := forall x: U, In x S <-> In x A /\ In x B.

Definition is_diff (S A B: U) := forall x: U, In x S <-> In x A /\ ~In x B.

Definition is_union_set (S A: U) := forall x, In x S <-> exists C, In x C /\ In C A.

Definition non_empty (A: U) := exists x, In x A.

Definition is_intersect_set (I: U) (A: U) (P: non_empty A) := forall x, In x I <-> forall C, In C I -> In x C.

Definition is_power_set (P A: U) := forall x, In x P <-> is_subset x A.

Theorem extension_revert : forall A B: U, A = B -> (forall x: U, In x A -> In x B).
Proof.
  intros A B H x H1.
  rewrite H in H1.
  trivial.
Qed.

Theorem empty_equal: forall A B: U, is_empty A -> is_empty B -> A = B.
Proof.
  intros A B HA HB.
  apply extension_axiom.
  intros x.
  split.
  unfold is_empty in HA, HB.
  - intros H. pose (HA' := HA x). contradiction.
  - intros H. pose (HB' := HB x). contradiction.
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


Theorem double_negation : forall P: Prop, ~~P -> P.
Proof.
  intros P H.
  destruct (excluded_middle P). auto.
  pose (H1 := H H0).
  contradiction.
Qed.

Theorem not_exists_and_forall: forall P: U -> Prop, ~(exists x, P x) <-> forall x, ~ P x.
Proof.
  intros P.
  split.
  - intros H x H1.
    apply H.
    exists x. auto.
  - intros H H1.
    induction H1 as [x H1].
    apply (H x). auto.
Qed.

Theorem not_forall_and_exists: forall P: U -> Prop, (exists x, ~P x) <-> ~(forall x, P x).
Proof.
  intros P.
  split.
  - intros H.
    induction H as [x H].
    intros H1.
    apply H.
    apply H1.
  - intros H.
    pose (H1 := excluded_middle (exists x, ~ P x)).
    destruct H1. auto.
    assert (forall x, P x) as H1.
    + intros x.
      apply (double_negation).
      intros H1.
      apply H0.
      exists x.
      auto.
    + contradiction.
Qed.

Theorem non_empty_not_is_empty : forall A: U, non_empty A <-> ~is_empty A.
Proof.
  intros A.
  unfold is_empty.
  unfold non_empty.
  split.
  - intros H1 H2.
    induction H1 as [x H1].
    apply (H2 x). auto.
  - intros H1.
    pose (H2 := not_forall_and_exists (fun x => ~In x A)).
    simpl in H2.
    destruct H2 as [_ H3].
    pose (H4 := H3 H1).
    induction H4 as [x H4].
    exists x.
    apply double_negation. auto.
Qed.

Parameter intersect : U -> U -> U.
Variable intersect_prop : forall A B: U, is_intersect (intersect A B) A B.

Parameter diff : U -> U -> U.
Variable diff_prop : forall A B: U, is_diff (diff A B) A B.

Parameter pair_set : U -> U -> U.
Variable pair_set_prop : forall A B: U, is_pair_set (pair_set A B) A B.

Parameter union_set : U -> U.
Variable union_set_prop : forall A: U, is_union_set(union_set A) A.

Parameter intersect_set : forall A: U, non_empty A -> U.
Variable intersect_set_prop : forall A: U, forall P: non_empty A, is_intersect_set (intersect_set A P) A P.

Parameter power_set : U -> U.
Variable power_set_prop : forall A: U, is_power_set (power_set A) A.

Definition pair (A B: U) := pair_set (pair_set A A) (pair_set A B).

Theorem intersect_sym: forall A B: U, intersect A B = intersect B A.
Proof.
  intros A B.
  pose (H1 := intersect_prop A B).
  pose (H2 := intersect_prop B A).
  unfold is_intersect in H1, H2.
  apply extension_axiom.
  intros x.
  split.
  - intros H.
    induction (H1 x) as [H3 _].
    induction (H2 x) as [_ H4].
    apply H4.
    assert (In x A /\ In x B) as H5. apply H3. auto.
    destruct H5. auto.
  - intros H.
    induction (H1 x) as [_ H3].
    induction (H2 x) as [H4 _].
    apply H3.
    assert (In x B /\ In x A) as H5. apply H4. auto.
    destruct H5. auto.
Qed.

Theorem theorem_2_1_1: forall A B C: U,
  intersect A (diff B C) = diff (intersect A B) C.
Proof.
  intros A B C.
  pose (H1 := diff_prop B C).
  pose (H2 := intersect_prop A (diff B C)).
  pose (H3 := intersect_prop A B).
  pose (H4 := diff_prop (intersect A B) C).

  unfold is_diff in H1, H4.
  unfold is_intersect in H2, H3.
  apply extension_axiom.
  intros x.
  split.
  - intros H.
    induction (H2 x) as [H5 _].
    pose (H6 := H5 H).
    destruct H6 as [H6 H7].
    induction (H1 x) as [H8 _].
    pose (H9 := H8 H7).
    destruct H9 as [H9 H10].
    induction (H4 x) as [_ H11].
    apply H11.
    split.
    + induction (H3 x) as [_ H12].
      apply H12.
      split; auto.
    + trivial.
  - intros H.
    induction (H4 x) as [H5 _].
    pose (H6 := H5 H).
    destruct H6 as [H6 H7].
    induction (H3 x) as [H8 _].
    pose (H9 := H8 H6).
    destruct H9 as [H9 H10].
    induction (H2 x) as [_ H11].
    apply H11.
    split. trivial.
    induction (H1 x) as [_ H12].
    apply H12.
    split. auto. auto.
Qed.

Theorem theorem_2_1_2: ~exists S: U, forall x: U, In x S.
Proof.
  intros H.
  induction H as [A H].
  pose (H1 := subset_axiom (fun (x: U) => ~In x x) A).
  induction H1 as [B H1].
  induction (H1 B) as [H2 H3].
  pose (HT := H B).
  pose (HM := excluded_middle (In B B)).
  destruct HM.
  - pose (H4 := H2 H0).
    destruct H4 as [H4 H5].
    auto.
  - assert (In B B) as H4. apply H3. auto. auto.
Qed.

Theorem theorem_2_1_3: forall P: U -> Prop, (exists A: U, forall x: U, P x -> In x A) ->
  exists ! D: U, forall x: U, In x D <-> P x.
Proof.
  intros P H.
  induction H as [A H].
  pose (H1 := subset_axiom P A).
  induction H1 as [D H1].
  exists D.
  unfold unique.
  split.
  - intros x.
    split.
    + intros H2.
      induction (H1 x) as [H3 _].
      destruct (H3 H2). auto.
    + intros H2.
      assert (In x A) as H3. apply H. auto.
      assert (In x A /\ P x) as H4. auto.
      destruct (H1 x) as [_ H5].
      apply H5. auto.
  - intros D1 H2.
    apply extension_axiom.
    intros x.
    split.
    + intros H3.
      destruct (H2 x) as [_ H4].
      apply H4.
      assert (In x A /\ P x) as H5. apply H1. auto.
      destruct H5. auto.
    + intros H3.
      destruct (H1 x) as [_ H4].
      apply H4.
      assert (P x) as H5.
      * destruct (H2 x) as [H6 _]. auto.
      * assert (In x A). auto.
      auto.
Qed.

Theorem union_set_unique: forall A, exists ! S: U, is_union_set S A.
Proof.
  intros A.
  induction (union_axiom A) as [S H].
  exists S.
  unfold unique.
  split. auto.
  intros S1.
  intros H1.
  unfold is_union_set in H1.
  apply extension_axiom.
  intros x.
  split.
  - intros H2.
    destruct (H x) as [H3 _].
    destruct (H1 x) as [_ H4].
    apply H4.
    apply H3. auto.
  - intros H2.
    destruct (H x) as [_ H3].
    destruct (H1 x) as [H4 _].
    apply H3. apply H4. auto.
Qed.

Theorem subset_axiom_unique: forall P: U -> Prop, forall A: U,
  exists ! S: U, forall x: U, In x S <-> In x A /\ P x.
Proof.
  intros P A.
  induction (subset_axiom P A) as [S H].
  exists S.
  unfold unique.
  split. auto.
  intros S' H1.
  apply extension_axiom.
  intros x.
  pose (H2 := H x).
  pose (H3 := H1 x).
  destruct H2.
  destruct H3.
  split. auto. auto.
Qed.

Theorem theorem_2_1_7: forall F, non_empty F -> exists ! I, forall x, In x I <-> forall C, In C F -> In x C.
Proof.
  intros F H.
  unfold non_empty in H.
  induction H as [A H].
  pose (H1 := subset_axiom_unique (fun x => forall C : U, In C F -> In x C) A).
  simpl in H1.
  induction H1 as [I H1].
  unfold unique in H1.
  destruct H1 as [H1 He].
  exists I.
  unfold unique.
  split.
  - intros x.
    split.
    + intros H2.
      destruct (H1 x) as [H3 _].
      pose (H4 := H3 H2).
      destruct H4. auto.
    + intros H2.
      destruct (H1 x) as [_ H3].
      apply H3.
      split. auto. auto.
  - intros I' H2.
    apply He. intros x.
    split.
    + intros H3.
      destruct (H2 x) as [H4 _]. pose (H5 := H4 H3 A H).
      auto.
    + intros H3.
      destruct (H2 x) as [_ H4].
      apply H4.
      destruct H3. auto.
Qed.

Theorem power_set_axiom_unique: forall A: U, exists ! P: U, forall x, In x P <-> is_subset x A.
Proof.
  intros A.
  induction (power_set_axiom A) as [P H].
  exists P.
  unfold unique.
  split. auto.
  intros P' H1.
  apply extension_axiom.
  intros x.
  destruct (H x).
  destruct (H1 x).
  split. auto. auto.
Qed.

Theorem equal_by_subset: forall A B: U, is_subset A B -> is_subset B A -> A = B.
Proof.
  intros A B H1 H2.
  unfold is_subset in H1, H2.
  apply extension_axiom.
  intros x.
  split. auto. auto.
Qed.

Theorem intersect_in: forall A B: U, forall x, In x (intersect A B) -> In x A /\ In x B.
Proof.
  intros A B x H.
  pose (H1 := intersect_prop A B x).
  destruct H1. auto.
Qed.

Theorem intersect_subset: forall A B X: U, is_subset X (intersect A B) <-> is_subset X A /\ is_subset X B.
Proof.
  intros A B X.
  split.
  - intros H.
    split.
    + intros x H1.
      pose (H2 := H x H1).
      destruct (intersect_in A B x H2). auto.
    + intros x H1.
      pose (H2 := H x H1).
      destruct (intersect_in A B x H2). auto.
  - intros H e He.
    destruct H as [H1 H2].
    pose (H3 := intersect_prop A B e).
    destruct H3 as [_ H3].
    apply H3.
    split.
    + apply H1. auto.
    + apply H2. auto.
Qed.

Theorem subset_in_power_set: forall A P: U, is_subset A P <-> In A (power_set P).
Proof.
  intros A P.
  split.
  - intros H.
    pose (H1 := power_set_prop P A).
    destruct H1. auto.
  - intros H.
    pose (H1 := power_set_prop P A).
    destruct H1. auto.
Qed.

Theorem intersect_intro: forall A B x: U, In x A -> In x B -> In x (intersect A B).
Proof.
  intros A B x H1 H2.
  pose (H3 := intersect_prop A B x).
  destruct H3 as [_ H4].
  apply H4. auto.
Qed.

Theorem theorem_2_1_11: forall A B: U, power_set (intersect A B) = intersect (power_set A) (power_set B).
Proof.
  intros A B.
  apply extension_axiom.
  intros x. split.
  - intros H.
    assert (is_subset x (intersect A B)) as H1.
      pose (H1 := power_set_prop (intersect A B) x).
      destruct H1. auto.

    pose (H2 := intersect_prop A B).
    pose (H3' := intersect_subset A B x).
    destruct H3' as [H3' _].
    destruct (H3' H1) as [H3 H4].
    pose (H5 := subset_in_power_set x A).
    destruct H5 as [H5 _].
    pose (H6 := subset_in_power_set x B).
    destruct H6 as [H6 _].
    apply intersect_intro. auto. auto.
  - intros H.
    pose (H1 := intersect_in (power_set A) (power_set B) x H).
    destruct H1 as [H1 H2].
    pose (H3 := subset_in_power_set x A).
    destruct H3 as [_ H3].
    pose (H4 := subset_in_power_set x B).
    destruct H4 as [_ H4].
    assert (is_subset x (intersect A B)) as H5.
    + pose (H5 := intersect_subset A B x).
      destruct H5 as [_ H5]. apply H5.
      auto.
    + pose (H6 := subset_in_power_set x (intersect A B)).
      destruct H6 as [H6 _].
      apply H6.
      auto.
Qed.

Theorem diff_subset: forall A B: U, is_subset (diff A B) A.
Proof.
  intros A B.
  pose (H := diff_prop A B).
  intros x.
  destruct (H x) as [H1 _].
  intros H2.
  destruct (H1 H2). auto.
Qed.

Theorem theorem_2_2_1: forall A F: U, exists! D: U, forall Y, In Y D <-> exists C, In C F /\ Y = diff A C.
Proof.
  intros A F.
  pose (H1 := theorem_2_1_3 (fun Y => exists C, In C F /\ Y = diff A C)). simpl in H1.
  apply H1.
  exists (power_set A).
  intros x H2.
  induction H2 as [C H2].
  destruct H2 as [_ H3].
  apply subset_in_power_set.
  rewrite H3.
  apply diff_subset.
Qed.

Theorem pairing_axiom_unique: forall A B: U, exists ! C: U, is_pair_set C A B.
Proof.
  intros A B.
  induction (pairing_axiom A B) as [S H].
  exists S.
  unfold unique.
  split.
  - auto.
  - intros S' H1.
    apply extension_axiom.
    intros x.
    split.
    + intros H2.
      pose (H3 := H x).
      destruct H3 as [H3 _].
      pose (H4 := H1 x).
      destruct H4 as [_ H4].
      auto.
    + intros H2.
      pose (H3 := H x).
      destruct H3 as [_ H3].
      pose (H4 := H1 x).
      destruct H4 as [H4 _].
      auto.
Qed.

Theorem lemma_3_1_2_double: forall x a b: U, pair_set x x = pair_set a b -> x = a /\ x = b.
Proof.
  intros x a b H1.
  pose (H2 := pair_set_prop x x).
  pose (H3 := pair_set_prop a b).
  unfold is_pair_set in H2, H3.
  rewrite H1 in H2.
  pose (H4 := H2 a).
  pose (H5 := H2 b).

  assert (In a (pair_set a b)) as H6.
  destruct (H3 a) as [_ H6]. auto.

  assert (In b (pair_set a b)) as H7.
  destruct (H3 b) as [_ H7]. auto.

  destruct H4 as [H4 _].
  destruct H5 as [H5 _].

  split.
  - symmetry. destruct (H4 H6). auto. auto.
  - symmetry. destruct (H5 H7). auto. auto.
Qed.

Theorem lemma_3_1_2: forall u v x y: U, pair x y = pair u v -> x = y -> (x = u /\ y = v).
Proof.
  intros u v x y H1 H2.
  symmetry in H2.
  rewrite H2 in H1.
  unfold pair in H1.
  pose (t := pair_set x x).
  pose (a := pair_set u u).
  pose (b := pair_set u v).

  pose (H3 := lemma_3_1_2_double t a b H1).
  destruct H3 as [H3 H4].

  pose (H5 := lemma_3_1_2_double x u u H3).
  destruct H5 as [H5 _].
  pose (H6 := lemma_3_1_2_double x u v H4).
  destruct H6 as [_ H6].
  rewrite H2.
  auto.
Qed.

Theorem pair_set_sym: forall a b: U, pair_set a b = pair_set b a.
Proof.
  intros a b.
  pose (H1 := pair_set_prop a b).
  pose (H2 := pair_set_prop b a).
  apply extension_axiom.
  intros x.
  split.
  - intros H.
    apply (H2 x).
    pose (H3 := H1 x).
    destruct H3 as [H3 _].
    pose (H4 := H3 H).
    case H4. auto. auto.
  - intros H.
    apply (H1 x).
    pose (H3 := H2 x).
    destruct H3 as [H3 _].
    pose (H4 := H3 H).
    case H4. auto. auto.
Qed.

Theorem pair_set_equal: forall a b x y: U, pair_set a b = pair_set x y -> a = x \/ a = y.
Proof.
  intros a b x y H1.
  pose (H2 := pair_set_prop x y a).
  apply H2.
  symmetry in H1. rewrite H1.
  pose (H3 := pair_set_prop a b a).
  apply H3.
  left. auto.
Qed.

Theorem pair_set_equal2: forall a b x y: U, pair_set a b = pair_set x y -> b = x \/ b = y.
Proof.
  intros a b x y H1.
  pose (H2 := pair_set_prop x y b).
  apply H2.
  symmetry in H1. rewrite H1.
  pose (H3 := pair_set_prop a b b).
  apply H3.
  right. auto. 
Qed.

Theorem theorem_3_1_3_diff: forall x a b: U, pair_set x x = pair_set a b -> a <> b -> False.
Proof.
  intros x a b H1 H2.
  pose (H3 := lemma_3_1_2_double x a b H1).
  destruct H3 as [H3 H4].
  rewrite H3 in H4.
  auto.
Qed.

Theorem theorem_3_1_3: forall x y u v: U, pair x y = pair u v -> x = u /\ y = v.
Proof.
  intros x y u v.
  pose (H1 := excluded_middle (x = y)).
  destruct H1.
  intros H1.
  apply lemma_3_1_2. auto. auto.
  intros H1.
  pose (H2 := excluded_middle (u = v)).
  destruct H2.
  assert (u = x /\ v = y) as H3.
  apply lemma_3_1_2. auto. auto.
  destruct H3 as [H3 H4].
  auto.

  unfold pair in H1.
  pose (H1' := H1).
  pose (H2 := pair_set_equal (pair_set x x) (pair_set x y) (pair_set u u) (pair_set u v) H1).
  assert (x = u) as Hx.
    destruct H2.
    pose (H3 := lemma_3_1_2_double x u u H2).
    destruct H3. auto.
    pose (H3 := theorem_3_1_3_diff x u v H2 H0).
    contradiction.

  split. auto.
  symmetry in Hx.
  rewrite Hx in H1'.
  pose (H3 := pair_set_equal2 (pair_set x x) (pair_set x y) (pair_set x x) (pair_set x v) H1').
  case H3.
  - intros H4.
    symmetry in H4.
    assert False.
    apply (theorem_3_1_3_diff x x y). auto. auto.
    contradiction.
  - intros H4.
    assert (y = x \/ y = v).
    apply (pair_set_equal2 x y x v). auto.
    case H5.
    + intros H6. symmetry in H6. contradiction.
    + auto.
Qed.


















