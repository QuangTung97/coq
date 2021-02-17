Inductive nat : Set :=
  | zero : nat
  | succ : nat -> nat.

Fixpoint add (a b: nat): nat :=
  match a with
  | zero => b
  | succ n => succ (add n b)
  end.

Theorem add_zero: forall a : nat, add a zero = a.
Proof.
  intros a.
  induction a as [ | a Ha].
  + simpl; reflexivity.
  + simpl; rewrite Ha; reflexivity.
Qed. 

Theorem add_succ: forall a b : nat, succ (add a b) = add a (succ b).
Proof.
  intros a b.
  elim a.
  - simpl; trivial.
  - intros n Ha. simpl. rewrite Ha. trivial.
Qed.

Theorem add_sym: forall a b: nat, add a b = add b a.
Proof.
  intros a b.
  induction a.
  + simpl. pose (add_zero b) as H. rewrite H. trivial. 
  + simpl. rewrite IHa. exact (add_succ b a).
Qed.

Theorem add_assoc: forall a b c: nat, add a (add b c) = add (add a b) c.
Proof.
  intros a b.
  elim a.
  - intros c. simpl. trivial.
  - intros n H1 c. simpl. rewrite (H1 c). trivial.
Qed.


