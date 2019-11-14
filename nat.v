Require Import logic.
Require Import axiom.
Require Import basic.
Require Import relation.

Definition nat (n: set) := forall B, inductive B -> n ∈ B.
Theorem nat_exists: exists A, forall n, nat n <-> n ∈ A.
Proof.
  destruct ax_infinity as [X P1].
  exists (subset_ctor (fun n => forall B, inductive B -> n ∈ B) X). 
  intros n.
  split.
  + intros P2.
    apply subset_intro.
    - apply (P2 X P1).
    - intros B P3.
      apply (P2 B P3).
  + apply subset_elim.
Qed.

Definition ω := extract_set nat_exists.
Notation "0ₙ" := ∅ (at level 60, no associativity).
Notation "1ₙ" := (S(∅)).
Notation "2ₙ" := (S(S(∅))).
Notation "3ₙ" := (S(S(S(∅)))).
Notation "4ₙ" := (S(S(S(S(∅))))).

Lemma nat_intro: forall x, nat x -> x ∈ ω.
Proof.
  intros x P1.
  destruct (extract_set_property nat_exists x) as [P2 _].
  apply (P2 P1).
Qed.

Lemma nat_elim: forall x, x ∈ ω-> nat x.
Proof.
  intros x P1.
  destruct (extract_set_property nat_exists x) as [_ P2].
  apply (P2 P1).
Qed.

Lemma nat_inductive: inductive ω.
Proof.
  split.
  + apply nat_intro.
    intros A [P1 _].
    apply P1.
  + intros x P1.
    apply nat_intro.
    intros A P2.
    pose (nat_elim x P1 A P2) as P3.
    destruct P2 as [P4 P5].
    apply (P5 x P3).
Qed.

Lemma nat_is_subset: forall A, inductive A -> ω ⊆ A.
Proof.
  intros A P1 x P2.
  apply (nat_elim x P2 A P1).
Qed.

Lemma empty_in_nat: ∅ ∈ ω.
Proof.
  apply nat_intro.
  intros B P1.
  destruct P1 as [P2 _].
  apply P2.
Qed.

Lemma successor_in_nat: forall k, k ∈ ω -> S(k) ∈ ω.
Proof.
  intros k P1.
  apply nat_intro.
  intros B P2.
  pose ((nat_elim _ P1) B P2) as P3.
  destruct P2 as [P2 P4].
  apply (P4 _ P3).
Qed.
  
Lemma induction_principle: forall T, T ⊆ ω -> inductive T -> T = ω.
Proof.
  intros T P1 P2.
  apply subset_asym.
  apply (conj P1 (nat_is_subset T P2)).
Qed.

Lemma induction_principle_: forall P: set -> Prop, P ∅ ->
  (forall k, P k -> P (S(k))) -> (forall n, n ∈ ω -> P n).
Proof.
  intros P P1 P2 n P3.
  assert ((subset_ctor P ω) ⊆ ω) as P4.
  { intros x.
    intros P5.
    destruct (subset_elim _ _ _ P5) as [P6 _].
    apply P6. }
  assert (inductive (subset_ctor P ω)) as P5.
  { split.
    + apply (subset_intro _ _ _ (empty_in_nat) P1).
    + intros x P5.
      destruct (subset_elim _ _ _ P5) as [P6 P7].
      apply (subset_intro _ _ _ (successor_in_nat _ P6) (P2 _ P7)). }
  rewrite <- (induction_principle _ P4 P5) in P3.
  destruct (subset_elim _ _ _ P3) as [_ P6].
  apply P6.
Qed.
    

