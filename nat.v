Require Import logic.
Require Import axiom.
Require Import basic.
Require Import relation.

Lemma succesor_elim: forall A x, x ∈ S(A) -> x = A \/ x ∈ A.
Proof.
  intros A x P1.
  destruct (in_union2_in _ _ _ P1) as [P2|P2].
  + right.
    apply P2.
  + left.
    symmetry.
    apply (in_singleton_equal _ _ P2).
Qed.

Lemma successor_intro_1: forall A, A ∈ S(A).
Proof.
  intros A.
  apply in_in_union2_2.
  apply in_singleton.
Qed.

Lemma successor_intro_2: forall A x, x ∈ A -> x ∈ S(A).
Proof.
  intros A.
  apply in_in_union2_1.
Qed.

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
    
Lemma nat_is_successor: forall x, x ∈ ω -> x <> ∅ -> exists y, x = S(y).
Proof.
  intros x P1 P2.
  pose (P := fun x => x = ∅ \/ exists y, x = S(y)).
  assert (P ∅) as P3.
  { left.
    reflexivity. }
  assert (forall k, P k -> P (S(k))) as P4.
  { intros k [P4|P4].
    + right.
      exists ∅.
      rewrite P4.
      reflexivity.
    + right.
      exists k.
      reflexivity. }
  destruct (induction_principle_ _ P3 P4 x P1) as [P5|P5].
  + contradiction.
  + apply P5.
Qed.

(* Skip Peano's System *)
Definition σ := subset_ctor (fun x => exists y, x = ⟨y, S(y)⟩) (cp ω ω).

(* Transition *)
Definition trans (A: set) := forall x a, x ∈ a /\ a ∈ A -> x ∈ A.

Lemma trans_elim_1: forall A, trans A -> ∪(A) ⊆ A.
Proof.
  intros A P1 x P2.
  destruct (in_union_in A x P2) as [a P3].
  apply (P1 _ _ (and_sym _ _ P3)).
Qed.

Lemma trans_elim_2: forall A, trans A -> forall a, a ∈ A -> a ⊆ A.
Proof. 
  intros A P1 a P2 x P3.
  apply (P1 _ _ (conj P3 P2)).
Qed.

Lemma trans_elim_3: forall A, trans A -> A ⊆ 𝒫(A).
Proof.
  intros A P1 x P2.
  apply subset_in_power.
  apply (trans_elim_2 _ P1 _ P2).
Qed.

Lemma trans_intro_1: forall A, ∪(A) ⊆ A -> trans A.
Proof.
  intros A P1 x a P2.
  apply P1.
  apply (in_in_union).
  exists a.
  apply (and_sym _ _ P2).
Qed.

Lemma trans_intro_2: forall A, (forall a, a ∈ A -> a ⊆ A) -> trans A.
Proof.
  intros A P1 x a [P2 P3].
  apply (P1 _ P3 x P2).
Qed.

Lemma trans_intro_3: forall A, A ⊆ 𝒫(A) -> trans A.
Proof.
  intros A P1 x a [P2 P3].
  apply (in_power_subset _ _ (P1 _ P3) x P2).
Qed.

Lemma union_trans_successor: forall A, trans A -> ∪(S(A)) = A.
Proof.
  intros A P1.
  apply ax_exten.
  intros x.
  split.
  + intros P2.
    destruct (in_union_in _ _ P2) as [y [P3 P4]].
    destruct (succesor_elim _ _ P3) as [P5|P5].
    - rewrite <- P5.
      apply P4.
    - apply (P1 _ _ (conj P4 P5)).
  + intros P2.
    apply (in_in_union).
    exists A.
    split.
    - apply successor_intro_1.
    - apply P2.
Qed.

Lemma nat_is_trans: forall A, nat A -> trans A.
Proof.
  intros A P1.
  assert (trans ∅) as P2.
  { intros x a [_ P2].
    absurd (a ∈ ∅).
    + apply not_in_empty.
    + apply P2. }
  assert (forall k, trans k -> trans (S(k))) as P3.
  { intros k P3.
    apply trans_intro_1.
    rewrite (union_trans_successor _ P3).
    intros x P4.
    apply (successor_intro_2 _ _ P4). }
  pose (nat_intro _ P1) as P4.
  apply (induction_principle_ _ P2 P3 A P4).
Qed.


