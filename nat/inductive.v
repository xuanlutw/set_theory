Require Import axiom.axiom.
Require Import operation.basic.

(* Successor *)
Definition suc (A: set) := A ∪ ({A}).
Notation "S( x )" := (suc(x)) (at level 60, no associativity).

Lemma suc_elim: forall A x, x ∈ S(A) -> x = A \/ x ∈ A.
Proof.
  intros A x P1.
  destruct (in_union2_in _ _ _ P1) as [P2|P2].
  + right.
    apply P2.
  + left.
    symmetry.
    apply (in_singleton_equal _ _ P2).
Qed.

Lemma suc_intro_1: forall A, A ∈ S(A).
Proof.
  intros A.
  apply in_in_union2_2.
  apply in_singleton.
Qed.

Lemma suc_intro_2: forall A x, x ∈ A -> x ∈ S(A).
Proof.
  intros A.
  apply in_in_union2_1.
Qed.

Lemma empty_not_suc: forall x, ∅ <> S(x).
Proof.
  intros x P1.
  absurd (x ∈ ∅).
  + apply not_in_empty.
  + rewrite P1.
    apply suc_intro_1.
Qed.
(*----------------------------------------------------------------------------*)

(* Inductive *)
Definition inductive (A: set) := ∅ ∈ A /\ forall x, x ∈ A -> S(x) ∈ A.
(*----------------------------------------------------------------------------*)

(* Transition *)
Definition trans (A: set) := forall x a, x ∈ a -> a ∈ A -> x ∈ A.

Lemma trans_elim_1: forall A, trans A -> ∪(A) ⊆ A.
Proof.
  intros A P1 x P2.
  destruct (in_union_in A x P2) as [a [P3 P4]].
  apply (P1 _ _ P4 P3).
Qed.

Lemma trans_elim_2: forall A, trans A -> forall a, a ∈ A -> a ⊆ A.
Proof. 
  intros A P1 a P2 x P3.
  apply (P1 _ _ P3 P2).
Qed.

Lemma trans_elim_3: forall A, trans A -> A ⊆ 𝒫(A).
Proof.
  intros A P1 x P2.
  apply subset_in_power.
  apply (trans_elim_2 _ P1 _ P2).
Qed.

Lemma trans_intro_1: forall A, ∪(A) ⊆ A -> trans A.
Proof.
  intros A P1 x a P2 P3.
  apply P1.
  apply (in_in_union).
  exists a.
  apply (conj P3 P2).
Qed.

Lemma trans_intro_2: forall A, (forall a, a ∈ A -> a ⊆ A) -> trans A.
Proof.
  intros A P1 x a P2 P3.
  apply (P1 _ P3 x P2).
Qed.

Lemma trans_intro_3: forall A, A ⊆ 𝒫(A) -> trans A.
Proof.
  intros A P1 x a P2 P3.
  apply (in_power_subset _ _ (P1 _ P3) x P2).
Qed.

Lemma union_trans_suc: forall A, trans A -> ∪(S(A)) = A.
Proof.
  intros A P1.
  apply ax_exten.
  intros x.
  split.
  + intros P2.
    destruct (in_union_in _ _ P2) as [y [P3 P4]].
    destruct (suc_elim _ _ P3) as [P5|P5].
    - rewrite <- P5.
      apply P4.
    - apply (P1 _ _ P4 P5).
  + intros P2.
    apply (in_in_union).
    exists A.
    split.
    - apply suc_intro_1.
    - apply P2.
Qed.

Lemma empty_is_trans: trans ∅.
Proof.
  intros x y P1 P2.  
  absurd (y ∈ ∅).
  + apply not_in_empty.
  + apply P2.
Qed.
(*----------------------------------------------------------------------------*)
