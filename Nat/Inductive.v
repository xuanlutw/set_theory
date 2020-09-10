Require Import Init.Init.
Require Import Relation.Relation.

Definition suc (A: J) := A ∪ (J{A}).
Notation   "S( x )"   := (suc(x)).

Definition inductive (A: J) := ∅ ∈ A ∧ ∀ x, x ∈ A → S(x) ∈ A.

Definition trans (A: J) := ∀ x, ∀ a, x ∈ a → a ∈ A → x ∈ A.

(* Successor *)
Lemma suc_e: ∀ A, ∀ x, x ∈ S(A) → x = A ∨ x ∈ A.
Proof.
  intros A x P1.
  destruct (union2_e _ _ _ P1) as [P2 | P2].
  + right.
    apply P2.
  + left.
    apply eq_s.
    apply (sing_e _ _ P2).
Qed.

Lemma suc_i1: ∀ A, A ∈ S(A).
Proof.
  intros A.
  apply union2_ir.
  apply sing_i.
Qed.

Lemma suc_i2: ∀ A, ∀ x, x ∈ A → x ∈ S(A).
Proof.
  intros A x P1.
  apply (union2_il _ _ _ P1).
Qed.

Lemma suc_i3: ∀ A, A ⊆ S(A).
Proof.
  intros A x P1.
  apply (suc_i2 _ _ P1).
Qed.

Lemma empty_not_suc: ∀ x, ∅ ≠ S(x).
Proof.
  intros x P1.
  apply (empty_i x).
  apply (eq_cr (λ y, x ∈ y) P1).
  apply suc_i1.
Qed.

Lemma suc_kick_self: ∀ A, S(A) \ J{A} = A.
Proof.
  intros A.
  apply sub_a.
  split.
  + intros x P1.
    destruct (compl_e _ _ _ P1) as [P2 P3].
    destruct (suc_e _ _ P2) as [P4 | P4].
    - apply bot_e.
      apply P3.
      apply (eq_cr (λ x, x ∈ J{A}) P4).
      apply sing_i.
    - apply P4.
  + intros x P1.
    apply compl_i.
    - apply (suc_i2 _ _ P1).
    - intros P2.
      apply (nin_self A).
      apply (eq_cr (λ x, x ∈ A) (sing_e _ _ P2)).
      apply P1.
Qed.
(*----------------------------------------------------------------------------*)

(* Transition *)
Lemma trans_e1: ∀ A, trans A → ∪(A) ⊆ A.
Proof.
  intros A P1 x P2.
  destruct (union_e A x P2) as [a [P3 P4]].
  apply (P1 _ _ P4 P3).
Qed.

Lemma trans_e2: ∀ A, trans A → ∀ a, a ∈ A → a ⊆ A.
Proof. 
  intros A P1 a P2 x P3.
  apply (P1 _ _ P3 P2).
Qed.

Lemma trans_e3: ∀ A, trans A → A ⊆ 𝒫(A).
Proof.
  intros A P1 x P2.
  apply power_i.
  apply (trans_e2 _ P1 _ P2).
Qed.

Lemma trans_i1: ∀ A, ∪(A) ⊆ A → trans A.
Proof.
  intros A P1 x a P2 P3.
  apply P1.
  apply union_i.
  exists a.
  apply (and_i P3 P2).
Qed.

Lemma trans_i2: ∀ A, (∀ a, a ∈ A → a ⊆ A) → trans A.
Proof.
  intros A P1 x a P2 P3.
  apply (P1 _ P3 x P2).
Qed.

Lemma trans_i3: ∀ A, A ⊆ 𝒫(A) → trans A.
Proof.
  intros A P1 x a P2 P3.
  apply (power_e _ _ (P1 _ P3) x P2).
Qed.

Lemma union_trans_suc: ∀ A, trans A → ∪(S(A)) = A.
Proof.
  intros A P1.
  apply sub_a.
  split.
  + intros x P2.
    destruct (union_e _ _ P2) as [y [P3 P4]].
    destruct (suc_e _ _ P3) as [P5|P5].
    - apply (eq_cl _ P5).
      apply P4.
    - apply (P1 _ _ P4 P5).
  + intros x P2.
    apply union_i.
    exists A.
    split.
    - apply suc_i1.
    - apply P2.
Qed.

Lemma empty_is_trans: trans ∅.
Proof.
  intros x y P1 P2.
  apply bot_e.
  apply (empty_i _ P2).
Qed.

Lemma suc_trans: ∀ A, trans A → trans (S(A)).
Proof.
  intros A P1.
  apply trans_i2.
  intros a P2 x P3.
  destruct (suc_e _ _ P2) as [P4 | P4].
  + apply suc_i2.
    apply (eq_cl (λ s, x ∈ s) P4).
    apply P3.
  + apply suc_i2.
    apply (P1 _ _ P3 P4).
Qed.
(*----------------------------------------------------------------------------*)
