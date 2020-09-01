Require Import Init.Logic.
Require Import Init.Classical.

(* Axiom of Extensionality *)
Axiom ax_exten:   ∀ A, ∀ B, (∀ x, x ∈ A ↔ x ∈ B) → A = B.
(* Axiom of Empty Set *)
Axiom ax_empty:   ∃ A, ∀ x, x ∉ A.
(* Axiom of Pairing *)
Axiom ax_pair:    ∀ A, ∀ B, ∃ C, ∀ x, x ∈ C ↔ (x = A ∨ x = B).
(* Axiom of Union *)
Axiom ax_union:   ∀ A, ∃ B, ∀ x, x ∈ B ↔ (∃ a, a ∈ A ∧ x ∈ a).
(* Axiom of Power Set *)
Axiom ax_power:   ∀ A, ∃ B, ∀ x, x ∈ B ↔ (∀ y, y ∈ x → y ∈ A). 
(* Axiom Schema of Subset *)
Axiom ax_subset:  ∀ₚ P, ∀ A, ∃ B, ∀ x, x ∈ B ↔ x ∈ A ∧ P x.

(* Some non axiom but useful theorem *)
(* Existence of the Union of Two *)
Theorem thm_union2: ∀ A, ∀ B, ∃ C, ∀ x, x ∈ C ↔ (x ∈ A ∨ x ∈ B).
Proof.
  intros A B.
  destruct (ax_pair A B) as [AB P1].
  destruct (ax_union AB) as [C P2].
  exists C.
  intro x.
  destruct (P2 x) as [P3 _].
  split.
  + intro P4.
    destruct (P3 P4) as [X [P5 P6]].
    destruct (P1 X ) as [P7 _].
    destruct (P7 P5) as [P8 | P8].
    - left. 
      apply (eq_cl _ P8).
      apply P6.
    - right.
      apply (eq_cl _ P8).
      apply P6.
  + intro P4.
    apply (P2 x).
    destruct P4 as [P4 | P4].
    - exists A.
      split.
      * apply (P1 A). left. apply eq_r.
      * apply P4.
    - exists B.
      split.
      * apply (P1 B). right. apply eq_r.
      * apply P4.
Qed.

