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
(* Axiom of Regularity *)
Axiom ax_regular: ∀ A, ∃ m, (∃ x, x ∈ A) → m ∈ A ∧ (~∃ x, x ∈ A ∧ x ∈ m).

