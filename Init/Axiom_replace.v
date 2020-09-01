Require Import Init.Logic.
Require Import Init.Operator.

(* Axiom Shema of Replacement *)
Axiom ax_replace: ∀ₚₚ P, ∀ A,
  (∀ x, ∀ y1, ∀ y2, x ∈ A → P x y1 → P x y2 → y1 = y2)
  → ∃ B, (∀ y, y ∈ B ↔ (∃x, x ∈ A ∧ (P x y))).

