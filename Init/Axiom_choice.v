Require Import Init.Logic.
Require Import Init.Operator.

(* Axiom of choice *)
(* Zorn's lemma *)
Definition chain (R: J) := ∀ C, ∀ D, C ∈ R → D ∈ R → C ⊆ D ∨ D ⊆ C.
Axiom zorn: ∀ A, (∀ R, R ⊆ A → chain R → ∪R ∈ A)
  → ∃ M, M ∈ A ∧ (∀ a, a ∈ A → a = M ∨ ~(M ⊆ a)).
