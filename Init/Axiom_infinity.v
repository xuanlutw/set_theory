Require Import Init.Logic.
Require Import Init.Operator.

(* Axiom of Infinity *)
Axiom ax_infinity: ∃ A, ∅ ∈ A ∧ ∀ x, x ∈ A → x ∪ `{x} ∈ A.
