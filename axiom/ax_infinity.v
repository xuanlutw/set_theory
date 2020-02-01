Require Import axiom.axiom.

(* Axiom of Infinity *)
Definition suc (A: set) := A ∪ ({A}).
Notation "S( x )" := (suc(x)) (at level 60, no associativity).
Definition inductive (A: set) := ∅ ∈ A /\ forall x, x ∈ A -> S(x) ∈ A.
Axiom ax_infinity: exists A, inductive A.
(*----------------------------------------------------------------------------*)
