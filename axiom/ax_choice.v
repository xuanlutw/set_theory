Require Import axiom.axiom.
Require Import relation.relation.
Require Import relation.function.

(* Axiom of Choice *)
Axiom ax_choice: forall R, rel R -> 
  exists H, function H /\ H ⊆ R /\ dom(H) = dom(R).
(*----------------------------------------------------------------------------*)
