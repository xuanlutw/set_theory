Require Import logic.
Require Import axiom.
Require Import basic.
Require Import relation.

(* Axiom of Choice *)
Axiom ax_choice: forall R, rel R -> 
  exists H, function H /\ H ⊆ R /\ dom(H) = dom(R).
(*----------------------------------------------------------------------------*)
