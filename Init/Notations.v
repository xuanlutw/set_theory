(* Constants: 0 *)
Reserved Notation "∅"    (at level 0).
Reserved Notation "'ω'"  (at level 0).
Reserved Notation "'σ'"  (at level 0).
Reserved Notation "𝟢"    (at level 0).
Reserved Notation "𝟣"    (at level 0).
Reserved Notation "𝟤"    (at level 0).
Reserved Notation "'ℵ₀'" (at level 0).

(* First Levev Set Constructor: 1 *)
Reserved Notation "{ x : A | P }" (at level 1, x at level 99).
Reserved Notation "`{ x , y }"    (at level 1, x at level 99).
Reserved Notation "`{ x }"        (at level 1, x at level 99).

(* Uniary: 10~19 *)
Reserved Notation "∪ A "     (at level 10, no associativity).
Reserved Notation "∩ A "     (at level 10, no associativity).
Reserved Notation "𝒫( x )"   (at level 10, no associativity).
Reserved Notation "S( x )"   (at level 10, no associativity).
Reserved Notation "dom( A )" (at level 10, no associativity).
Reserved Notation "ran( A )" (at level 10, no associativity).
Reserved Notation "fld( A )" (at level 10, no associativity).
Reserved Notation "| A |"    (at level 10, no associativity).

(* No Associative: 20 ~ 24 *)
Reserved Notation "F [ x ]"        (at level 20, no associativity).
Reserved Notation "F ↾ A"          (at level 20, no associativity).
Reserved Notation "F ⟦ A ⟧"        (at level 20, no associativity).
Reserved Notation "E( R , A )"     (at level 20, no associativity).
Reserved Notation "EI( R , A )"    (at level 20, no associativity).
Reserved Notation "ER( R )"        (at level 20, no associativity).
Reserved Notation "⟨ A , B ⟩"      (at level 20, no associativity).
Reserved Notation "[ A ]\ R"       (at level 20, no associativity).
Reserved Notation "[ x ]( R , A )" (at level 20, no associativity).

(* Set Operator: 25 ~29 *)
Reserved Notation "A \ B" (at level 25, left associativity).
Reserved Notation "A ∪ B" (at level 26, left associativity).
Reserved Notation "A ∩ B" (at level 27, left associativity).
Reserved Notation "A ⨉ B" (at level 28, left associativity).

(* Function Operator: 30 ~ 34 *)
Reserved Notation "A ∘ B" (at level 30, right associativity).

(* Nature Number: 35 ~ 39 *)
Reserved Notation "m ^ₙ n" (at level 35, left associativity).
Reserved Notation "m ×ₙ n" (at level 36, left associativity).
Reserved Notation "m +ₙ n" (at level 37, left associativity).

(* Cardinal Number: 40 ~ 44 *)
Reserved Notation "m ^c n" (at level 40, left associativity).
Reserved Notation "m ×c n" (at level 41, left associativity).
Reserved Notation "m +c n" (at level 42, left associativity).

(* Set to Proposition: 80 ~ 89 *)
Reserved Notation "x = y"       (at level 80, no associativity).
Reserved Notation "x ≠ y"       (at level 80, no associativity).
Reserved Notation "x ∈ y"       (at level 80, no associativity).
Reserved Notation "x ∉ y"       (at level 80, no associativity).
Reserved Notation "x ⊆ y"       (at level 80, no associativity).
Reserved Notation "x ⊂ y"       (at level 80, no associativity).
Reserved Notation "x <[ R ] y"  (at level 80, no associativity).
Reserved Notation "x ≮[ R ] y"  (at level 80, no associativity).
Reserved Notation "x ≤[ R ] y"  (at level 80, no associativity).
Reserved Notation "x ≰[ R ] y"  (at level 80, no associativity).
Reserved Notation "m <ₙ n"      (at level 80, no associativity).
Reserved Notation "m ≤ₙ n"      (at level 80, no associativity).
Reserved Notation "A ≈ B"       (at level 80, no associativity).
Reserved Notation "A ≉ B"       (at level 80, no associativity).
Reserved Notation "A ≼ B"       (at level 80, no associativity).
Reserved Notation "A ⋠ B"       (at level 80, no associativity).

(* Logical: 90 ~ 99 *)
Reserved Notation "⊤"         (at level 90, no associativity).
Reserved Notation "⊥"         (at level 91, no associativity).
Reserved Notation "~ x"       (at level 92, right associativity).
Reserved Notation "x ∧ y"     (at level 93, right associativity).
Reserved Notation "x ∨ y"     (at level 94, right associativity).
Reserved Notation "x → y"     (at level 95, right associativity, y at level 200).
Reserved Notation "x ↔ y"     (at level 96, no associativity).
Reserved Notation "∃  A , P"  (at level 97, right associativity, P at level 200).
Reserved Notation "∀  A , P"  (at level 97, right associativity, P at level 200).
Reserved Notation "∀ₚ A , P"  (at level 97, right associativity, P at level 200).
Reserved Notation "∀ₚₚ A , P" (at level 97, right associativity, P at level 200).
Reserved Notation "'λ' x , P" (at level 97, right associativity).

