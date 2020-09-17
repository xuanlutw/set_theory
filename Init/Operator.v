Require Export Init.Notations.
Require Import Init.Logic.
Require Import Init.Classical.
Require Import Init.Axiom.

(* Operators *)
Definition subset (A B: J) := (∀ x, x ∈ A → x ∈ B).
Notation   "x ⊆ y"         := (subset x y).

Definition proper_subset (A B: J) := ((subset A B) ∧ A ≠ B).
Notation   "x ⊂ y"                := (proper_subset x y).

Definition empty_c := (ex_outl ax_empty).
Notation   "∅"     := (empty_c).

Definition pair_c (A B: J) := (ex_outl (ax_pair A B)).
Notation   "`{ x , y }"    := (pair_c x y).

Definition singleton (A: J) := (pair_c A A).
Notation   "`{ x }"         := (singleton x).

Definition union_c (A: J) := (ex_outl (ax_union A)).
Notation   "∪ A "         := (union_c A).

Definition union2_c (A B: J) := (∪(`{A, B})).
Notation   "A ∪ B"           := (union2_c A B).

Definition power_c (A: J) := (ex_outl (ax_power A)).
Notation   "𝒫( x )"       := (power_c x).

Definition sub_c (P: J → Prop) (x: J) := (ex_outl (ax_subset P x)).
Notation   "{ x : A | P }"            := (sub_c (λ x, P) A).

Definition inter_c (A: J) := ({x: ∪A| ∀ a, a ∈ A → x ∈ a}).
Notation   "∩ A"          := (inter_c A).

Definition inter2_c (A B: J) := ({x: A| x ∈ B}).
Notation   "A ∩ B"           := (inter2_c A B).

Definition complement (A B : J) := ({x: A| x ∉ B}).
Notation   "A \ B"              := (complement A B).

Definition opair (A B: J) := `{`{A}, `{A, B}}.
Notation  "⟨ A , B ⟩"     := (opair A B).

Definition in_cp (x A B: J) := ∃ a, ∃ b, a ∈ A ∧ b ∈ B ∧ x = ⟨a, b⟩.
Definition cp (A B: J)      := {x: 𝒫(𝒫(A ∪ B))| in_cp x A B}.
Notation   "A ⨉ B"          := (cp A B).
(*----------------------------------------------------------------------------*)

(* Basic Properties *)

(* Subset *)
Lemma sub_a: ∀ A, ∀ B, A ⊆ B ∧ B ⊆ A → A = B.
Proof.
  intros A B [P1 P2].
  apply ax_exten.
  intro x.
  split.
  + apply (P1 x).
  + apply (P2 x).
Qed.

Lemma sub_r: ∀ A, A ⊆ A.
Proof.
  intros A x P.
  apply P.
Qed.

Lemma sub_t: ∀ A, ∀ B, ∀ C, A ⊆ B → B ⊆ C → A ⊆ C.
Proof.
  intros A B C P1 P2 x P3.
  apply ((P2 x) ((P1 x) P3)).
Qed.

Lemma sub_i_eq: ∀ A, ∀ B, A = B → A ⊆ B.
Proof.
  intros A B P1.
  apply (eq_cl _ P1).
  apply sub_r.
Qed.

Lemma ax_exten_reverse: ∀ A, ∀ B, A = B → (∀ x, x ∈  A ↔ x ∈  B).
Proof.
  intros A B P1 x.
  apply (eq_cl (λ s, x ∈ A ↔ x ∈ s) P1).
  apply iff_r.
Qed.

Lemma sub_reduce: ∀ₚ P, ∀ A, (∀ x, (P x) → x ∈ A) → (∃ B, ∀ y, y ∈ B ↔ (P y)).
Proof.
  intros P A P1.
  exists {x : A | P x}.
  intros x.
  destruct (ex_outr (ax_subset P A) x) as [P2 P3].
  split.
  + apply P2.
  + intros P4.
    apply P3.
    apply (and_i (P1 x P4) P4).
Qed.

Lemma sub_i: ∀ₚ P, ∀ A, ∀ x, x ∈ A → (P x) → x ∈ {y: A| P y}.
Proof.
  intros P A x P1 P2.
  destruct (ex_outr (ax_subset P A) x) as [_ P3].
  apply P3.
  apply (and_i P1 P2).
Qed.

Lemma sub_e: ∀ₚ P, ∀ A, ∀ x, x ∈  {y: A| P y} → x ∈ A ∧ (P x).
Proof.
  intros P A x P1.
  destruct (ex_outr (ax_subset P A) x) as [P2 _].
  apply (P2 P1).
Qed.

Lemma sub_e1: ∀ₚ P, ∀ A, {y: A| P y} ⊆ A.
Proof.
  intros P A x P1.
  destruct (sub_e _ _ _ P1) as [P2 _].
  apply P2.
Qed.
(*----------------------------------------------------------------------------*)

(* Non Equality *)
Lemma neq_e: ∀ A, ∀ B, A ≠ B → ∃ x, (x ∈ A ∧ x ∉  B) ∨ (x ∈ B ∧ x ∉  A).
Proof.
  intros A B.
  apply contraposition2.
  intros P1.
  apply sub_a.
  split.
  + intros x P2. 
    destruct (not_or_and (not_ex_all_not _ P1 x)) as [P3 _].
    destruct (not_and_or P3) as [P4 | P4].
    - apply (bot_e _ (P4 P2)).
    - apply (nn_e P4). 
  + intros x P2.
    destruct (not_or_and (not_ex_all_not _ P1 x)) as [_ P3].
    destruct (not_and_or P3) as [P4 | P4].
    - apply (bot_e _ (P4 P2)).
    - apply (nn_e P4). 
Qed.

Lemma neq_i: ∀ A, ∀ B, ∀ x, x ∈ A → x ∉  B → A ≠ B.
Proof.
  intros A B x P1 P2 P3.
  apply (P2 (eq_cl _ P3 P1)).
Qed.
(*----------------------------------------------------------------------------*)

(* Proper Subset *)
Lemma psub_i: ∀ A, ∀ B, A ⊆ B → A ≠ B → A ⊂ B.
Proof.
  intros A B P1 P2.
  apply (and_i P1 P2).
Qed.

Lemma psub_i1: ∀ A, ∀ B, (∀ x, x ∈ A → x ∈ B) → (∃ y, y ∈ A ∧ y ∉  B) → A ⊂ B.
Proof.
  intros A B P1 [y [P2 P3]].
  split.
  + intros x P4.
    apply (P1 _ P4).
  + apply (neq_i _ _ _ P2 P3).
Qed.

Lemma psub_e: ∀ A, ∀ B, A ⊂ B → A ⊆ B.
Proof.
  intros A B [P1 _].
  apply P1.
Qed.

Lemma psub_e1: ∀ A, ∀ B, A ⊂ B → A ≠ B.
Proof.
  intros A B [_ P1].
  apply P1.
Qed.

Lemma psub_e2: ∀ A, ∀ B, A ⊂ B → ∃ x, x ∉ A ∧ x ∈ B.
Proof.
  intros A B [P1 P2].
  destruct (neq_e _ _ P2) as [x [[P3 P4] | [P3 P4]]].
  + apply bot_e.
    apply P4.
    apply (P1 _ P3).
  + exists x.
    apply (and_i P4 P3).
Qed.

Lemma psub_ir: ∀ A, ~ A ⊂ A.
Proof.
  intros A P1.
  apply (psub_e1 _ _ P1).
  apply eq_r.
Qed.

Lemma sub_e2: ∀ A, ∀ B, A ⊆ B → A ⊂ B ∨ A = B.
Proof.
  intros A B P1.
  destruct (LEM (A = B)) as [P2 | P2].
  + right.
    apply P2.
  + left.
    apply (psub_i _ _ P1 P2).
Qed.

Lemma psub_t: ∀ A, ∀ B, ∀ C, A ⊂ B → B ⊂ C → A ⊂ C.
Proof.
  intros A B C P1 P2.
  apply psub_i.
  + intros x P3.
    pose (psub_e _ _ P1 _ P3) as P4.
    apply (psub_e _ _ P2 _ P4).
  + destruct (psub_e2 _ _ P1) as [x [P3 P4]].
    apply neq_s.
    apply (neq_i _ _ x).
    - apply (psub_e _ _ P2 _ P4).
    - apply P3.
Qed.
(*----------------------------------------------------------------------------*)

(* Empty Set *)
Lemma empty_i: ∀ A, A ∉  ∅.
Proof.
  intro A.
  apply (ex_outr ax_empty A).
Qed.

Lemma empty_i1: ∀ A, ∅ ⊆ A.
Proof.
  intros A x P1.
  apply (bot_e _ (empty_i _ P1)).
Qed.

Lemma empty_unique: ∀ A, (∀ B, B ∉ A) → A = ∅ .
Proof.
  intros A P1.
  apply ax_exten.
  intro x.
  split.
  + intro P3. 
    apply (bot_e _ (P1 _ P3)).
  + intro P3.
    apply (bot_e _ (empty_i _ P3)).
Qed.

Lemma nempty_ex: ∀ A, A ≠ ∅  → (∃ x, x ∈ A).
Proof.
  intros A.
  apply contraposition2.
  intro P1.
  apply empty_unique.
  apply not_ex_all_not.
  apply P1. 
Qed.

Lemma ex_nempty: ∀ A, (∃ x, x ∈ A) → A ≠ ∅.
Proof.
  intros A [x P1] P2.
  apply (empty_i x).
  apply (eq_cl _ P2 P1).
Qed.

Lemma sub_empty: ∀ₚ P, ∀ A, ∀ t, {y: A| P y} = ∅ → t ∈ A → ~(P t).
Proof.
  intros P A t P1 P2 P3.
  apply (empty_i t).
  apply (eq_cl _ P1).
  apply (sub_i _ _ _ P2 P3).
Qed.

Lemma sub_empty_empty: ∀ S, S ⊆ ∅ → S = ∅.
Proof.
  intros S P1.
  apply sub_a.
  split.
  + intros x P2.
    apply (P1 _ P2).
  + intros x P2.
    apply bot_e.
    apply (empty_i _ P2).
Qed.
(*----------------------------------------------------------------------------*)

(* Power set *)
Lemma power_e: ∀ A, ∀ x, x ∈ 𝒫(A) → x ⊆ A.
Proof.
  intros A x P1 y P2.
  destruct (ex_outr (ax_power A) x) as [P3 _].
  apply (P3 P1 _ P2).
Qed.

Lemma power_i: ∀ A, ∀ x, x ⊆ A → x ∈ 𝒫(A).
Proof.
  intros A x P1.
  destruct (ex_outr (ax_power A) x) as [_ P2].
  apply (P2 P1).
Qed.

Lemma in_power: ∀ A, A ∈ 𝒫(A).
Proof.
  intros A.
  apply power_i.
  apply sub_r.
Qed.
(*----------------------------------------------------------------------------*)

(* Union *)
Lemma union_e: ∀ A, ∀ x, x ∈ ∪(A) → (∃ y, y ∈ A ∧ x ∈ y).
Proof.
  intros A x P1.
  destruct (ex_outr (ax_union A) x) as [P2 _].
  apply (P2 P1).
Qed.

Lemma union_i: ∀ A, ∀ x, (∃ y, y ∈ A ∧ x ∈ y) → x ∈ ∪(A).
Proof.
  intros A x P1.
  destruct (ex_outr (ax_union A) x) as [_ P2].
  apply (P2 P1).
Qed.

Lemma union_i2: ∀ A, ∀ x, x ∈ A → x ⊆ ∪A.
Proof.
  intros A x P1 s P2.
  apply union_i.
  exists x.
  apply (and_i P1 P2).
Qed.
(*----------------------------------------------------------------------------*)

(* Pair and Singleton *)
Lemma pair_e: ∀ A, ∀ B, ∀ x, x ∈ `{A, B} → x = A ∨ x = B.
Proof.
  intros A B x P1.
  destruct (ex_outr (ax_pair A B) x) as [P2 _].
  apply (P2 P1).
Qed.

Lemma pair_il: ∀ A, ∀ B, A ∈ `{A, B}.
Proof.
  intros A B.
  destruct (ex_outr (ax_pair A B) A) as [_ P2].
  apply P2.
  left.
  apply eq_r.
Qed.

Lemma pair_ir: ∀ A, ∀ B, B ∈ `{A, B}.
Proof.
  intros A B.
  destruct (ex_outr (ax_pair A B) B) as [_ P2].
  apply P2.
  right.
  apply eq_r.
Qed.

Lemma pair_s: ∀ A, ∀ B, `{A, B} = `{B, A}.
Proof.
  intros A B.
  apply sub_a.
  split.
  + intros x P1.
    destruct (pair_e _ _ _ P1) as [P2 | P2].
    - apply (eq_cr (λ y, y ∈ `{B, A}) P2).
      apply pair_ir.
    - apply (eq_cr (λ y, y ∈ `{B, A}) P2).
      apply pair_il.
  + intros x P1.
    destruct (pair_e _ _ _ P1) as [P2 | P2].
    - apply (eq_cr (λ y, y ∈ `{A, B}) P2).
      apply pair_ir.
    - apply (eq_cr (λ y, y ∈ `{A, B}) P2).
      apply pair_il.
Qed.

Lemma pair_eql: ∀ A, ∀ B, ∀ C, ∀ D, `{A, B} = `{C, D} → A = C ∨ A = D.
Proof.
  intros A B C D P1.
  pose (pair_il A B) as P2.
  pose (eq_cl _ P1 P2) as P3.
  apply (pair_e _ _ _ P3). 
Qed.

Lemma pair_eqr: ∀ A, ∀ B, ∀ C, ∀ D, `{A, B} = `{C, D} → B = C ∨ B = D.
Proof.
  intros A B C D P1.
  pose (pair_ir A B) as P2.
  pose (eq_cl _ P1 P2) as P3.
  apply (pair_e _ _ _ P3). 
Qed.

Lemma sing_i: ∀ A, A ∈ `{A}.
Proof.
  intros A.
  destruct (ex_outr (ax_pair A A) A) as [_ P1].
  apply P1.
  left.
  apply eq_r.
Qed.

Lemma sing_i2: ∀ A, ∀ B, A = B → A ∈ `{B}.
Proof.
  intros A B P1.
  apply (eq_cl (λ x, A ∈ `{x}) P1).
  apply sing_i.
Qed.

Lemma sing_e: ∀ A, ∀ B, B ∈ `{A} → A = B.
Proof.
  intros A B P1.
  destruct (ex_outr (ax_pair A A) B) as [P2 _].
  destruct (P2 P1) as [P3 | P3].
  + apply eq_s.
    apply P3.
  + apply eq_s.
    apply P3.
Qed.

Lemma nsing_i: ∀ A, ∀ B, A ≠ B → B ∉ `{A}.
Proof.
  intros A B.
  apply contraposition1.
  apply sing_e.
Qed.

Lemma nsing_e: ∀ A, ∀ B, B ∉ `{A} → A ≠ B.
Proof.
  intros A B.
  apply contraposition1.
  intros P1.
  generalize (eq_s P1).
  apply sing_i2.
Qed.
  
Lemma sing_sub_i: ∀ A, ∀ B, A ∈ B → `{A} ⊆ B.
Proof.
  intros A B P1 x P2.
  apply (eq_cl (λ x, x ∈ B) (sing_e _ _ P2)).
  apply P1.
Qed.

Lemma sing_sub_e: ∀ A, ∀ B, `{A} ⊆ B → A ∈ B.
Proof.
  intros A B P1.
  apply P1.
  apply sing_i.
Qed.

Lemma sing_nempty: ∀ A, `{A} ≠ ∅.
Proof.
  intros A.
  apply ex_nempty.
  exists A.
  apply sing_i.
Qed.

Lemma sing_pair_eq1: ∀ A, ∀ B, ∀ C, `{A} = `{B, C} → A = B.
Proof.
  intros A B C P1.
  apply sing_e.
  apply (eq_cr _ P1).
  apply pair_il.
Qed.

Lemma sing_pair_eq2: ∀ A, ∀ B, ∀ C, `{A} = `{B, C} → A = C.
Proof.
  intros A B C P1.
  pose (eq_t P1 (pair_s B C)) as P2.
  apply (sing_pair_eq1 _ _ _ P2).
Qed.

Lemma sing_pair_eq3: ∀ A, ∀ B, ∀ C, `{A} = `{B, C} → B = C.
Proof.
  intros A B C P1.
  pose (eq_s (sing_pair_eq1 _ _ _ P1)) as P2.
  pose (sing_pair_eq2 _ _ _ P1) as P3.
  apply (eq_t P2 P3).
Qed.

Lemma sing_eq: ∀ A, ∀ B, `{A} = `{B} → A = B.
Proof.
  intros A B P1.
  apply sing_e.
  apply (eq_cr _ P1).
  apply sing_i.
Qed.
(*----------------------------------------------------------------------------*)

(* Union of Two *)
Lemma union2_e: ∀ A, ∀ B, ∀ x, x ∈ A ∪ B → x ∈ A ∨ x ∈ B.
Proof.
  intros A B x P1.
  destruct (union_e _ _ P1) as [a [P2 P3]].
  destruct (pair_e _ _ _ P2) as [P4 | P4].
  + left.
    apply (eq_cl (λ y, x ∈ y) P4).
    apply P3.
  + right.
    apply (eq_cl (λ y, x ∈ y) P4).
    apply P3.
Qed.

Lemma union2_il: ∀ A, ∀ B, ∀ x, x ∈ A → x ∈ A ∪ B.
Proof.
  intros A B x P1.
  apply union_i.
  exists A.
  split.
  + apply pair_il.
  + apply P1.
Qed.

Lemma union2_ir: ∀ A, ∀ B, ∀ x, x ∈ B → x ∈ A ∪ B.
Proof.
  intros A B x P1.
  apply union_i.
  exists B.
  split.
  + apply pair_ir.
  + apply P1.
Qed.

Lemma union2_en: ∀ A, ∀ B, ∀ x, x ∉ A ∪ B → x ∉ A ∧ x ∉ B.
Proof.
  intros A B x P1.
  split.
  + intros P2.
    apply P1.
    apply (union2_il _ _ _ P2).
  + intros P2.
    apply P1.
    apply (union2_ir _ _ _ P2).
Qed.

Lemma union2_s: ∀ A, ∀ B, A ∪ B = B ∪ A.
Proof.
  intros A B.
  apply sub_a.
  split.
  + intros x P1.
    destruct (union2_e _ _ _ P1) as [P2 | P2].
    - apply (union2_ir _ _ _ P2).
    - apply (union2_il _ _ _ P2).
  + intros x P1.
    destruct (union2_e _ _ _ P1) as [P2 | P2].
    - apply (union2_ir _ _ _ P2).
    - apply (union2_il _ _ _ P2).
Qed.

Lemma union2_sub: ∀ A, ∀ B, ∀ C, A ⊆ C → B ⊆ C → A ∪ B ⊆ C.
Proof.
  intros A B C P1 P2 x P3.
  destruct (union2_e _ _ _ P3) as [P4 | P4].
  + apply (P1 _ P4).
  + apply (P2 _ P4).
Qed.

Lemma union2_sub_l: ∀ A, ∀ B, A ⊆ A ∪ B.
Proof.
  intros A B x P1.
  apply union2_il.
  apply P1.
Qed.

Lemma union2_sub_r: ∀ A, ∀ B, B ⊆ A ∪ B.
Proof.
  intros A B x P1.
  apply union2_ir.
  apply P1.
Qed.

Lemma union2_sub_absorb_l: ∀ A, ∀ B, A ⊆ B → A ∪ B = B.
Proof.
  intros A B P1.
  apply sub_a.
  split.
  + intros x P2.
    destruct (union2_e _ _ _ P2) as [P3 | P3].
    - apply (P1 _ P3).
    - apply P3.
  + intros x P2.
    apply (union2_ir _ _ _ P2).
Qed.

Lemma union2_sub_absorb_r: ∀ A, ∀ B, A ⊆ B → B ∪ A = B.
Proof.
  intros A B P1.
  apply (eq_t (union2_s B A)).
  apply (union2_sub_absorb_l _ _ P1).
Qed.

Lemma union2_empty_absorb_l: ∀ A, ∅ ∪ A = A.
Proof.
  intros A.
  apply sub_a.
  split.
  + intros x P1.
    destruct (union2_e _ _ _ P1) as [P2 | P2].
    - apply bot_e. 
      apply (empty_i _ P2).
    - apply P2.
  + intros x P1.
    apply (union2_ir _ _ _ P1).
Qed.

Lemma union2_empty_absorb_r: ∀ A, A ∪ ∅ = A.
Proof.
  intros A.
  apply (eq_t (union2_s A ∅)).
  apply union2_empty_absorb_l.
Qed.

Lemma union2_sub_weak_l: ∀ A, ∀ B, ∀ C, C ⊆ A → C ⊆ (A ∪ B).
Proof.
  intros A B C P1 x P2.
  apply union2_il.
  apply (P1 _ P2).
Qed.

Lemma union2_sub_weak_r: ∀ A, ∀ B, ∀ C, C ⊆ B → C ⊆ (A ∪ B).
Proof.
  intros A B C P1 x P2.
  apply union2_ir.
  apply (P1 _ P2).
Qed.

Lemma union2_sub_preserve_l: ∀ A, ∀ A', ∀ B, A ⊆ A' → A ∪ B ⊆ A' ∪ B.
Proof.
  intros A A' B P1 x P2.
  destruct (union2_e _ _ _ P2) as [P3 | P3].
  + apply (union2_il _ _ _ (P1 _ P3)).
  + apply (union2_ir _ _ _ P3).
Qed.

Lemma union2_sub_preserve_r: ∀ A, ∀ B, ∀ B', B ⊆ B' → A ∪ B ⊆ A ∪ B'.
  intros A A' B P1 x P2.
  destruct (union2_e _ _ _ P2) as [P3 | P3].
  + apply (union2_il _ _ _ P3).
  + apply (union2_ir _ _ _ (P1 _ P3)).
Qed.

Lemma union2_sing_e: ∀ A, ∀ a, ∀ x, x ∈ A ∪ `{a} → x ∈ A ∨ x = a.
Proof.
  intros A a x P1.
  destruct (union2_e _ _ _ P1) as [P2 | P2].
  + left.
    apply P2.
  + right.
    apply (eq_s (sing_e _ _ P2)).
Qed.

Lemma union2_sing_il: ∀ A, ∀ a, ∀ x, x ∈ A → x ∈ A ∪ `{a}.
Proof.
  intros A a x.
  apply union2_il.
Qed.

Lemma union2_sing_ir: ∀ A, ∀ a, a ∈ A ∪ `{a}.
Proof.
  intros A a.
  apply union2_ir.
  apply sing_i.
Qed.
(*----------------------------------------------------------------------------*)

(* Intersection *)
Lemma inter_e: ∀ A, ∀ x, x ∈ ∩A → (∀ a, a ∈ A → x ∈ a).
Proof.
  intros A x P1 a P2.
  destruct (sub_e _ _ _ P1) as [_ P3].
  apply (P3 _ P2).
Qed.

Lemma inter_i: ∀ A, ∀ x, A ≠ ∅ → (∀ a, a ∈ A → x ∈ a) → x ∈ ∩A.
Proof.
  intros A x P1 P2.
  apply sub_i.
  + apply union_i.
    destruct (nempty_ex _ P1) as [a P3].
    exists a.
    split.
    - apply P3.
    - apply (P2 _ P3).
  + apply P2.
Qed.

Lemma inter_sub: ∀ A, ∀ a, a ∈ A → ∩A ⊆ a.
Proof.
  intros A a P1 x P2.
  apply (inter_e _ _ P2 _ P1).
Qed.
(*----------------------------------------------------------------------------*)

(* Intersection of Two *)
Lemma inter2_e: ∀ A, ∀ B, ∀ x, x ∈ A ∩ B → x ∈ A ∧ x ∈ B.
Proof.
  intros A B.
  apply sub_e.
Qed.

Lemma inter2_i: ∀ A, ∀ B, ∀ x, x ∈ A → x ∈ B → x ∈ A ∩ B.
Proof.
  intros A B.
  apply sub_i.
Qed.

Lemma inter2_s: ∀ A, ∀ B, A ∩ B = B ∩ A.
Proof.
  intros A B.
  apply sub_a.
  split.
  + intros x P1.
    destruct (inter2_e _ _ _ P1) as [P2 P3].
    apply (inter2_i _ _ _ P3 P2).
  + intros x P1.
    destruct (inter2_e _ _ _ P1) as [P2 P3].
    apply (inter2_i _ _ _ P3 P2).
Qed.
  
Lemma inter2_sub_l: ∀ A, ∀ B, A ∩ B ⊆ A.
Proof.
  intros A B x P1.
  destruct (inter2_e _ _ _ P1) as [P2 _].
  apply P2.
Qed.

Lemma inter2_sub_r: ∀ A, ∀ B, A ∩ B ⊆ B.
Proof.
  intros A B.
  apply (eq_cl (λ x, x ⊆ B) (inter2_s B A)).
  apply inter2_sub_l.
Qed.

Lemma inter2_absorb_l: ∀ A, ∀ B, A ⊆ B → A ∩ B = A.
Proof.
  intros A B P1.
  apply sub_a.
  split.
  + intros x P2.
    destruct (inter2_e _ _ _ P2) as [P3 _].
    apply P3.
  + intros x P2.
    apply inter2_i.
    - apply P2.
    - apply (P1 _ P2).
Qed.

Lemma inter2_absorb_r: ∀ A, ∀ B, B ⊆ A → A ∩ B = B.
Proof.
  intros A B P1.
  apply (eq_cr (λ x, x = B) (inter2_s _ _)).
  apply (inter2_absorb_l _ _ P1).
Qed.

Lemma inter2_eq_sub_l: ∀ A, ∀ B, A ∩ B = A → A ⊆ B.
Proof.
  intros A B P1 x P2.
  pose (eq_cr (λ y, x ∈ y) P1 P2) as P3.
  destruct (inter2_e _ _ _ P3) as [_ P4].
  apply P4.
Qed.

Lemma inter2_eq_sub_r: ∀ A, ∀ B, A ∩ B = B → B ⊆ A.
Proof.
  intros A B P1.
  apply inter2_eq_sub_l.
  apply (eq_cr (λ x, x = B) (inter2_s _ _)).
  apply P1.
Qed.

Lemma inter2_empty: ∀ A, ∀ B, (∀ x, x ∈ A → x ∉ B) → A ∩ B = ∅.
Proof.
  intros A B P1.
  apply sub_a.
  split.
  + intros x P2.
    destruct (inter2_e _ _ _ P2) as [P3 P4].
    apply bot_e.
    apply (P1 _ P3 P4).
  + intros x P2.
    apply bot_e.
    apply (empty_i _ P2).
Qed.

Lemma sub_inter2: ∀ A, ∀ B, ∀ C, C ⊆ A → C ⊆ B → C ⊆ A ∩ B.
Proof.
  intros A B C P1 P2 x P3.
  apply inter2_i.
  + apply (P1 x P3).
  + apply (P2 x P3).
Qed.

Lemma sub_inter2_el: ∀ A, ∀ B, ∀ C, C ⊆ A ∩ B → C ⊆ A.
Proof.
  intros A B C P1 x P2.
  destruct (inter2_e _ _ _ (P1 x P2)) as [P3 _].
  apply P3.
Qed.
 
Lemma sub_inter2_er: ∀ A, ∀ B, ∀ C, C ⊆ A ∩ B → C ⊆ B.
Proof.
  intros A B C.
  apply (eq_cl (λ x, C ⊆ x → C ⊆ B) (inter2_s B A)).
  apply sub_inter2_el.
Qed.

Lemma disjoint_selection: ∀ A, ∀ B, ∀ x, A ∩ B = ∅ → x ∈ A ∪ B → 
  (x ∈ A ∧ x ∉  B) ∨ (x ∈ B ∧ x ∉  A).
Proof.
  intros A B x P1 P2.
  destruct (union2_e _ _ _ P2) as [P3 | P3].
  + left.
    split.
    - apply P3.
    - intros P4.
      apply bot_e.
      apply (empty_i x).
      apply (eq_cl _ P1).
      apply (inter2_i _ _ _ P3 P4).
  + right.
    split.
    - apply P3.
    - intros P4.
      apply bot_e.
      apply (empty_i x).
      apply (eq_cl _ P1).
      apply (inter2_i _ _ _ P4 P3).
Qed.
(*----------------------------------------------------------------------------*)

(* Complement *)
Lemma compl_i: ∀ A, ∀ B, ∀ x, x ∈ A → x ∉  B → x ∈ A \ B.
Proof.
  intros A B x P1 P2.
  apply (sub_i _ _ _ P1 P2).
Qed.

Lemma compl_e: ∀ A, ∀ B, ∀ x, x ∈ A \ B → x ∈ A ∧ x ∉  B.
Proof.
  intros A B x P1.
  apply (sub_e _ _ _ P1).
Qed.

Lemma compl_exchange: ∀ A, ∀ B, ∀ C, A \ B \ C = A \ C \ B.
Proof.
  intros A B C.
  apply sub_a.
  split.
  + intros x P1.
    destruct (compl_e _ _ _ P1) as [P2 P3].
    destruct (compl_e _ _ _ P2) as [P4 P5].
    apply compl_i.
    - apply compl_i.
      * apply P4.
      * apply P3.
    - apply P5.
  + intros x P1.
    destruct (compl_e _ _ _ P1) as [P2 P3].
    destruct (compl_e _ _ _ P2) as [P4 P5].
    apply compl_i.
    - apply compl_i.
      * apply P4.
      * apply P3.
    - apply P5.
Qed.

Lemma compl_inter2: ∀ A, ∀ B, A ∩ (B \ A) = ∅.
Proof.
  intros A B.
  apply sub_a.
  split.
  + intros x P1.
    destruct (inter2_e _ _ _ P1) as [P2 P3].
    destruct (compl_e _ _ _ P3) as [_ P4].
    apply (bot_e _ (P4 P2)).
  + intros x P1.
    apply (bot_e _ (empty_i _ P1)). 
Qed.

Lemma compl_inter2_2: ∀ A, ∀ B, A ∩ (A \ B)= A \ B.
Proof.
  intros A B.
  apply sub_a.
  split.
  + intros x P1.
    destruct (inter2_e _ _ _ P1) as [_ P2].
    apply P2.
  + intros x P1.
    destruct (compl_e _ _ _ P1) as [P2 _].
    apply inter2_i.
    - apply P2.
    - apply P1.
Qed.

Lemma compl_dilemma: ∀ A, ∀ B, ∀ x, x ∈ A → x ∈ A ∩ B ∨ x ∈ A \ B.
Proof.
  intros A B x P1.
  destruct (LEM (x ∈ B)) as [P2 | P2].
  + left.
    apply (inter2_i _ _ _ P1 P2).
  + right.
    apply (compl_i _ _ _ P1 P2).
Qed.

Lemma compl_union2: ∀ A, ∀ B, A ∪ (B \ A) = A ∪ B.
Proof.
  intros A B.
  apply sub_a.
  split.
  + intros x P1.
    destruct (union2_e _ _ _ P1) as [P2 | P2].
    - apply (union2_il _ _ _ P2).
    - destruct (compl_e _ _ _ P2) as [P3 _].
      apply (union2_ir _ _ _ P3).
  + intros x P1.
    destruct (union2_e _ _ _ P1) as [P2 | P2].
    - apply (union2_il _ _ _ P2).
    - destruct (LEM (x ∈ A)) as [P3 | P3].
      * apply (union2_il _ _ _ P3).
      * apply (union2_ir _ _ _ (compl_i _ _ _ P2 P3)).
Qed.

Lemma compl_sub: ∀ A, ∀ B, (A \ B) ⊆ A.
Proof.
  intros A B x P1.
  destruct (compl_e _ _ _ P1) as [P2 _].
  apply P2.
Qed.

Lemma compl_psub: ∀ A, ∀ B, B ⊆ A → B ≠ ∅ → A \ B ⊂ A.
Proof.
  intros A B P1 P2.
  apply psub_i.
  + apply compl_sub.
  + intros P3.
    destruct (nempty_ex _ P2) as [x P4].
    pose (eq_cr (λ y, x ∈ y) P3 (P1 _ P4)) as P5.
    destruct (compl_e _ _ _ P5) as [_ P6].
    apply (P6 P4).
Qed.

Lemma compl_sub_reverse: ∀ A, ∀ B1, ∀ B2, B1 ⊆ B2 → A \ B2 ⊆ A \ B1.
Proof.
  intros A B1 B2 P1 x P2.
  destruct (compl_e _ _ _ P2) as [P3 P4].
  apply compl_i.
  + apply P3.
  + intros P5.
    apply P4.
    apply (P1 _ P5).
Qed.

Lemma compl_psub_ex: ∀ A, ∀ B, A ⊂ B → ∃ x, x ∈ B \ A.
Proof.
  intros A B [P1 P2].
  destruct (neq_e _ _ P2) as [x P3].
  exists x.
  destruct P3 as [[P3 P4] | [P3 P4]].
  + apply (bot_e _ (P4 (P1 _ P3))).
  + apply (compl_i _ _ _ P3 P4).
Qed.

Lemma compl_psub_nempty: ∀ A, ∀ B, A ⊂ B → B \ A ≠ ∅.
Proof.
  intros A B P1.
  apply ex_nempty.
  apply (compl_psub_ex _ _ P1).
Qed.

Lemma compl_empty: ∀ A, ∀ B, A \ B = ∅ → A ⊆ B.
Proof.
  intros A B P1 x P2.
  apply nn_e.
  intros P3.
  apply (empty_i x).
  apply (eq_cl (λ s, x ∈ s) P1).
  apply (compl_i _ _ _ P2 P3).
Qed.

Lemma compl_union2_annihilate: ∀ A, ∀ B, B ⊆ A → (A \ B) ∪ B = A.
Proof.
  intros A B P1.
  apply sub_a.
  split.
  + intros x P2.
    destruct (union2_e _ _ _ P2) as [P3 | P3].
    - destruct (compl_e _ _ _ P3) as [P4 _].
      apply P4.
    - apply (P1 _ P3).
  + intros x P2.
    destruct (LEM (x ∈ B)) as [P3 | P3].
    - apply union2_ir.
      apply P3.
    - apply union2_il.
      apply compl_i.
      * apply P2.
      * apply P3.
Qed.
(*----------------------------------------------------------------------------*)

(* Order Pairs *)
Lemma opair_e: ∀ A, ∀ B, ∀ x, x ∈ ⟨A, B⟩ → x = `{A} ∨ x = `{A, B}.
Proof.
  intros A B x P1.
  apply (pair_e _ _ _ P1).
Qed.

(* 3A *)
Theorem opair_eq_i: ∀ A, ∀ B, ∀ C, ∀ D, (A = C) → (B = D) → ⟨A, B⟩ = ⟨C, D⟩.
Proof.
  intros A B C D P1 P2.
  apply (eq_cl (λ x, ⟨A, B⟩ = ⟨x, D⟩) P1).
  apply (eq_cl (λ x, ⟨A, B⟩ = ⟨A, x⟩) P2).
  apply eq_r.
Qed.

Theorem opair_eq_e: ∀ A, ∀ B, ∀ C, ∀ D, ⟨A, B⟩ = ⟨C, D⟩ → (A = C) ∧ (B = D).
Proof.
  intros A B C D P1.
  destruct (pair_eql _ _ _ _ P1) as [P2 | P2].
  + destruct (pair_eqr _ _ _ _ (eq_s P1)) as [P3 | P3].
    - split.
      * apply (sing_eq _ _ P2).
      * destruct (pair_eqr _ _ _ _ P1) as [P4 | P4].
        ++apply (eq_cl _ (sing_pair_eq2 _ _ _ (eq_s P3))).
          apply (eq_s (sing_pair_eq3 _ _ _ (eq_s P4))).
        ++destruct (pair_eqr _ _ _ _ P4) as [P5 | P5].
          --apply (eq_t P5). 
            apply (sing_pair_eq3 _ _ _ (eq_s P3)).
          --apply P5.
    - split.
      * apply (sing_eq _ _ P2).
      * destruct (pair_eqr _ _ _ _ P3) as [P4 | P4].
        ++destruct (pair_eqr _ _ _ _ (eq_s P3)) as [P5 | P5].
          --apply (eq_t P5).
            apply (eq_t (sing_eq _ _ (eq_s P2))).
            apply (eq_s P4).
          --apply P5.
        ++apply (eq_s P4).
  + split.
    - apply (sing_pair_eq1 _ _ _ P2).
    - destruct (pair_eqr _ _ _ _ P1) as [P3 | P3].
      * apply (eq_t (eq_s (sing_pair_eq3 _ _ _ (eq_s P3)))).
        apply (sing_pair_eq2 _ _ _ P2).
      * destruct (pair_eqr _ _ _ _ P3) as [P4 | P4].
        ++apply(eq_t P4).
          apply (sing_pair_eq3 _ _ _ P2).
        ++apply P4.
Qed.

Theorem opair_eq_el: ∀ A, ∀ B, ∀ C, ∀ D, ⟨A, B⟩ = ⟨C, D⟩ → A = C.
Proof.
  intros A B C D P1.
  destruct (opair_eq_e _ _ _ _ P1) as [P2 _].
  apply P2.
Qed.

Theorem opair_eq_er: ∀ A, ∀ B, ∀ C, ∀ D, ⟨A, B⟩ = ⟨C, D⟩ → B = D.
Proof.
  intros A B C D P1.
  destruct (opair_eq_e _ _ _ _ P1) as [_ P2].
  apply P2.
Qed.

Lemma opair_superset: ∀ A, ∀ B, ∀ C, A ∈ C → B ∈ C → ⟨A, B⟩ ∈ 𝒫(𝒫(C)).
Proof.
  intros A B C P1 P2.
  apply power_i.
  intros x P3.
  apply power_i.
  intros y P4.
  destruct (pair_e _ _ _ P3) as [P5 | P5].
  + apply (eq_cl (λ x, x ∈ C) (sing_e _ _ (eq_cl _ P5 P4))).
    apply P1.
  + destruct (pair_e _ _ _ (eq_cl (λ x, y ∈ x) P5 P4)) as [P6 | P6].
    - apply (eq_cr (λ x, x ∈ C) P6).
      apply P1.
    - apply (eq_cr (λ x, x ∈ C) P6).
      apply P2.
Qed.

Lemma opair_eq_swap: ∀ a, ∀ b, ∀ c, ∀ d, ⟨a, b⟩ = ⟨c, d⟩ → ⟨b, a⟩ = ⟨d, c⟩.
Proof.
  intros a b c d P1.
  apply (eq_cl (λ x, ⟨b, a⟩ = ⟨d, x⟩) (opair_eq_el _ _ _ _ P1)).
  apply (eq_cl (λ x, ⟨b, a⟩ = ⟨x, a⟩) (opair_eq_er _ _ _ _ P1)).
  apply eq_r.
Qed.
(*----------------------------------------------------------------------------*)

(* Cartesion Product *)
Lemma cp_i: ∀ A, ∀ B, ∀ x, ∀ y, x ∈ A → y ∈ B → ⟨x, y⟩ ∈ A ⨉ B.
Proof.
  intros A B x y P1 P2.
  apply sub_i.
  + apply opair_superset.
    - apply (union2_il _ _ _ P1).
    - apply (union2_ir _ _ _ P2).
  + exists x.
    exists y.
    repeat split.
    - apply P1.
    - apply P2.
Qed.

Lemma cp_e: ∀ A, ∀ B, ∀ x, x ∈ A ⨉ B → in_cp x A B.
  intros A B x P1.
  apply (sub_e _ _ _ P1).
Qed.

Lemma cp_e2: ∀ x, ∀ y, ∀ A, ∀ B, ⟨x, y⟩ ∈ A ⨉ B → x ∈ A ∧ y ∈ B.
Proof.
  intros x y A B P1.
  destruct (cp_e _ _ _ P1) as [a [b [P2 [P3 P4]]]].
  split.
  + apply (eq_cr (λ x, x ∈ A) (opair_eq_el _ _ _ _ P4)).
    apply P2.
  + apply (eq_cr (λ x, x ∈ B) (opair_eq_er _ _ _ _ P4)).
    apply P3.
Qed.

Lemma cp_swap: ∀ A, ∀ B, ∀ x, ∀ y, ⟨x, y⟩ ∈ cp A B → ⟨y, x⟩ ∈ B ⨉ A.
Proof.
  intros A B x y P1.
  destruct (cp_e2 _ _ _ _ P1) as [P2 P3]. 
  apply (cp_i _ _ _ _ P3 P2).
Qed.

Lemma cp_sub: ∀ A, ∀ B, ∀ C, ∀ D, A ⊆ C → B ⊆ D → A ⨉ B ⊆ C ⨉ D.
Proof.
  intros A B C D P1 P2 r P3.
  destruct (cp_e _ _ _ P3) as [x [y [P4 [P5 P6]]]].
  apply (eq_cr (λ r, r ∈ C ⨉ D) P6).
  apply cp_i.
  + apply (P1 _ P4).
  + apply (P2 _ P5).
Qed.
(*----------------------------------------------------------------------------*)

(* Russell *)
Lemma no_universe: ~(∃ A, ∀ x, x ∈ A).
Proof.
  intros [A P1].
  pose ({x: A| x ∉ x}) as R.
  assert (R ∉ R) as P2.
  { intros P2.
    destruct (sub_e _ _ _ P2) as [_ P3].
    apply bot_e.
    apply (P3 P2). }
  assert (R ∈ R) as P3.
  { apply sub_i.
    + apply P1.
    + apply P2. }
  apply bot_e.
  apply (P2 P3).
Qed.

Lemma ex_extra: ∀ A, ∃ x, x ∉ A.
Proof.
  intros A.
  apply not_all_ex_not.
  apply (@not_ex_all_not (λ A, ∀ x, x ∈ A) no_universe).
Qed.

(* Axiom of Regularity *)
Lemma nin_self: ∀ A, A ∉ A.
Proof.
  intros A P1.
  assert (∃ x, x ∈ `{A}) as P2.
  { exists A.
    apply sing_i. }
  destruct (ax_regular `{A}) as [m P3].
  destruct (P3 P2) as [P4 P5].
  apply P5.
  exists A.
  split.
  + apply sing_i.
  + apply (eq_cl (λ x, A ∈ x) (sing_e _ _ P4)).
    apply P1.
Qed.

Lemma no_mutual_in: ∀ A, ∀ B, ~(A ∈ B ∧ B ∈ A).
Proof.
  intros A B [P1 P2].
  assert (∃ x, x ∈ `{A, B}) as P3.
  { exists A.
    apply pair_il. }
  destruct (ax_regular `{A, B}) as [m P4].
  destruct (P4 P3) as [P5 P6].
  apply P6.
  destruct (pair_e _ _ _ P5) as [P7 | P7].
  + exists B.
    split.
    - apply pair_ir.
    - apply (eq_cr (λ x, B ∈ x) P7).
      apply P2.
  + exists A.
    split.
    - apply pair_il.
    - apply (eq_cr (λ x, A ∈ x) P7).
      apply P1.
Qed.
(*----------------------------------------------------------------------------*)

