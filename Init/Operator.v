Require Export Init.Notations.
Require Import Init.Logic.
Require Import Init.Classical.
Require Import Init.Axiom.

Lemma AA: ∀ s, ∀ k, s ∈ k → s ∈ k.
Proof.
  intros s k P1.
  apply P1.
Qed.

(* Operators *)
Definition subset (A B: J) := (∀ x, x ∈ A → x ∈ B).
Notation   "x ⊆ y"         := (subset x y).

Definition proper_subset (A B: J) := ((subset A B) ∧ A ≠ B).
Notation   "x ⊂ y"                := (proper_subset x y).

Definition empty_c := (ex_outl ax_empty).
Notation   "∅"     := (empty_c).

Definition pair_c (A B: J) := (ex_outl (ax_pair A B)).
Notation   "J{ x , y }"    := (pair_c x y).

Definition singleton (A: J) := (pair_c A A).
Notation   "J{ x }"         := (singleton x).

Definition union_c (A: J) := (ex_outl (ax_union A)).
Notation   "∪ A "         := (union_c A).

Definition union2_c (A B: J) := (ex_outl (thm_union2 A B)).
Notation   "A ∪ B"           := (union2_c A B).

Definition power_c (A: J) := (ex_outl (ax_power A)).
Notation   "𝒫( x )"       := (power_c x).

Definition sub_c (P: J → Prop) (x: J) := (ex_outl (ax_subset P x)).
Notation   "{ x : A | P }"            := (sub_c (λ x, P) A).

Definition inter2_c (A B: J) := ({x: A| x ∈ B}).
Notation   "A ∩ B"           := (inter2_c A B).

Definition complement (A B : J) := ({x: A| x ∉ B}).
Notation   "A \ B"              := (complement A B).

Definition opair (A B: J) := J{J{A}, J{A, B}}.
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
    destruct (not_or_and (not_ex_all_not x _ P1 x)) as [P3 _].
    destruct (not_and_or P3) as [P4 | P4].
    - apply (bot_e _ (P4 P2)).
    - apply (nn_e P4). 
  + intros x P2.
    destruct (not_or_and (not_ex_all_not x _ P1 x)) as [_ P3].
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

Lemma sub_e2: ∀ A, ∀ B, A ⊆ B → A ⊂ B ∨ A = B.
Proof.
  intros A B P1.
  destruct (LEM (A = B)) as [P2 | P2].
  + right.
    apply P2.
  + left.
    apply (psub_i _ _ P1 P2).
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
  apply (not_ex_all_not A).
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
(*----------------------------------------------------------------------------*)

(* Pair and Singleton *)
Lemma pair_e: ∀ A, ∀ B, ∀ x, x ∈ J{A, B} → x = A ∨ x = B.
Proof.
  intros A B x P1.
  destruct (ex_outr (ax_pair A B) x) as [P2 _].
  apply (P2 P1).
Qed.

Lemma pair_il: ∀ A, ∀ B, A ∈ J{A, B}.
Proof.
  intros A B.
  destruct (ex_outr (ax_pair A B) A) as [_ P2].
  apply P2.
  left.
  apply eq_r.
Qed.

Lemma pair_ir: ∀ A, ∀ B, B ∈ J{A, B}.
Proof.
  intros A B.
  destruct (ex_outr (ax_pair A B) B) as [_ P2].
  apply P2.
  right.
  apply eq_r.
Qed.

Lemma pair_s: ∀ A, ∀ B, J{A, B} = J{B, A}.
Proof.
  intros A B.
  apply sub_a.
  split.
  + intros x P1.
    destruct (pair_e _ _ _ P1) as [P2 | P2].
    - apply (eq_cr (λ y, y ∈ J{B, A}) P2).
      apply pair_ir.
    - apply (eq_cr (λ y, y ∈ J{B, A}) P2).
      apply pair_il.
  + intros x P1.
    destruct (pair_e _ _ _ P1) as [P2 | P2].
    - apply (eq_cr (λ y, y ∈ J{A, B}) P2).
      apply pair_ir.
    - apply (eq_cr (λ y, y ∈ J{A, B}) P2).
      apply pair_il.
Qed.

Lemma pair_eql: ∀ A, ∀ B, ∀ C, ∀ D, J{A, B} = J{C, D} → A = C ∨ A = D.
Proof.
  intros A B C D P1.
  pose (pair_il A B) as P2.
  pose (eq_cl _ P1 P2) as P3.
  apply (pair_e _ _ _ P3). 
Qed.

Lemma pair_eqr: ∀ A, ∀ B, ∀ C, ∀ D, J{A, B} = J{C, D} → B = C ∨ B = D.
Proof.
  intros A B C D P1.
  pose (pair_ir A B) as P2.
  pose (eq_cl _ P1 P2) as P3.
  apply (pair_e _ _ _ P3). 
Qed.

Lemma sing_i: ∀ A, A ∈ J{A}.
Proof.
  intros A.
  destruct (ex_outr (ax_pair A A) A) as [_ P1].
  apply P1.
  left.
  apply eq_r.
Qed.

Lemma sing_i2: ∀ A, ∀ B, A = B → A ∈ J{B}.
Proof.
  intros A B P1.
  apply (eq_cl (λ x, A ∈ J{x}) P1).
  apply sing_i.
Qed.

Lemma sing_e: ∀ A, ∀ B, B ∈ J{A} → A = B.
Proof.
  intros A B P1.
  destruct (ex_outr (ax_pair A A) B) as [P2 _].
  destruct (P2 P1) as [P3 | P3].
  + apply eq_s.
    apply P3.
  + apply eq_s.
    apply P3.
Qed.

Lemma nsing_e: ∀ A, ∀ B, A ≠ B → B ∉ J{A}.
Proof.
  intros A B.
  apply contraposition1.
  apply sing_e.
Qed.

Lemma sing_pair_eq1: ∀ A, ∀ B, ∀ C, J{A} = J{B, C} → A = B.
Proof.
  intros A B C P1.
  apply sing_e.
  apply (eq_cr _ P1).
  apply pair_il.
Qed.

Lemma sing_pair_eq2: ∀ A, ∀ B, ∀ C, J{A} = J{B, C} → A = C.
Proof.
  intros A B C P1.
  pose (eq_t P1 (pair_s B C)) as P2.
  apply (sing_pair_eq1 _ _ _ P2).
Qed.

Lemma sing_pair_eq3: ∀ A, ∀ B, ∀ C, J{A} = J{B, C} → B = C.
Proof.
  intros A B C P1.
  pose (eq_s (sing_pair_eq1 _ _ _ P1)) as P2.
  pose (sing_pair_eq2 _ _ _ P1) as P3.
  apply (eq_t P2 P3).
Qed.

Lemma sing_eq: ∀ A, ∀ B, J{A} = J{B} → A = B.
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
  destruct (ex_outr (thm_union2 A B) x) as [P2 _].
  apply (P2 P1).
Qed.

Lemma union2_il: ∀ A, ∀ B, ∀ x, x ∈ A → x ∈ A ∪ B.
Proof.
  intros A B x P1.
  destruct (ex_outr (thm_union2 A B) x) as [_ P2].
  apply P2.
  left.
  apply P1.
Qed.

Lemma union2_ir: ∀ A, ∀ B, ∀ x, x ∈ B → x ∈ A ∪ B.
Proof.
  intros A B x P1.
  destruct (ex_outr (thm_union2 A B) x) as [_ P2].
  apply P2.
  right.
  apply P1.
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
(*----------------------------------------------------------------------------*)

(* Order Pairs *)
Lemma opair_e: ∀ A, ∀ B, ∀ x, x ∈ ⟨A, B⟩ → x = J{A} ∨ x = J{A, B}.
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
    split.
    - apply P1.
    - split.
      * apply P2.
      * apply eq_r.
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
(*----------------------------------------------------------------------------*)
