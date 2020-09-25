Require Import Init.Init.
Require Import Relation.Relation_.
Require Import Relation.Function.

(* Equivalence Relation *)
Definition eqrel (R A:J) := 
  (r_over R A) ∧ (r_refl R A) ∧ (r_sym R A) ∧ (r_trans R A).

Lemma eqrel_i: ∀ R, rel R → r_sym R (fld(R)) → r_trans R (fld(R))
  → eqrel R (fld(R)).
Proof.
  intros R P1 P2 P3.
  repeat split.
  + apply (r_over_fld _ P1).
  + intros x P4.
    destruct (fld_e _ _ P4) as [P5 | P5].
    * destruct (dom_e _ _ P5) as [y P6].
      pose (fld_ir _ _ (ran_i _ _ _ P6)) as P7.
      apply (P3 _ _ _ P4 P7 P4 P6 (P2 _ _ P4 P7 P6)).
    * destruct (ran_e _ _ P5) as [y P6].
      pose (fld_id _ _ (dom_i _ _ _ P6)) as P7.
      apply (P3 _ _ _ P4 P7 P4 (P2 _ _ P7 P4 P6) P6).
  + apply P2.
  + apply P3.
Qed.

Lemma eqrel_e1: ∀ x, ∀ y, ∀ R, ∀ A, eqrel R A → ⟨x, y⟩ ∈ R → x ∈ A.
Proof.
  intros x y R A [P1 _] P2.
  destruct (cp_e2 _ _ _ _ (P1 _ P2)) as [P3 _].
  apply P3.
Qed.

Lemma eqrel_e2: ∀ x, ∀ y, ∀ R, ∀ A, eqrel R A → ⟨x, y⟩ ∈ R → y ∈ A.
Proof.
  intros x y R A [P1 _] P2.
  destruct (cp_e2 _ _ _ _ (P1 _ P2)) as [_ P3].
  apply P3.
Qed.

Lemma eqrel_s: ∀ R, ∀ A, ∀ x, ∀ y, eqrel R A → ⟨x, y⟩ ∈ R → ⟨y, x⟩ ∈ R.
Proof.
  intros R A x y P1 P2.
  pose (eqrel_e1 _ _ _ _ P1 P2) as P3.
  pose (eqrel_e2 _ _ _ _ P1 P2) as P4.
  assert (r_sym R A) as P5.
  { apply P1. }
  apply (P5 _ _ P3 P4 P2).
Qed.

Lemma eqrel_r: ∀ R, ∀ A, ∀ x, eqrel R A → x ∈ A → ⟨x, x⟩ ∈ R.
Proof.
  intros R A x [_ [P1 _]] P2.
  apply (P1 _ P2).
Qed.

Lemma eqrel_t: ∀ R, ∀ A, ∀ x, ∀ y, ∀ z, eqrel R A → ⟨x, y⟩ ∈ R → ⟨y, z⟩ ∈ R
  → ⟨x, z⟩ ∈ R.
Proof.
  intros R A x y z P1 P2 P3.
  assert (r_trans R A) as P4.
  { apply P1. }
  apply (P4 _ y _).
  + apply (eqrel_e1 _ _ _ _ P1 P2).
  + apply (eqrel_e1 _ _ _ _ P1 P3).
  + apply (eqrel_e2 _ _ _ _ P1 P3).
  + apply P2.
  + apply P3.
Qed.
(*----------------------------------------------------------------------------*)

(* Equivalence Class *)
Lemma equiv_class_ex: ∀ R, ∀ A, ∀ x, ∃ C, eqrel R A → x ∈ A → 
  ∀ y, ⟨x, y⟩ ∈ R ↔ y ∈ C.
Proof.
  intros R A x.
  exists ({y: A| ⟨x, y⟩ ∈ R}).
  intros P1 P2 y.
  split.
  + intros P3.
    apply sub_i.
    - apply (eqrel_e2 _ _ _ _ P1 P3).
    - apply P3.
  + intros P3.
    destruct (sub_e _ _ _ P3) as [P4 P5].
    apply P5.
Qed.

(*Definition equiv_class (R A x: J) := {y: A| x ∈ A ∧ eqrel R A ∧ ⟨x, y⟩ ∈ R}.*)
Definition equiv_class (R A x: J) := (ex_outl (equiv_class_ex R A x)).
Notation "[ x ]( R , A )"         := (equiv_class R A x).

Lemma equiv_class_i1: ∀ R, ∀ A, ∀ x, ∀ y, eqrel R A → ⟨x, y⟩ ∈ R → y ∈ [x](R, A).
Proof.
  intros R A x y P1 P2.
  destruct (ex_outr (equiv_class_ex R A x) P1 (eqrel_e1 _ _ _ _ P1 P2) y)
    as [P3 _].
  apply (P3 P2).
Qed.

Lemma equiv_class_i2: ∀ R, ∀ A, ∀ x, ∀ y, eqrel R A → ⟨x, y⟩ ∈ R → x ∈ [y](R, A).
Proof.
  intros R A x y P1 P2.
  apply (equiv_class_i1 _ _ _ _ P1 (eqrel_s _ _ _ _ P1 P2)).
Qed.

Lemma equiv_class_r: ∀ R, ∀ A, ∀ x, eqrel R A → x ∈ A → x ∈ [x](R, A).
Proof.
  intros R A x P1 P2.
  apply equiv_class_i1.
  + apply P1.
  + apply (eqrel_r _ _ _ P1 P2).
Qed.

Lemma equiv_class_e1: ∀ R, ∀ A, ∀ x, ∀ y, eqrel R A → x ∈ A → y ∈ [x](R, A)
  → ⟨x, y⟩ ∈ R.
Proof.
  intros R A x y P1 P2 P3.
  destruct (ex_outr (equiv_class_ex R A x) P1 P2 y) as [_ P4].
  apply (P4 P3).
Qed.

Lemma equiv_class_e2: ∀ R, ∀ A, ∀ x, ∀ y, eqrel R A → x ∈ A → y ∈ [x](R, A)
  → ⟨y, x⟩ ∈ R.
Proof.
  intros R A x y P1 P2 P3.
  pose (equiv_class_e1 _ _ _ _ P1 P2 P3) as P4.
  apply (eqrel_s _ _ _ _ P1 P4).
Qed.

Lemma equiv_class_e3: ∀ R, ∀ A, ∀ x, ∀ y, eqrel R A → x ∈ A → y ∈ [x](R, A)
  → x ∈ A.
Proof.
  intros R A x y P1 P2 P3.
  pose (equiv_class_e1 _ _ _ _ P1 P2 P3) as P4.
  apply (eqrel_e1 _ _ _ _ P1 P4).
Qed.

Lemma equiv_class_e4: ∀ R, ∀ A, ∀ x, ∀ y, eqrel R A → x ∈ A → y ∈ [x](R, A)
  → y ∈ A.
Proof.
  intros R A x y P1 P2 P3.
  pose (equiv_class_e1 _ _ _ _ P1 P2 P3) as P4.
  apply (eqrel_e2 _ _ _ _ P1 P4).
Qed.

Lemma equiv_class_s: ∀ R, ∀ A, ∀ x, ∀ y, eqrel R A → x ∈ A → y ∈ [x](R, A)
  → x ∈ [y](R, A).
Proof.
  intros R A x y P1 P2 P3.
  apply equiv_class_i2.
  + apply P1.
  + apply (equiv_class_e1 _ _ _ _ P1 P2 P3).
Qed.

Lemma equiv_class_eq_i: ∀ R, ∀ A, ∀ x, ∀ y, eqrel R A → ⟨x, y⟩ ∈ R
  → [x](R, A) = [y](R, A).
Proof.
  intros R A x y P1 P2.
  apply sub_a.
  split.
  - intros r P3.
    apply (equiv_class_i2 _ _ _ _ P1).
    apply (eqrel_t _ _ _ x _ P1).
    * apply (equiv_class_e2 _ _ _ _ P1 (eqrel_e1 _ _ _ _ P1 P2) P3).
    * apply P2.
  - intros r P3.
    apply (equiv_class_i1 _ _ _ _ P1).
    apply (eqrel_t _ _ _ y _ P1).
    * apply P2.
    * apply (equiv_class_e1 _ _ _ _ P1 (eqrel_e2 _ _ _ _ P1 P2) P3).
Qed.

Lemma equiv_class_eq_e: ∀ R, ∀ A, ∀ x, ∀ y, eqrel R A → x ∈ A → y ∈ A
  → [x](R, A) = [y](R, A) → ⟨x, y⟩ ∈ R.
Proof.
  intros R A x y P1 P2 P3 P4.
  apply (equiv_class_e1 _ _ _ _ P1 P2).
  apply (eq_cr (λ x, y ∈ x) P4).
  apply (equiv_class_r _ _ _ P1 P3).
Qed.

Lemma equiv_class_sub: ∀ R, ∀ A, ∀ x, eqrel R A → x ∈ A → [x](R, A) ⊆ A.
Proof.
  intros R A x P1 P2 r P3.
  apply (equiv_class_e4 _ _ _ _ P1 P2 P3).
Qed.
(*----------------------------------------------------------------------------*)

(* Partition *)
Definition is_part (A B: J) := (∀ x, ∀ y, x ∈ A → y ∈ A → x ≠ y → x ∩ y = ∅) ∧ ∪(A) = B.

Lemma equiv_part_ex: ∀ R, ∀ A, ∃ P, eqrel R A
  → is_part P A ∧ (∀ p, p ∈ A → [p](R, A) ∈ P) 
  ∧ (∀ p, p ∈ P → ∃ x, x ∈ A ∧ p = [x](R, A)).
Proof.
  intros R A.
  exists ({p: 𝒫(A)| ∃ x, x ∈ A ∧ p = [x](R, A)}).
  intros P1.
  repeat split.
  + intros p1 p2 Q1 Q2.
    apply contraposition2.
    intros Q3.
    destruct (nempty_ex _ Q3) as [a Q4].
    destruct (inter2_e _ _ _ Q4) as [Q5 Q6].
    destruct (sub_e _ _ _ Q1) as [_ [a1 [Q7 Q8]]].
    destruct (sub_e _ _ _ Q2) as [_ [a2 [Q9 Q10]]].
    apply (eq_cr (λ x, x = _) Q8).
    apply (eq_cr (λ x, _ = x) Q10).
    apply (equiv_class_eq_i _ _ _ _ P1).
    apply (eqrel_t _ _ _ a _ P1).
    - apply (equiv_class_e1 _ _ _ _ P1 Q7 (eq_cl (λ x, a ∈ x) Q8 Q5)).
    - apply (equiv_class_e2 _ _ _ _ P1 Q9 (eq_cl (λ x, a ∈ x) Q10 Q6)).
  + apply sub_a.
    split.
    - intros x Q1.
      destruct (union_e _ _ Q1) as [p [Q2 Q3]].
      destruct (sub_e _ _ _ Q2) as [Q4 _].
      pose (power_e _ _ Q4) as Q5.
      apply (Q5 _ Q3).
    - intros x Q1.
      apply union_i.
      exists ([x](R, A)).
      split.
      * apply sub_i.
        ++apply power_i.
          apply (equiv_class_sub _ _ _ P1 Q1).
        ++exists x.
          apply (and_i Q1 (eq_r _)).
      * apply (equiv_class_r _ _ _ P1 Q1).
  + intros p Q1.
    apply sub_i.
    - apply power_i.
      apply (equiv_class_sub _ _ _ P1 Q1).
    - exists p.
      apply (and_i Q1 (eq_r _)).
  + intros x Q1.
    destruct (sub_e _ _ _ Q1) as [Q2 [a [Q3 Q4]]].
    exists a.
    split.
    - apply Q3.
    - apply Q4.
Qed.

Definition equiv_part (R A: J) := (ex_outl (equiv_part_ex R A)).
Notation "[ A ]\ R"            := (equiv_part R A).

Lemma equiv_part_e1: ∀ R, ∀ A, ∀ a, eqrel R A → a ∈ [A]\R
  → ∃ x, x ∈ A ∧ a = [x](R, A).
Proof.
  intros R A x P1 P2.
  destruct (ex_outr (equiv_part_ex R A) P1) as [_ [_ P5]].
  apply (P5 _ P2).
Qed.

Lemma equiv_part_e2: ∀ R, ∀ A, ∀ a, ∀ x, eqrel R A → a ∈ x → x ∈ [A]\R → a ∈ A.
Proof.
  intros R A a x P1 P2 P3.
  destruct (ex_outr (equiv_part_ex R A) P1) as [_ [_ P4]].
  destruct (P4 _ P3) as [a' [P5 P6]].
  apply (equiv_class_e4 _ _ _ _ P1 P5 (eq_cl (λ x, a ∈ x) P6 P2)).
Qed.

Lemma equiv_part_i: ∀ R, ∀ A, ∀ x, eqrel R A → x ∈ A → [x](R, A) ∈ [A]\R.
Proof.
  intros R A x P1 P2.
  destruct (ex_outr (equiv_part_ex R A) P1) as [_ [P4 _]].
  apply (P4 _ P2).
Qed.

Lemma equiv_part_is_part: ∀ R, ∀ A, eqrel R A → is_part ([A]\R) A.
Proof.
  intros R A P1.
  destruct (ex_outr (equiv_part_ex R A) P1) as [P2 _].
  apply P2.
Qed.
(*----------------------------------------------------------------------------*)
