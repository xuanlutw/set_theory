Require Import Init.Init.
Require Import Relation.Relation.
Require Import Nat.Inductive.

(* Nature Number *)
(* Use k ∈ ω not nat k *)
Definition nat (n: J) := ∀ B, inductive B → n ∈ B.

Theorem omega_exists: ∃ A, ∀ n, nat n ↔ n ∈ A.
Proof.
  destruct ax_infinity as [X P1].
  exists ({n: X| ∀ B, inductive B → n ∈ B}).
  intros n.
  split.
  + intros P2.
    apply sub_i.
    - apply (P2 X P1).
    - intros B P3.
      apply (P2 B P3).
  + apply sub_e.
Qed.

Definition omega := (ex_outl omega_exists).
Notation   "'ω'" := omega.

Definition induction_step (P: J → Prop) := (∀ k, k ∈ ω → P k → P (S(k))).

Lemma omega_i: ∀ x, nat x → x ∈ ω.
Proof.
  intros x P1.
  destruct (ex_outr omega_exists x) as [P2 _].
  apply (P2 P1).
Qed.

Lemma omega_e: ∀ x, x ∈ ω → nat x.
Proof.
  intros x P1.
  destruct (ex_outr omega_exists x) as [_ P2].
  apply (P2 P1).
Qed.

Lemma omega_is_inductive: inductive ω.
Proof.
  split.
  + apply omega_i.
    intros A [P1 _].
    apply P1.
  + intros x P1.
    apply omega_i.
    intros A P2.
    pose (omega_e x P1 A P2) as P3.
    destruct P2 as [P4 P5].
    apply (P5 x P3).
Qed.

Lemma omega_min_inductive: ∀ A, inductive A → ω ⊆ A.
Proof.
  intros A P1 x P2.
  apply (omega_e x P2 A P1).
Qed.

Lemma empty_is_nat: ∅ ∈ ω.
Proof. 
  apply omega_i.
  intros x [P1 _].
  apply P1.
Qed.

Lemma suc_is_nat: ∀ k, k ∈ ω → S(k) ∈ ω.
Proof.
  intros k P1.
  destruct (omega_is_inductive) as [_ P2].
  apply (P2 _ P1).
Qed.

Lemma nat_nonempty: ω ≠ ∅.
Proof.
  apply ex_nempty.
  exists ∅.
  apply empty_is_nat.
Qed.
(*----------------------------------------------------------------------------*)

(* Induction Principle *)
Lemma inductive_subset_omega_coincident: ∀ T, T ⊆ ω → inductive T → T = ω.
Proof.
  intros T P1 P2.
  apply sub_a.
  apply (and_i P1 (omega_min_inductive T P2)).
Qed.

Lemma induction_principle: ∀ₚ P, P ∅ → induction_step P → (∀ n, n ∈ ω → P n).
Proof.
  intros P P1 P2 n P3.
  assert ({x: ω| P x} ⊆ ω) as P4.
  { intros x P5.
    destruct (sub_e _ _ _ P5) as [P6 _].
    apply P6. }
  assert (inductive {x: ω| P x}) as P5.
  { split.
    + apply (sub_i _ _ _ (empty_is_nat) P1).
    + intros x P5.
      destruct (sub_e _ _ _ P5) as [P6 P7].
      apply (sub_i _ _ _ (suc_is_nat _ P6) (P2 _ P6 P7)). }
  destruct (sub_e _ _ _ 
    (eq_cr _ (inductive_subset_omega_coincident _ P4 P5) P3)) as [_ P6].
  apply P6.
Qed.
(*----------------------------------------------------------------------------*)

(* More Natue Number Property *)
Lemma nat_is_suc: ∀ x, x ∈ ω → x ≠ ∅ → ∃ y, y ∈ ω ∧ x = S(y).
Proof.
  intros x P1 P2.
  pose (λ x, x = ∅ ∨ ∃ y, y ∈ ω ∧ x = S(y)) as P.
  assert (P ∅) as P3.
  { left.
    apply eq_r. }
  assert (induction_step P) as P4.
  { intros k P5 [P4 | P4].
    + right.
      exists ∅.
      split.
      - apply empty_is_nat. 
      - apply (eq_cr (λ x, S(x) = S(∅)) P4).
        apply eq_r.
    + right.
      exists k.
      split.
      - apply P5. 
      - apply eq_r. }
  destruct (induction_principle _ P3 P4 x P1) as [P5 | P5].
  + apply (bot_e _ (P2 P5)).
  + apply P5.
Qed.

(* 4F *)
Lemma nat_is_trans: ∀ A, A ∈ ω → trans A.
Proof.
  intros A P1.
  assert (induction_step trans) as P2.
  { intros k _ P2.
    apply trans_i1.
    apply (eq_cr (λ x, x ⊆ S(k)) (union_trans_suc _ P2)).
    apply suc_i3. }
  apply (induction_principle _ (empty_is_trans) P2 A P1).
Qed.

(* 4G *)
Lemma omega_is_trans: trans ω.
Proof. 
  assert (∅ ⊆ ω) as P1.
  { intros x P1.
    apply bot_e.
    apply (empty_i _ P1). }
  assert (induction_step (λ x, x ⊆ ω)) as P2.
  { intros k P2 P3 x P4.
    destruct (suc_e _ _ P4) as [P5 | P5].
    + apply (eq_cr (λ x, x ∈ ω) P5).
      apply P2.
    + apply (P3 _ P5). }
  apply (trans_i2 _ (induction_principle _ P1 P2)).
Qed.

Lemma nat_not_in_self: ∀ n, n ∈ ω → n ∉  n.
Proof.
  intros n P1.
  assert (∅ ∉ ∅) as P2.
  { apply empty_i. }
  assert (induction_step (λ x, x ∉ x)) as P3.
  { intros k P3 P4 P5.
    destruct (suc_e _ _ P5) as [P6 | P6].
    + apply (eq_cr (λ x, k ∉ x) P6 P4). 
      apply suc_i1.
    + apply P4.
      apply (nat_is_trans _ P3 _ _ (suc_i1 k) P6). } 
  apply (induction_principle _ P2 P3 _ P1).
Qed.

Lemma suc_unique: ∀ x, ∀ y, x ∈ ω → y ∈ ω → S(x) = S(y) → x = y.
Proof. 
  intros x y P1 P2 P3.
  destruct (suc_e _ _ (eq_cl (λ y, x ∈ y) P3 (suc_i1 x))) as [P4 | P4].
  + apply P4.
  + destruct (suc_e _ _ (eq_cr (λ x, y ∈ x) P3 (suc_i1 y))) as [P5 | P5].
    - apply (eq_s P5).
    - apply bot_e.
      apply (nat_not_in_self _ P1).
      apply (nat_is_trans _ P1 _ _ P4 P5).
Qed.

Lemma empty_in_nat: ∀ n, n ∈ ω → n ≠ ∅ → ∅ ∈ n.
Proof.
  intros n P1 P2.
  pose (λ k, k ∈ ω → k ≠ ∅ → ∅ ∈ k) as P.
  assert (P ∅) as I1.
  { intros Q1 Q2.
    apply bot_e.
    apply (Q2 (eq_r _)). }
  assert (induction_step P) as I2.
  { intros k Q1 Q2 Q3 Q4.
    destruct (LEM (k = ∅)) as [Q5 | Q5].
    + apply (eq_cr (λ x, ∅ ∈ S(x)) Q5).
      apply suc_i1.
    + pose (nat_is_trans _ (suc_is_nat _ Q1)) as Q6.
      apply (Q6 _ _ (Q2 Q1 Q5) (suc_i1 k)). }
  apply (induction_principle _ I1 I2 _ P1 P1 P2).
Qed.

(*----------------------------------------------------------------------------*)
