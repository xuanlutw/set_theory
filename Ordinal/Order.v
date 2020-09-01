Require Import Init.Init.
Require Import Relation.Relation.
Require Import Nat.Nat.

Notation " x <[ R ] y" := (⟨x, y⟩ ∈ R).
Notation " x ≮[ R ] y" := (⟨x, y⟩ ∉ R).
Notation " x ≤[ R ] y" := (⟨x, y⟩ ∈ R ∨ x = y).
Notation " x ≰[ R ] y" := (~(x ≤[R] y)).

Definition tricho (R A: J) := ∀ x, ∀ y, x ∈ A → y ∈ A 
  → (( x <[R] y ∧ x ≠ y ∧ ~y <[R] x) ∨ 
     (~x <[R] y ∧ x = y ∧ ~y <[R] x) ∨ 
     (~x <[R] y ∧ x ≠ y ∧  y <[R] x)).

Definition tricho_weak (R A: J) := ∀ x, ∀ y, x ∈ A → y ∈ A 
  → ( x <[R] y ∨ x = y ∨ y <[R] x).

Definition po (R A: J) := r_trans R A ∧ r_irrefl R A.

Definition lo (R A: J) := r_trans R A ∧ tricho R A.

Definition least       (R A s: J) := ∀ x, x ∈ A → s ≤[R] x.
Definition least_bound (R A: J)   := ∃ x, x ∈ A ∧ least R A x. 
Definition least_prop  (R A: J)   := ∀ S, S ⊆ A → S ≠ ∅ → least_bound R S.

Definition wo (R A: J) := lo R A ∧ least_prop R A.

(* Trichotomy *)
Lemma tricho_to_weak: ∀ R, ∀ A, tricho R A → tricho_weak R A.
Proof.
  intros R A P1.
  intros x y P2 P3.
  destruct (P1 _ _ P2 P3) as [P4 | [P4 | P4]].
  + destruct P4 as [P4 _].
    left.
    apply P4.
  + destruct P4 as [_ [P4 _]].
    right. left.
    apply P4.
  + destruct P4 as [_ [_ P4]].
    right. right.
    apply P4.
Qed.

(* Partial Order *)
Lemma po_trans: ∀ R, ∀ A, po R A → r_trans R A.
Proof.
  intros R A P1.
  destruct P1 as [P1 _].
  apply P1.
Qed.

Lemma po_irrefl: ∀ R, ∀ A, po R A → r_irrefl R A.
Proof.
  intros R A P1.
  destruct P1 as [_ P1].
  apply P1.
Qed.

Lemma po_weak_at_most_1: ∀ R, ∀ A, ∀ x, ∀ y, po R A → x ∈ A → y ∈ A 
  → ~(x <[R] y ∧ x = y).
Proof.
  intros R A x y P1 P2 P3 [P4 P5].
  apply (po_irrefl _ _ P1 _ P3).
  apply (eq_cl (λ x, x <[R] y) P5).
  apply P4.
Qed.

Lemma po_weak_at_most_2: ∀ R, ∀ A, ∀ x, ∀ y, po R A → x ∈ A → y ∈ A
  → ~(y <[R] x ∧ x = y).
Proof.
  intros R A x y P1 P2 P3 [P4 P5].
  apply (po_irrefl _ _ P1 _ P3).
  apply (eq_cl (λ x, y <[R] x) P5).
  apply P4.
Qed.

Lemma po_weak_at_most_3: ∀ R, ∀ A, ∀ x, ∀ y, po R A → x ∈ A → y ∈ A
  → ~(x <[R] y ∧ y <[R] x).
Proof.
  intros R A x y P1 P2 P3 [P4 P5].
  apply (po_irrefl _ _ P1 _ P2).
  apply (po_trans _ _ P1 _ _ _ P2 P3 P2 P4 P5).
Qed.

Lemma po_sandwich: ∀ R, ∀ A, ∀ x, ∀ y, po R A → x ∈ A → y ∈ A → x ≤[R] y 
  → y ≤[R] x → x = y.
Proof.
  intros R A x y P1 P2 P3 [P4 | P4] [P5 | P5].
  + apply bot_e.
    apply (po_irrefl _ _ P1 _ P2).
    apply (po_trans _ _ P1 _ _ _ P2 P3 P2 P4 P5).
  + apply (eq_s P5).
  + apply P4.
  + apply P4.
Qed.
(*----------------------------------------------------------------------------*)

(* Linear Order *)
Lemma lo_is_po: ∀ R, ∀ A, lo R A → po R A.
Proof.
  intros R A [P1 P2].
  split.
  + apply P1.
  + intros x P3.
    destruct (P2 _ _ P3 P3) as [P4 | [P4 | P4]].
    - destruct P4 as [_ [_ P4]].
      apply P4.
    - destruct P4 as [_ [_ P4]].
      apply P4.
    - destruct P4 as [P4 _].
      apply P4.
Qed.

Lemma lo_irrefl: ∀ R, ∀ A, lo R A → r_irrefl R A.
Proof.
  intros R A P1.
  apply (po_irrefl _ _ (lo_is_po _ _ P1)).
Qed.

Lemma lo_trans: ∀ R, ∀ A, lo R A → r_trans R A.
  intros R A P1.
  apply (po_trans _ _ (lo_is_po _ _ P1)).
Qed.

Lemma lo_tricho: ∀ R, ∀ A, lo R A → tricho R A.
Proof.
  intros R A P1.
  destruct P1 as [_ P1].
  apply P1.
Qed.

Lemma lo_tricho_weak: ∀ R, ∀ A, lo R A → tricho_weak R A.
Proof.
  intros R A P1.
  apply (tricho_to_weak _ _ (lo_tricho _ _ P1)).
Qed.

Lemma lo_neq_e: ∀ R, ∀ A, ∀ x, ∀ y, lo R A → x ∈ A → y ∈ A → x ≠ y 
  → (x <[R] y) ∨ (y <[R] x).
Proof.
  intros R A x y P1 P2 P3 P4.
  destruct (lo_tricho _ _ P1 _ _ P2 P3) as [P5 | [P5 | P5]].
  + destruct P5 as [P5 [_ P6]].
    left.
    apply (and_i P5 P6).
  + destruct P5 as [_ [P5 _]].
    apply bot_e.
    apply (P4 P5).
  + destruct P5 as [P5 [_ P6]].
    right.
    apply (and_i P5 P6).
Qed.

Lemma lo_neq_i: ∀ R, ∀ A, ∀ x, ∀ y, lo R A → x ∈ A → y ∈ A → x <[R] y → x ≠ y.
Proof.
  intros R A x y P1 P2 P3 P4.
  destruct (lo_tricho _ _ P1 _ _ P2 P3) as [P5 | [P5 | P5]].
  + destruct P5 as [_ [P5 _]].
    apply P5.
  + destruct P5 as [P5 _].
    apply bot_e.
    apply (P5 P4).
  + destruct P5 as [_ [P5 _]].
    apply P5.
Qed.

Lemma lo_nl_e: ∀ R, ∀ A, ∀ x, ∀ y, lo R A → x ∈ A → y ∈ A → x ≮[R] y 
  → y ≤[R] x.
Proof.
  intros R A x y P1 P2 P3 P4.
  destruct (lo_tricho _ _ P1 _ _ P2 P3) as [P5 | [P5 | P5]].
  + destruct P5 as [P5 _].
    apply bot_e.
    apply (P4 P5).
  + destruct P5 as [_ [P5 _]].
    right.
    apply (eq_s P5).
  + destruct P5 as [_ [_ P5]].
    left.
    apply P5.
Qed.

Lemma lo_nl_i: ∀ R, ∀ A, ∀ x, ∀ y, lo R A → x ∈ A → y ∈ A → x ≤[R] y 
  → y ≮[R] x.
Proof.
  intros R A x y P1 P2 P3 [P4 | P4].
  + destruct (lo_tricho _ _ P1 _ _ P3 P2) as [P5 | [P5 | P5]].
    - destruct P5 as [_ [_ P5]].
      apply bot_e.
      apply (P5 P4).
    - destruct P5 as [P5 _].
      apply P5.
    - destruct P5 as [P5 _].
      apply P5.
  + destruct (lo_tricho _ _ P1 _ _ P3 P2) as [P5 | [P5 | P5]].
    - destruct P5 as [_ [P5 _]].
      apply bot_e.
      apply (P5 (eq_s P4)).
    - destruct P5 as [P5 _].
      apply P5.
    - destruct P5 as [P5 _].
      apply P5.
Qed.

Lemma lo_nle_e: ∀ R, ∀ A, ∀ x, ∀ y, lo R A → x ∈ A → y ∈ A → x ≰[R] y 
  → y <[R] x.
Proof.
  intros R A x y P1 P2 P3 P4.
  destruct (not_or_and P4) as [P5 P6].
  destruct (lo_tricho _ _ P1 _ _ P2 P3) as [P7 | [P7 | P7]].
  + destruct P7 as [P7 _].
    apply bot_e.
    apply (P5 P7).
  + destruct P7 as [_ [P7 _]].
    apply bot_e.
    apply (P6 P7).
  + destruct P7 as [_ [_ P7]].
    apply P7.
Qed.

Lemma lo_nle_i: ∀ R, ∀ A, ∀ x, ∀ y, lo R A → x ∈ A → y ∈ A → x <[R] y 
  → y ≰[R] x.
Proof.
  intros R A x y P1 P2 P3 P4.
  apply and_not_or.
  split.
  + destruct (lo_tricho _ _ P1 _ _ P3 P2) as [P5 | [P5 | P5]].
    - destruct P5 as [_ [_ P5]].
      apply bot_e.
      apply (P5 P4).
    - destruct P5 as [_ [_ P5]].
      apply bot_e.
      apply (P5 P4).
    - destruct P5 as [P5 _].
      apply P5.
  + destruct (lo_tricho _ _ P1 _ _ P3 P2) as [P5 | [P5 | P5]].
    - destruct P5 as [_ [P5 _]].
      apply P5.
    - destruct P5 as [_ [_ P5]].
      apply bot_e.
      apply (P5 P4).
    - destruct P5 as [_ [P5 _]].
      apply P5.
Qed.
(*----------------------------------------------------------------------------*)

(* Well Order *)
Lemma wo_least_prop: ∀ R, ∀ A, wo R A → least_prop R A.
Proof.
  intros R A [_ P1].
  apply P1.
Qed.

Lemma wo_is_lo: ∀ R, ∀ A, wo R A → lo R A.
Proof.
  intros R A [P1 _].
  apply P1.
Qed.

Lemma wo_trans: ∀ R, ∀ A, wo R A → r_trans R A.
  intros R A P1.
  apply (lo_trans _ _ (wo_is_lo _ _ P1)).
Qed.

Lemma wo_tricho: ∀ R, ∀ A, wo R A → tricho R A.
Proof.
  intros R A P1.
  apply lo_tricho.
  apply (wo_is_lo _ _ P1).
Qed.

Lemma wo_tricho_weak: ∀ R, ∀ A, wo R A → tricho_weak R A.
Proof.
  intros R A P1.
  apply lo_tricho_weak.
  apply (wo_is_lo _ _ P1).
Qed.

Lemma wo_neq_e: ∀ R, ∀ A, ∀ x, ∀ y, wo R A → x ∈ A → y ∈ A → x ≠ y 
  → (x <[R] y) ∨ (y <[R] x).
Proof.
  intros R A x y P1.
  apply lo_neq_e.
  apply (wo_is_lo _ _ P1).
Qed.

Lemma wo_neq_i: ∀ R, ∀ A, ∀ x, ∀ y, wo R A → x ∈ A → y ∈ A → x <[R] y
  → x ≠ y.
Proof.
  intros R A x y P1.
  apply lo_neq_i.
  apply (wo_is_lo _ _ P1).
Qed.

Lemma wo_nl_e: ∀ R, ∀ A, ∀ x, ∀ y, wo R A → x ∈ A → y ∈ A → x ≮[R] y
  → y ≤[R] x.
Proof.
  intros R A x y P1.
  apply lo_nl_e. 
  apply (wo_is_lo _ _ P1).
Qed.

Lemma wo_nl_i: ∀ R, ∀ A, ∀ x, ∀ y, wo R A → x ∈ A → y ∈ A → x ≤[R] y 
  → y ≮[R] x.
Proof.
  intros R A x y P1.
  apply lo_nl_i.
  apply (wo_is_lo _ _ P1).
Qed.

Lemma wo_nle_e: ∀ R, ∀ A, ∀ x, ∀ y, wo R A → x ∈ A → y ∈ A → x ≰[R] y
  → y <[R] x.
Proof.
  intros R A x y P1.
  apply lo_nle_e. 
  apply (wo_is_lo _ _ P1).
Qed.

Lemma wo_nle_i: ∀ R, ∀ A, ∀ x, ∀ y, wo R A → x ∈ A → y ∈ A → x <[R] y
  → y ≰[R] x.
Proof.
  intros R A x y P1.
  apply lo_nle_i.
  apply (wo_is_lo _ _ P1).
Qed.

Lemma no_descend: ∀ R, ∀ A, ∀ f, wo R A → fnm f ω A → 
  ~(∀ n, n ∈ ω → f[S(n)] <[R] f[n]).
Proof.
  intros R A f P1 [P2 [P3 P4]] P5.
  assert (least_bound R (ran(f))) as P6.
  { apply (wo_least_prop _ _ P1).
    + apply P4.
    + apply ex_nempty.
      exists (f[∅]).
      apply (fval_ran _ _ P2).
      apply (eq_cr (λ x, ∅ ∈ x) P3).
      apply empty_is_nat. }
  assert (~(least_bound R (ran(f)))) as P7.
  { intros _.
    destruct P6 as [y [P7 P8]].
    destruct (ran_e _ _ P7) as [x P9].
    pose (eq_cl (λ s, x ∈ s) P3 (dom_i2 _ _ _ P9)) as P10.
    pose (fval_ran _ _ P2 (eq_cr (λ s, S(x) ∈ s) P3 (suc_is_nat _ P10))) as P11.
    apply (wo_nle_i _ _ (f[S(x)]) (f[x]) P1).
    + apply P4.
      apply P11.
    + apply P4.
      apply (fval_ran _ _ P2).
      apply (eq_cr (λ s, x ∈ s) P3).
      apply P10.
    + apply (P5 _ P10).
    + apply (eq_cl (λ s, s ≤[R] f[S(x)]) (fval_i _ _ _ P2 P9)).
      apply P8.
      apply P11. }
  apply bot_e.
  apply (P7 P6).
Qed.
(* Skip reverse *)

Lemma wo_prop_least: ∀ₚ P, ∀ R, ∀ A, ∀ x0, wo R A → x0 ∈ A → P x0
  → ∃ x, x ∈ A ∧ P x ∧ (∀ y, y ∈ A → P y → x ≤[R] y).
Proof.
  intros P R A x0 P1 P2 P3.
  pose ({x: A| P x}) as X.
  assert (X ≠ ∅) as P4.
  { apply ex_nempty.
    exists x0.
    apply sub_i.
    + apply P2.
    + apply P3. }
  destruct (wo_least_prop _ _ P1 X (sub_e1 _ _) P4) as [x [P5 P6]].
  destruct (sub_e _ _ _ P5) as [P7 P8].
  exists x.
  repeat split.
  + apply P7.
  + apply P8.
  + intros y P9 P10.
    apply P6.
    apply (sub_i _ _ _ P9 P10).
Qed.
(*----------------------------------------------------------------------------*)

(* Subset *)
Lemma sub_r_irrefl: ∀ R, ∀ A, ∀ B, r_irrefl R A → B ⊆ A → r_irrefl R B.
Proof.
  intros R A B P1 P2 x P3.
  apply (P1 _ (P2 _ P3)).
Qed.

Lemma sub_r_trans: ∀ R, ∀ A, ∀ B, r_trans R A → B ⊆ A → r_trans R B.
Proof.
  intros R A B P1 P2 x y z P3 P4 P5.
  apply (P1 _ _ _ (P2 _ P3) (P2 _ P4) (P2 _ P5)).
Qed.

Lemma sub_tricho: ∀ R, ∀ A, ∀ B, tricho R A → B ⊆ A → tricho R B.
Proof.
  intros R A B P1 P2 x y P3 P4.
  apply (P1 _ _ (P2 _ P3) (P2 _ P4)).
Qed.

Lemma sub_least_prop: ∀ R, ∀ A, ∀ B, least_prop R A → B ⊆ A → least_prop R B.
Proof.
  intros R A B P1 P2 x P3 P4.
  apply (P1 _ (sub_t _ _ _ P3 P2) P4).
Qed.
  
Lemma sub_po: ∀ R, ∀ A, ∀ B, po R A → B ⊆ A → po R B.
Proof.
  intros R A B [P1 P2] P3.
  split.
  + apply (sub_r_trans _ _ _ P1 P3).
  + apply (sub_r_irrefl _ _ _ P2 P3).
Qed.

Lemma sub_lo: ∀ R, ∀ A, ∀ B, lo R A → B ⊆ A → lo R B.
Proof.
  intros R A B [P1 P2] P3.
  split.
  + apply (sub_r_trans _ _ _ P1 P3).
  + apply (sub_tricho _ _ _ P2 P3).
Qed.

Lemma sub_wo: ∀ R, ∀ A, ∀ B, wo R A → B ⊆ A → wo R B.
Proof.
  intros R A B [P1 P2] P3.
  split.
  + apply (sub_lo _ _ _ P1 P3).
  + apply (sub_least_prop _ _ _ P2 P3).
Qed.
(*----------------------------------------------------------------------------*)

(* Better Transitive *)
Lemma l_l_t: ∀ R, ∀ A, ∀ x, ∀ y, ∀ z, r_trans R A → x ∈ A → y ∈ A → z ∈ A
  → x <[R] y → y <[R] z → x <[R] z.
Proof.
  intros R A x y z P1 P2 P3 P4 P5 P6.
  apply (P1 _ _ _ P2 P3 P4 P5 P6).
Qed.

Lemma l_le_t: ∀ R, ∀ A, ∀ x, ∀ y, ∀ z, r_trans R A → x ∈ A → y ∈ A → z ∈ A
  → x <[R] y → y ≤[R] z → x <[R] z.
Proof.
  intros R A x y z P1 P2 P3 P4 P5 [P6 | P6].
  + apply (P1 _ _ _ P2 P3 P4 P5 P6).
  + apply (eq_cl (λ y, x <[R] y) P6).
    apply P5.
Qed.

Lemma le_l_t: ∀ R, ∀ A, ∀ x, ∀ y, ∀ z, r_trans R A → x ∈ A → y ∈ A → z ∈ A
  → x ≤[R] y → y <[R] z → x <[R] z.
Proof.
  intros R A x y z P1 P2 P3 P4 [P5 | P5] P6.
  + apply (P1 _ _ _ P2 P3 P4 P5 P6).
  + apply (eq_cr (λ x, x <[R] z) P5).
    apply P6.
Qed.

Lemma le_le_t: ∀ R, ∀ A, ∀ x, ∀ y, ∀ z, r_trans R A → x ∈ A → y ∈ A → z ∈ A
  → x ≤[R] y → y ≤[R] z → x ≤[R] z.
Proof.
  intros R A x y z P1 P2 P3 P4 [P5 | P5] [P6 | P6].
  + left.
    apply (P1 _ _ _ P2 P3 P4 P5 P6).
  + left.
    apply (eq_cl (λ y, x <[R] y) P6).
    apply P5.
  + left.
    apply (eq_cr (λ x, x <[R] z) P5).
    apply P6.
  + right.
    apply (eq_t P5 P6).
Qed.

Lemma sub_exten: ∀R, ∀ A, ∀ t, t ∈ A → {x: A| x ≤[R] t} = {x: A| x <[R] t} ∪ J{t}.
Proof.
  intros R A t P0.
  apply sub_a.
  split.
  + intros x P1.
    destruct (sub_e _ _ _ P1) as [P2 [P3 | P3]].
    - apply union2_il.
      apply (sub_i _ _ _ P2 P3).
    - apply union2_ir.
      apply (eq_cr (λ x, x ∈ J{t}) P3).
      apply sing_i.
  + intros x P1.
    destruct (union2_e _ _ _ P1) as [P2 | P2].
    - destruct (sub_e _ _ _ P2) as [P3 P4].
      apply (sub_i _ _ _ P3 (or_il _ P4)).
    - apply (eq_cl (λ x, x ∈ {x0: A| x0 ≤[R] t}) (sing_e _ _ P2)).
      apply (sub_i _ _ _ P0 (or_ir _ (eq_r _))).
Qed.
