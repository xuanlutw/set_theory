Require Import Init.Init.
Require Import Relation.Relation.
Require Import Nat.Nat.

Definition less (x y R: J) := (⟨x, y⟩ ∈ R).
Notation " x <[ R ] y" := (less x y R).
Notation " x ≮[ R ] y" := (~(less x y R)).
Notation " x ≤[ R ] y" := ((x <[R] y) ∨ x = y).
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

Definition isom (R A S B: J) :=  ∃ f, bij f A B ∧ 
  (∀ x, ∀ y, x ∈ A → y ∈ A → ⟨x, y⟩ ∈ R → ⟨f[x], f[y]⟩ ∈ S) ∧
  (∀ x, ∀ y, x ∈ A → y ∈ A → ⟨f[x], f[y]⟩ ∈ S → ⟨x, y⟩ ∈ R).

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

Lemma lo_sandwich: ∀ R, ∀ A, ∀ x, ∀ y, lo R A → x ∈ A → y ∈ A → x ≤[R] y 
  → y ≤[R] x → x = y.
  intros R A x y P1.
  apply (po_sandwich _ _ _ _ (lo_is_po _ _ P1)).
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

Lemma wo_sandwich: ∀ R, ∀ A, ∀ x, ∀ y, wo R A → x ∈ A → y ∈ A → x ≤[R] y 
  → y ≤[R] x → x = y.
  intros R A x y P1.
  apply (lo_sandwich _ _ _ _ (wo_is_lo _ _ P1)).
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

(* Relation exten *)
Lemma rel_eq1: ∀ R1, ∀ R2, ∀ A, ∀ x, ∀ y, R1 ∩ (A ⨉ A) = R2 ∩ (A ⨉ A) → x ∈ A 
  → y ∈ A → x <[R1] y → x <[R2] y.
Proof.
  intros R1 R2 A x y P1 P2 P3 P4.
  assert (⟨x, y⟩ ∈ (R1 ∩ (A ⨉ A))) as P5.
  { apply inter2_i.
    + apply P4.
    + apply (cp_i _ _ _ _ P2 P3). }
  pose (eq_cl (λ s, ⟨x, y⟩ ∈ s) P1 P5) as P6.
  destruct (inter2_e _ _ _ P6) as [P7 _].
  apply P7.
Qed.

Lemma rel_eq2: ∀ R1, ∀ R2, ∀ A, ∀ x, ∀ y, R1 ∩ (A ⨉ A) = R2 ∩ (A ⨉ A) → x ∈ A
  → y ∈ A → x ≮[R1] y → x ≮[R2] y.
Proof.
  intros R1 R2 A x y P1 P2 P3 P4 P5.
  apply P4.
  apply (rel_eq1 _ _ _ _ _ (eq_s P1) P2 P3 P5).
Qed.

Lemma rel_eq3: ∀ R1, ∀ R2, ∀ A, ∀ x, ∀ y, R1 ∩ (A ⨉ A) = R2 ∩ (A ⨉ A) → x ∈ A
  → y ∈ A → x ≤[R1] y → x ≤[R2] y.
Proof.
  intros R1 R2 A x y P1 P2 P3 [P4 | P4].
  + left.
    apply (rel_eq1 _ _ _ _ _ P1 P2 P3 P4).
  + right.
    apply P4.
Qed.

Lemma trans_rel_exten: ∀ R1, ∀ R2, ∀ A, R1 ∩ (A ⨉ A) = R2 ∩ (A ⨉ A) 
  → r_trans R1 A → r_trans R2 A.
Proof.
  intros R1 R2 A P1 P2 x y z P3 P4 P5 P6 P7.
  apply (rel_eq1 _ _ _ _ _ P1 P3 P5).
  apply (P2 _ _ _ P3 P4 P5).
  + apply (rel_eq1 _ _ _ _ _ (eq_s P1) P3 P4 P6).
  + apply (rel_eq1 _ _ _ _ _ (eq_s P1) P4 P5 P7).
Qed.

Lemma tricho_rel_exten: ∀ R1, ∀ R2, ∀ A, R1 ∩ (A ⨉ A) = R2 ∩ (A ⨉ A)
  → tricho R1 A → tricho R2 A.
Proof.
  intros R1 R2 A P1 P2 x y P3 P4.
  destruct (P2 _ _ P3 P4) as [[P5 [P6 P7]] | [[P5 [P6 P7]] | [P5 [P6 P7]]]].
  + left.
    repeat split.
    - apply (rel_eq1 _ _ _ _ _ P1 P3 P4 P5).
    - apply P6.
    - apply (rel_eq2 _ _ _ _ _ P1 P4 P3 P7).
  + right. left.
    repeat split.
    - apply (rel_eq2 _ _ _ _ _ P1 P3 P4 P5).
    - apply P6.
    - apply (rel_eq2 _ _ _ _ _ P1 P4 P3 P7).
  + right. right.
    repeat split.
    - apply (rel_eq2 _ _ _ _ _ P1 P3 P4 P5).
    - apply P6.
    - apply (rel_eq1 _ _ _ _ _ P1 P4 P3 P7).
Qed.

Lemma least_prop_rel_exten: ∀ R1, ∀ R2, ∀ A, R1 ∩ (A ⨉ A) = R2 ∩ (A ⨉ A)
  → least_prop R1 A → least_prop R2 A.
Proof.
  intros R1 R2 A P1 P2 A' P3 P4.
  destruct (P2 _ P3 P4) as [x [P5 P6]].
  exists x.
  split.
  + apply P5.
  + intros x' P7.
    apply (rel_eq3 _ _ _ _ _ P1 (P3 _ P5) (P3 _ P7) (P6 _ P7)).
Qed.
    
Lemma lo_rel_exten: ∀ R1, ∀ R2, ∀ A, R1 ∩ (A ⨉ A) = R2 ∩ (A ⨉ A) → lo R1 A
  → lo R2 A.
Proof.
  intros R1 R2 A P1 [P2 P3].
  split.
  + apply (trans_rel_exten _ _ _ P1 P2).
  + apply (tricho_rel_exten _ _ _ P1 P3).
Qed.

Lemma wo_rel_exten: ∀ R1, ∀ R2, ∀ A, R1 ∩ (A ⨉ A) = R2 ∩ (A ⨉ A) → wo R1 A
  → wo R2 A.
Proof.
  intros R1 R2 A P1 [P2 P3].
  split.
  + apply (lo_rel_exten _ _ _ P1 P2).
  + apply (least_prop_rel_exten _ _ _ P1 P3).
Qed.
(*----------------------------------------------------------------------------*)

(* Add Largest Element *)
(*Lemma trans_add_largest: ∀ R, ∀ A, ∀ a, a ∉ A → r_trans R A *)
  (*→ r_trans (R ∪ (A ⨉ J{a})) (A ∪ J{a}).*)
(*Proof.*)
  (*intros R A a P1 P2 x y z P3 P4 P5 P6 P7.*)
  (*destruct (union2_sing_e _ _ _ P3) as [P8 | P8].*)
  (*+ destruct (union2_sing_e _ _ _ P4) as [P9 | P9].*)
    (*- destruct (union2_sing_e _ _ _ P5) as [P10 | P10].*)
      (** ...*)
        (*do many many case analysis...*)
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
(*----------------------------------------------------------------------------*)

(* Isomorphrism *)
Lemma isom_r: ∀ R, ∀ A, isom R A R A.
Proof.
  intros R A.
  exists (id A).
  split.
  + apply id_is_bij.
  + split.
    - intros x y P1 P2 P3.
      apply (eq_cr (λ s, ⟨s, id A[y]⟩ ∈ R) (id_fval _ _ P1)).
      apply (eq_cr (λ s, ⟨x, s⟩ ∈ R) (id_fval _ _ P2)).
      apply P3.
    - intros x y P1 P2 P3.
      apply (eq_cl (λ s, ⟨s, y⟩ ∈ R) (id_fval _ _ P1)).
      apply (eq_cl (λ s, ⟨id A[x], s⟩ ∈ R) (id_fval _ _ P2)).
      apply P3.
Qed.

Lemma isom_s: ∀ R, ∀ A, ∀ S, ∀ B, isom R A S B → isom S B R A.
Proof.
  intros R A S B [f [P1 [P2 P3]]].
  destruct (inv_bij _ _ _ P1) as [P4 _].
  exists (inv f).
  split.
  + apply (inv_bij _ _ _ P1).
  + split.
    - intros x y P5 P6 P7.
      apply P3.
      * apply (fval_codom _ _ _ _ P4 P5).
      * apply (fval_codom _ _ _ _ P4 P6).
      * destruct (bij_e _ _ _ P1) as [_ P8].
        destruct P1 as [_ [P1 _]].
        pose (eq_cr (λ s, x ∈ s) P1 P5) as P9.
        pose (eq_cr (λ s, y ∈ s) P1 P6) as P10.
        apply (eq_cr (λ s, ⟨s, f[inv f[y]]⟩ ∈ S) (inv_fn_ex2 _ _ _ _ P8 P9)).
        apply (eq_cr (λ s, ⟨x, s⟩ ∈ S) (inv_fn_ex2 _ _ _ _ P8 P10)).
        apply P7.
    - intros x y P5 P6 P7.
      destruct (bij_e _ _ _ P1) as [_ P8].
      destruct P1 as [_ [P1 _]].
      pose (eq_cr (λ s, x ∈ s) P1 P5) as P9.
      pose (eq_cr (λ s, y ∈ s) P1 P6) as P10.
      apply (eq_cl (λ s, ⟨s, y⟩ ∈ S) (inv_fn_ex2 _ _ _ _ P8 P9)).
      apply (eq_cl (λ s, ⟨f[inv f[x]], s⟩ ∈ S) (inv_fn_ex2 _ _ _ _ P8 P10)).
      apply P2.
      * apply (fval_codom _ _ _ _ P4 P5).
      * apply (fval_codom _ _ _ _ P4 P6).
      * apply P7.
Qed.

Lemma isom_t: ∀ R, ∀ A, ∀ S, ∀ B, ∀ T, ∀ C, isom R A S B → isom S B T C 
  → isom R A T C.
Proof.
  intros R A S B T C [f [P1 [P2 P3]]] [g [P4 [P5 P6]]].
  exists (g ∘ f).
  split.
  + apply (comp_bij _ _ _ _ _ P1 P4).
  + split.
    - intros x y Q1 Q2 Q3.
      destruct P1 as [P1 _].
      destruct P4 as [P4 _].
      pose (comp_dom_fnm _ _ _ _ _ P1 P4) as Q4.
      pose (eq_cr (λ s, x ∈ s) Q4 Q1) as Q5.
      pose (eq_cr (λ s, y ∈ s) Q4 Q2) as Q6.
      pose (fval_codom _ _ _ _ P1 Q1) as Q7.
      pose (fval_codom _ _ _ _ P1 Q2) as Q8.
      apply (eq_cl (λ s, ⟨s, (g ∘ f)[y]⟩ ∈ T)
        (comp_fval _ _ _ (and_el P1) (and_el P4) Q5)).
      apply (eq_cl (λ s, ⟨g[f[x]], s⟩ ∈ T)
        (comp_fval _ _ _ (and_el P1) (and_el P4) Q6)).
      apply (P5 _ _ Q7 Q8).
      apply (P2 _ _ Q1 Q2 Q3).
    - intros x y Q1 Q2 Q3.
      destruct P1 as [P1 _].
      destruct P4 as [P4 _].
      pose (comp_dom_fnm _ _ _ _ _ P1 P4) as Q4.
      pose (eq_cr (λ s, x ∈ s) Q4 Q1) as Q5.
      pose (eq_cr (λ s, y ∈ s) Q4 Q2) as Q6.
      pose (fval_codom _ _ _ _ P1 Q1) as Q7.
      pose (fval_codom _ _ _ _ P1 Q2) as Q8.
      apply (P3 _ _ Q1 Q2).
      apply (P6 _ _ Q7 Q8).
      apply (eq_cr (λ s, ⟨s, g[f[y]]⟩ ∈ T)
        (comp_fval _ _ _ (and_el P1) (and_el P4) Q5)).
      apply (eq_cr (λ s, ⟨(g ∘ f)[x], s⟩ ∈ T)
        (comp_fval _ _ _ (and_el P1) (and_el P4) Q6)).
      apply Q3.
Qed.
(* Skip 7F *)

Lemma isom_r_irrefl: ∀ R, ∀ A, ∀ S, ∀ B, r_irrefl R A → isom R A S B 
  → r_irrefl S B.
Proof.
  intros R A S B P1 [f [P2 [P3 P4]]] x P5 P6.
  assert ((inv f)[x] ∈ A) as Q1.
  { destruct P2 as [[Q1 [Q2 _]] [Q3 Q4]].
    apply (eq_cl (λ s, (inv f)[x] ∈ s) Q2).
    apply (eq_cl (λ s, (inv f)[x] ∈ s) (inv_ran f)).
    apply fval_ran.
    + apply inv_fn.
      apply Q4.
    + apply (eq_cr (λ s, x ∈ s) (inv_dom f)).
      apply (eq_cr (λ s, x ∈ s) Q3).
      apply P5. }
  destruct (bij_e _ _ _ P2) as [_ P7].
  destruct P2 as [_ [P2 _]].
  pose (eq_cr (λ s, x ∈ s) P2 P5) as P8.
  pose (eq_cr (λ s, ⟨s, s⟩ ∈ S) (inv_fn_ex2 _ _ _ _ P7 P8) P6) as P9.
  apply (P1 ((inv f)[x])).
  + apply Q1.
  + apply (P4 _ _ Q1 Q1).
    apply P9.
Qed.

Lemma isom_r_trans: ∀ R, ∀ A, ∀ S, ∀ B, r_trans R A → isom R A S B 
  → r_trans S B.
Proof.
  intros R A S B P1 P2 x y z Q1 Q2 Q3 P3 P4.
  destruct (isom_s _ _ _ _ P2) as [f [P5 [P6 P7]]].
  pose (P6 _ _ Q1 Q2 P3) as P8.
  pose (P6 _ _ Q2 Q3 P4) as P9.
  destruct P5 as [P5 _].
  pose (P1 _ _ _ (fval_codom _ _ _ _ P5 Q1) (fval_codom _ _ _ _ P5 Q2)
    (fval_codom _ _ _ _ P5 Q3) P8 P9) as P10.
  apply (P7 _ _ Q1 Q3 P10).
Qed.

Lemma isom_tricho: ∀ R, ∀ A, ∀ S, ∀ B, tricho R A → isom R A S B → 
  tricho S B.
Proof.
  intros R A S B P1 P2 x y Q1 Q2.
  destruct (isom_s _ _ _ _ P2) as [f [[P5 [P8 P9]] [P6 P7]]].
  destruct (P1 _ _ (fval_codom _ _ _ _ P5 Q1) (fval_codom _ _ _ _ P5 Q2))
    as [[S1 [S2 S3]]|[[S1 [S2 S3]]|[S1 [S2 S3]]]].
  + left.
    repeat split.
    - apply (P7 _ _ Q1 Q2 S1).
    - intros P10.
      apply S2.
      apply (eq_cr (λ x, f[x] = f[y]) P10).
      apply eq_r.
    - intros P10.
      apply S3.
      apply (P6 _ _ Q2 Q1 P10).
  + right. left.
    repeat split.
    - intros P10.
      apply S1.
      apply (P6 _ _ Q1 Q2 P10).
    - destruct P5 as [P5 [P10 _]].
      apply (P9 _ _ (f[x])).
      * apply (fval_i2 _ _ P5).
        apply (eq_cr (λ s, x ∈ s) P10).
        apply Q1.
      * apply (eq_cr (λ s, ⟨y, s⟩ ∈ f) S2).
        apply (fval_i2 _ _ P5).
        apply (eq_cr (λ s, y ∈ s) P10).
        apply Q2.
    - intros P11.
      apply bot_e.
      apply S3.
      apply (P6 _ _ Q2 Q1 P11).
  + right. right.
    repeat split.
    - intros P10.
      apply S1.
      apply (P6 _ _ Q1 Q2 P10).
    - intros P10.
      apply S2.
      apply (eq_cr (λ x, f[x] = f[y]) P10).
      apply eq_r.
    - apply (P7 _ _ Q2 Q1 S3).
Qed.

Lemma isom_least_prop: ∀ R, ∀ A, ∀ S, ∀ B, least_prop R A → isom R A S B 
  → least_prop S B.
Proof.
  intros R A S B P1 P2 C P3 P4.
  destruct P2 as [f [[[P5 [P6 _]] [P7 P8]] [P9 P10]]].
  assert (inj f A B) as P11.
  { repeat split.
    + apply (and_el P5).
    + apply (and_er P5).
    + apply P6.
    + apply (eq_cr (λ x, x ⊆ B) P7).
      apply sub_r.
    + apply P8. }
  assert ((inv f)⟦C⟧ ⊆ A) as Q1.
  { apply (eq_cl (λ x, (inv f)⟦C⟧ ⊆ x) P6).
    apply (inv_image_ran). }
  assert ((inv f)⟦C⟧ ≠ ∅) as Q2.
  { destruct (nempty_ex _ P4) as [x Q2].
    apply ex_nempty.
    exists ((inv f)[x]).
    apply image_i.
    exists x.
    split.
    + apply fval_i2.
      - apply inv_fn.
        apply P8.
      - apply (eq_cr (λ y, x ∈ y) (inv_dom f)).
        apply (eq_cr (λ y, x ∈ y) P7).
        apply (P3 _ Q2).
    + apply Q2. }
  destruct (P1 _ Q1 Q2) as [x [Q3 Q4]].
  exists (f[x]).
  split.
  + destruct (image_e _ _ _ Q3) as [y [Q5 Q6]].
    apply (eq_cl (λ x, x ∈ C) (fval_i _ _ _ P5 (inv_e _ _ _ Q5))).
    apply Q6.
  + intros y P12.
    assert ((inv f)[y] ∈ (inv f)⟦C⟧) as P13.
    { apply image_i2.
      + apply inv_fn.
        apply P8.
      + apply (eq_cr (λ x, y ∈ x) (inv_dom f)).
        apply (eq_cr (λ x, y ∈ x) P7).
        apply (P3 _ P12).
      + apply P12. }
    destruct (Q4 _ P13) as [Q5 | Q5].
    - left.
      assert (y ∈ ran(f)) as Q6.
      { apply (eq_cr (λ x, y ∈ x) P7).
        apply (P3 _ P12). }
      apply (eq_cl (λ y, f[x] <[S] y) (inv_fn_ex2 _ _ _ _ P11 Q6)).
      apply (P9).
      * apply (eq_cl (λ y, x ∈ y) P6).
        destruct (image_e _ _ _ Q3) as [s [Q8 _]].
        apply (dom_i2 _ _ _ (inv_e _ _ _ Q8)).
      * apply (eq_cl (λ x, (inv f)[y] ∈ x) P6).
        apply (eq_cl (λ x, (inv f)[y] ∈ x) (inv_ran f)).
        apply fval_ran.
        ++apply inv_fn.
          apply P8.
        ++apply (eq_cr (λ x, y ∈ x) (inv_dom f)).
          apply Q6.
      * apply Q5.
    - right.
      apply (eq_cr (λ x, f[x] = y) Q5).
      apply (inv_fn_ex2 _ _ _ _ P11).
      apply (eq_cr (λ x, y ∈ x) P7).
      apply (P3 _ P12).
Qed.

Lemma isom_po: ∀ R, ∀ A, ∀ S, ∀ B, po R A → isom R A S B → po S B.
Proof.
  intros R A S B [P1 P2] P3.
  split.
  + apply (isom_r_trans _ _ _ _ P1 P3).
  + apply (isom_r_irrefl _ _ _ _ P2 P3).
Qed.

Lemma isom_lo: ∀ R, ∀ A, ∀ S, ∀ B, lo R A → isom R A S B → lo S B.
Proof.
  intros R A S B [P1 P2] P3.
  split.
  + apply (isom_r_trans _ _ _ _ P1 P3).
  + apply (isom_tricho _ _ _ _ P2 P3).
Qed.

Lemma isom_wo: ∀ R, ∀ A, ∀ S, ∀ B, wo R A → isom R A S B → wo S B.
Proof.
  intros R A S B [P1 P2] P3.
  split.
  + apply (isom_lo _ _ _ _ P1 P3).
  + apply (isom_least_prop _ _ _ _ P2 P3).
Qed.
(*----------------------------------------------------------------------------*)
