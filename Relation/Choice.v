Require Import Init.Init.
Require Import Relation.Relation_.
Require Import Relation.Function.
Require Import Relation.Function_ctor.
Require Import Relation.Utils.

(* Axiom Choice I *)
Lemma rel_to_fn: ∀ R, rel R → ∃ F, fn F ∧ F ⊆ R ∧ dom(R) = dom(F).
Proof.
  intros R P1.
  pose ({f: 𝒫(R)| fn f}) as A.
  assert (∀ C, C ⊆ A → chain C → ∪C ∈ A) as P2.
  { intros C Q1 Q2.
    pose (sub_t _ _ _ Q1 (sub_e1 _ _)) as Q3.
    apply sub_i.
    + apply power_i.
      intros x Q4.
      destruct (union_e _ _ Q4) as [c [Q5 Q6]].
      pose (power_e _ _ (Q3 _ Q5)) as Q7.
      apply (Q7 _ Q6).
    + split.
      - intros x Q4.
        destruct (union_e _ _ Q4) as [c [Q5 Q6]].
        apply (P1 _ (power_e _ _ (Q3 _ Q5) _ Q6)).
      - intros x y1 y2 Q4 Q5.
        destruct (union_e _ _ Q4) as [c1 [Q6 Q7]].
        destruct (union_e _ _ Q5) as [c2 [Q8 Q9]].
        destruct (Q2 _ _ Q6 Q8) as [Q10 | Q10].
        * destruct (sub_e _ _ _ (Q1 _ Q8)) as [_ [_ Q11]].
          apply (Q11 _ _ _ (Q10 _ Q7) Q9).
        * destruct (sub_e _ _ _ (Q1 _ Q6)) as [_ [_ Q11]].
          apply (Q11 _ _ _ Q7 (Q10 _ Q9)). }
  destruct (zorn _ P2) as [M [P3 P4]].
  exists M.
  split.
  + apply (sub_e _ _ _ P3).
  + split.
    - apply power_e.
      apply (sub_e _ _ _ P3).
    - apply sub_a.
      split.
      * intros x Q1.
        apply nn_e.
        intros Q2.
        destruct (dom_e _ _ Q1) as [y Q3].
        pose (M ∪ `{⟨x, y⟩}) as M'.
        assert (M' ∈ A) as Q4.
        { apply sub_i.
          + apply power_i.
            intros s S1.
            destruct (union2_e _ _ _ S1) as [S2 | S2].
            - destruct (sub_e _ _ _ P3) as [S3 _].
              apply (power_e _ _ S3 _ S2).
            - apply (eq_cl (λ x, x ∈ R) (sing_e _ _ S2) Q3).
          + destruct (sub_e _ _ _ P3) as [_ S1].
            apply (fn_exten _ _ _ S1 Q2). }
        assert (M' ≠ M) as Q5.
        { apply (neq_i _ _ (⟨x, y⟩)).
          + apply union2_ir.
            apply sing_i.
          + intros S1.
            apply Q2.
            apply (dom_i _ _ _ S1). }
        assert (M ⊆ M') as Q6.
        { apply union2_sub_l. }
        destruct (P4 _ Q4) as  [Q7 | Q7].
        ++apply (Q5 Q7).
        ++apply (Q7 Q6).
      * apply sub_dom.
        apply power_e.
        apply (sub_e _ _ _ P3).
Qed.

(* Axiom of Choice II *)
Lemma multiplicative: ∀ H, fn H → (∀ i, i ∈ dom(H) → H[i] ≠ ∅)
  → ∃ f, fn f ∧ dom(f) = dom(H) ∧ (∀ i, i ∈ dom(f) → f[i] ∈ H[i]).
Proof.
  intros H P1 P2.
  pose ({r: dom(H) ⨉ ∪(ran(H))| ∃ i, ∃ y, r = ⟨i, y⟩ ∧ y ∈ H[i]}) as R.
  destruct (rel_to_fn R (cp_sub_rel _ _ _ )) as [F [P3 [P4 P5]]].
  exists F.
  split.
  + apply P3.
  + split.
    - apply (eq_cl (λ x, x = dom(H)) P5).
      apply sub_a.
      split.
      * apply (cp_sub_dom _ _ _ (sub_e1 _ _)).
      * intros i Q1.
        destruct (nempty_ex _ (P2 _ Q1)) as [y Q2].
        apply (dom_i _ _ y).
        apply sub_i.
        ++apply cp_i.
          --apply Q1.
          --apply union_i.
            exists (H[i]).
            split.
            **apply (fval_ran _ _ P1 Q1).
            **apply Q2.
        ++exists i.
          exists y.
          split.
          --apply eq_r.
          --apply Q2.
    - intros i Q1.
      destruct (dom_e _ _ Q1) as [y Q2].
      pose (P4 _ Q2) as Q3.
      destruct (sub_e _ _ _ Q3) as [Q4 [i' [y' [Q5 Q6]]]].
      apply (eq_cr (λ x, F[i] ∈ H[x]) (opair_eq_el _ _ _ _ Q5)).
      apply (eq_cr (λ x, x ∈ H[i']) (fval_i _ _ _ P3 Q2)).
      apply (eq_cr (λ x, x ∈ H[i']) (opair_eq_er _ _ _ _ Q5) Q6).
Qed.

(* Axiom of Choice IV *)
Lemma ax_iv: ∀ A, (∀ a, a ∈ A → a ≠ ∅)
  → (∀ a1, ∀ a2, a1 ∈ A → a2 ∈ A → a1 ≠ a2 → a1 ∩ a2 = ∅)
  → (∃ C, ∀ a, a ∈ A → ∃ x, C ∩ a = `{x}).
Proof.
  intros A P1 P2.
  pose (id A) as H.
  assert (∀ i, i ∈ dom(H) → H[i] ≠ ∅) as P3.
  { intros i Q1 Q2.
    pose (eq_cl (λ x, i ∈ x) (id_dom _) Q1) as Q3.
    pose (eq_cl (λ x, x = ∅) (id_fval _ _ Q3) Q2) as Q4.
    apply (P1 _ Q3).
    apply Q4. }
  destruct (multiplicative _ (id_is_fn _) P3) as [F [P4 [P5 P6]]].
  exists (ran(F)).
  intros a P7.
  pose (eq_t P5 (id_dom _)) as P8.
  pose (eq_cr (λ x, a ∈ x) P8 P7) as P9.
  exists (F[a]).
  apply sub_a.
  split.
  + intros y Q1.
    destruct (inter2_e _ _ _ Q1) as [Q2 Q3].
    destruct (ran_e _ _ Q2) as [x Q4].
    destruct (LEM (x = a)) as [Q5 | Q5].
    - apply sing_i2.
      apply eq_s.
      apply (eq_cl (λ x, F[x] = y) Q5 (fval_i _ _ _ P4 Q4)).
    - assert (x ∈ A) as Q7.
      { apply (eq_cl (λ y, x ∈ y) P8).
        apply (dom_i _ _ _ Q4). }
      assert (x ∩ a ≠ ∅) as Q6.
      { apply ex_nempty.
        exists y.
        apply inter2_i.
        + apply (eq_cl (λ y, y ∈ x) (fval_i _ _ _ P4 Q4)).
          apply (eq_cl (λ y, F[x] ∈ y) (id_fval _ _ Q7)).
          apply (P6 _ (eq_cr (λ y, x ∈ y) P8 Q7)).
        + apply Q3. }
      apply bot_e.
      apply (Q6 (P2 _ _ Q7 P7 Q5)).
  + intros y Q1.
    apply inter2_i.
    - apply (eq_cl (λ x, x ∈ ran(F)) (sing_e _ _ Q1)).
      apply (fval_ran _ _ P4 P9).
    - apply (eq_cl (λ x, x ∈ a) (sing_e _ _ Q1)).
      apply (eq_cl (λ x, F[a] ∈ x) (id_fval _ _ P7)).
      apply (P6 _ P9).
Qed.

(* Axiom of Choice III *)
Lemma choice_fn_ex: ∀ A, ∃ F,
  fn F ∧ dom(F) = 𝒫(A) \ `{∅} ∧ ∀ B, B ≠ ∅ → B ⊆ A → F[B] ∈ B.
Proof.
  intros A.
  pose (𝒫(A) \ `{∅}) as B.
  pose (id B) as H.
  pose (id_is_fn B) as P1.
  assert (∀ i, i ∈ dom(H) → H[i] ≠ ∅) as P2.
  { intros i Q1 Q2.
    pose (eq_cl (λ x, x ∈ ran(id B)) Q2 (fval_ran _ _ P1 Q1)) as Q3.
    pose (eq_cl (λ x, ∅ ∈ x) (id_ran _) Q3) as Q4.
    destruct (compl_e _ _ _ Q4) as [_ Q5].
    apply Q5.
    apply sing_i. }
  destruct (multiplicative _ P1 P2) as [f [P3 [P4 P5]]].
  exists f.
  split.
  + - apply P3.
  + split.
    - apply (eq_cr (λ x, x = 𝒫(A) \ `{∅}) P4).
      apply id_dom.
    - intros A' Q1 Q2.
      assert (A' ∈ B) as Q3.
      { apply compl_i.
        + apply power_i.
          apply Q2.
        + apply nsing_i.
          apply (neq_s Q1). }
      assert (A' ∈ dom(f)) as Q4.
      { apply (eq_cr (λ x, A' ∈ x) (eq_t P4 (id_dom _))).
        apply Q3. }
      apply (eq_cl (λ x, f[A'] ∈ x) (id_fval _ _ Q3)).
      apply (P5 _ Q4).
Qed.
