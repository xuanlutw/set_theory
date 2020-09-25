Require Import Init.Init.
Require Import Relation.Relation.
Require Import Nat.Inductive.
Require Import Nat.Nature.

(* Recursion Theorem *)
Definition _rec_accept (F A a: J) :=
  λ f, fn f ∧ dom(f) ⊆ ω ∧ ran(f) ⊆ A ∧ ∅ ∈ dom(f) ∧ f[∅] = a ∧ 
    (∀ n, n ∈ ω → S(n) ∈ dom(f) → n ∈ dom(f) ∧ f[S(n)] = F[f[n]]).

Lemma _rec_fun: ∀ A, ∀ a, ∀ F, fn (∪{x: 𝒫(ω ⨉ A)| _rec_accept F A a x}).
Proof.
  intros A a F.
  pose (_rec_accept F A a) as P.
  pose ({x: 𝒫(ω ⨉ A)| P x}) as H.
  pose (∪H) as h.
  split.
  (* is relation *)
  + apply union_rel.
    intros f P1.
    destruct (sub_e _ _ _ P1) as [_ [[P2 _] _]].
    apply P2.
  (* is single value *)
  + intros a0.
    (* induction property *)
    pose (λ x, ∀ b1, ∀ b2, ⟨x, b1⟩ ∈ h → ⟨x, b2⟩ ∈ h → b1 = b2) as PI.
    assert (PI ∅) as P1.
    { intros b1 b2 P2 P3.
      destruct (union_e _ _ P2) as [H1 [Q1 Q2]].
      destruct (sub_e _ _ _ Q1) as [_ [Q3 [_ [_ [Q4 [Q5 _]]]]]].
      destruct (fval_e _ _ _ (eq_s Q5) Q3 Q4) as [_ Q6].
      apply (eq_cl (λ x, x = b2) (Q6 _ Q2)).
      destruct (union_e _ _ P3) as [H2 [R1 R2]].
      destruct (sub_e _ _ _ R1) as [_ [R3 [_ [_ [R4 [R5 _]]]]]].
      destruct (fval_e _ _ _ (eq_s R5) R3 R4) as [_ R6].
      apply (R6 _ R2). }
    (* induction step *)
    assert (induction_step PI) as P2.
    { intros k P2 P3 b1 b2 P4 P5.
      destruct (union_e _ _ P4) as [H1 [Q1 Q2]].
      destruct (sub_e _ _ _ Q1) as [_ [Q3 [_ [_ [_ [_ Q4]]]]]].
      destruct (Q4 _ P2 (dom_i _ _ _  Q2)) as [Q5 Q6].
      apply (eq_cr (λ x, x = b2) (fval_i _ _ _ Q3 Q2)).
      apply (eq_cr (λ x, x = b2) Q6).
      destruct (union_e _ _ P5) as [H2 [R1 R2]].
      destruct (sub_e _ _ _ R1) as [_ [R3 [_ [_ [_ [_ R4]]]]]].
      destruct (R4 _ P2 (dom_i _ _ _ R2)) as [R5 R6].
      apply (eq_cr (λ x, F[H1[k]] = x) (fval_i _ _ _ R3 R2)).
      apply (eq_cr (λ x, F[H1[k]] = x) R6).
      assert (H1[k] = H2[k]) as P6.
      { apply P3.
        + apply union_i.
          exists H1.
          split.
          - apply Q1.
          - apply (fval_i2 _ _ Q3 Q5).
        + apply union_i.
          exists H2.
          split.
          - apply R1.
          - apply (fval_i2 _ _ R3 R5). }
      apply (eq_cr (λ x, F[x] = F[H2[k]]) P6).
      apply eq_r. }
    destruct (LEM (a0 ∈ ω)) as [P3 | P3].
    - apply (induction_principle _ P1 P2 a0 P3).
    - intros b1 b2 P4 _.
      apply bot_e.
      apply P3.
      destruct (union_e _ _ P4) as [Hi [P5 P6]].
      destruct (sub_e _ _ _ P5) as [_ [_ [P7 _]]].
      apply (P7 _ (dom_i _ _ _ P6)).
Qed.

Lemma _rec_single_pair_accept: ∀ A, ∀ a, ∀ F, a ∈ A 
  → `{⟨∅, a⟩} ∈ {x: 𝒫(ω ⨉ A)| _rec_accept F A a x}.
Proof.
  intros A a F P1.
  pose (_rec_accept F A a) as P.
  pose ({x: 𝒫(ω ⨉ A)| P x}) as H.
  pose (∪H) as h.
  apply sub_i.
  { apply power_i.
    intros x P2.
    apply (eq_cl (λ x, x ∈ ω ⨉ A) (sing_e _ _ P2)).
    apply cp_i.
    + apply empty_is_nat.
    + apply P1. }
  split.
  { apply sing_pair_is_fn. }
  split.
  { apply (eq_cr (λ x, x ⊆ ω) (sing_pair_dom ∅ a)).
    intros x P2.
    apply (eq_cl (λ x, x ∈ ω) (sing_e _ _ P2)).
    apply empty_is_nat. }
  split.
  { apply (eq_cr (λ x, x ⊆ A) (sing_pair_ran ∅ a)).
    intros x P2.
    apply (eq_cl (λ x, x ∈ A) (sing_e _ _ P2)).
    apply P1. }
  split.
  { apply (eq_cr (λ x, ∅ ∈ x) (sing_pair_dom ∅ a)).
    apply sing_i. }
  split.
  { apply eq_s. 
    apply fval_i.
    + apply sing_pair_is_fn. 
    + apply sing_i. }
  { intros n P3 P4.
    apply bot_e.
    apply (empty_not_suc n).
    apply (sing_e _ _ (eq_cl (λ x, S(n) ∈ x) (sing_pair_dom ∅ a) P4)). }
Qed.

Lemma _rec_union_fn: ∀ A, ∀ a, ∀ F, ∀ f, ∀ x, ∀ y, a ∈ A → fnm F A A
  → S(x) ∉  dom(f) → ⟨x, y⟩ ∈ f → x ∈ ω → f ∈ {x: 𝒫(ω ⨉ A)| _rec_accept F A a x}
  → fn (f ∪ `{⟨S(x), F[y]⟩}).
Proof. 
  intros A a F f x y P1 P2 P3 P4 P5 P6.
  pose (_rec_accept F A a) as P.
  pose ({x: 𝒫(ω ⨉ A)| P x}) as H.
  pose (∪H) as h.
  apply piecewise_function. 
  + destruct (sub_e _ _ _ P6) as [_ [Q1 _]].
    apply Q1.
  + apply sing_pair_is_fn.
  + apply (eq_cr (λ x, dom(f) ∩ x = ∅) (sing_pair_dom (S(x)) (F[y]))).
    apply (eq_cr (λ x, x = ∅) (inter2_s (dom(f)) (`{S(x)}))).
    apply inter2_empty.
    intros s P7 P8.
    apply P3.
    apply (eq_cr (λ s, s ∈ dom(f)) (sing_e _ _ P7) P8).
Qed.

Lemma _rec_union_accept: ∀ A, ∀ a, ∀ F, ∀ f, ∀ x, ∀ y, a ∈ A → fnm F A A 
  → S(x) ∉  dom(f) → ⟨x, y⟩ ∈ f → x ∈ ω → f ∈ {x: 𝒫(ω ⨉ A)| _rec_accept F A a x}
  → (f ∪ `{⟨S(x), F[y]⟩}) ∈ {x: 𝒫(ω ⨉ A)| _rec_accept F A a x}.
Proof.
  intros A a F f x y P1 P2 P3 P4 P5 P6.
  pose (_rec_accept F A a) as P.
  pose ({x: 𝒫(ω ⨉ A)| P x}) as H.
  pose (∪H) as h.
  apply sub_i.
  { apply power_i.
    intros z Q1.
    destruct (union2_e _ _ _ Q1) as [Q2 | Q2].
    + destruct (sub_e _ _ _ P6) as [Q3 _].
      apply (power_e _ _ Q3 _ Q2).
    + apply (eq_cl (λ z, z ∈ ω ⨉ A) (sing_e _ _ Q2)).
      apply cp_i.
      - apply (suc_is_nat _ P5).
      - destruct P2 as [Q3 [Q4 Q5]]. 
        apply Q5.
        apply fval_ran.
        * apply Q3.
        * destruct (sub_e _ _ _ P6) as [_ [_ [_ [Q6 _]]]].
          apply (eq_cr (λ x, y ∈ x) Q4).
          apply (Q6 _ (ran_i _ _ _ P4)). }
  split.
  { apply (_rec_union_fn _ _ _ _ _ _ P1 P2 P3 P4 P5 P6). }
  split.
  { apply (eq_cr (λ x, x ⊆ ω) (union2_dom f `{⟨S(x), F[y]⟩})).
    apply union2_sub. 
    + destruct (sub_e _ _ _ P6) as [_ [_ [Q3 _]]].
      apply Q3.
    + apply (eq_cr (λ x, x ⊆ ω) (sing_pair_dom (S(x)) (F[y]))).
      apply sing_sub_i.
      apply (suc_is_nat _ P5). }
  split.
  { apply (eq_cr (λ x, x ⊆ A) (union2_ran f `{⟨S(x), F[y]⟩})).
    apply union2_sub. 
    + destruct (sub_e _ _ _ P6) as [_ [_ [_ [Q3 _]]]].
      apply Q3.
    + destruct P2 as [Q1 [Q2 Q3]].
      destruct (sub_e _ _ _ P6) as [_ [_ [_ [Q4 _]]]].
      apply (eq_cr (λ x, x ⊆ A) (sing_pair_ran (S(x)) (F[y]))).
      apply sing_sub_i.
      apply Q3.
      apply fval_ran.
      - apply Q1.
      - apply (eq_cr (λ x, y ∈ x) Q2).
        apply Q4.
        apply (ran_i _ _ _ P4). }
  split.
  { destruct (sub_e _ _ _ P6) as [_ [_ [_ [_ [Q1 _]]]]].
    apply (eq_cr (λ x, ∅ ∈ x) (union2_dom f `{⟨S(x), F[y]⟩})).
    apply union2_il.
    apply Q1. }
  split.
  { apply eq_s.
    apply fval_i.
    + apply (_rec_union_fn _ _ _ _ _ _ P1 P2 P3 P4 P5 P6).
    + destruct (sub_e _ _ _ P6) as [_ [Q1 [_ [_ [Q2 [Q3 _]]]]]].
      apply union2_il.
      apply (eq_cl (λ x, ⟨∅, x⟩ ∈ f) Q3).
      apply (fval_i2 _ _ Q1 Q2). }
  { apply (eq_cr (λ s, ∀ n, n ∈ ω → S(n) ∈ s 
      → n ∈ s ∧ (f ∪ `{⟨S(x), F [y]⟩})[S(n)] = F[(f ∪ `{⟨S(x), F[y]⟩})[n]]) 
      (union2_dom f `{⟨S(x), F[y]⟩})). 
    intros n Q1 Q2.
    destruct (union2_e _ _ _ Q2) as [Q3 | Q3].
    + split.
      - destruct (sub_e _ _ _ P6) as [_ [_ [_ [_ [_ [_ Q4]]]]]].
        destruct (Q4 _ Q1 Q3) as [Q5 _].
        apply union2_il.
        apply Q5.
      - destruct (sub_e _ _ _ P6) as [_ [Q4 [_ [_ [_ [_ Q5]]]]]].
        destruct (Q5 _ Q1 Q3) as [Q6 Q7].
        apply (eq_cl (λ s, s = F[(f ∪ `{⟨S(x), F[y]⟩})[n]]) 
          (union2_fvall _ _ _ Q4 (_rec_union_fn _ _ _ _ _ _ P1 P2 P3 P4 P5 P6) Q3)).
        apply (eq_cl (λ s, f[S(n)] = F[s])
          (union2_fvall _ _ _ Q4 (_rec_union_fn _ _ _ _ _ _ P1 P2 P3 P4 P5 P6) Q6)).
        apply Q7.
    + pose (eq_cl (λ x, S(n) ∈ x) (sing_pair_dom (S(x)) (F[y])) Q3) as Q4.
      pose (suc_unique _ _ P5 Q1 (sing_e _ _ Q4)) as Q5.
      pose (eq_cl (λ x, x ∈ dom(f)) Q5 (dom_i _ _ _ P4)) as Q6.
      destruct (sub_e _ _ _ P6) as [_ [Q7 [_ [_ [_ [_ _]]]]]].
      split.
      - apply union2_il.
        apply Q6.
      - apply (eq_cl (λ s, s = F[(f ∪ `{⟨S(x), F[y]⟩})[n]]) 
          (union2_fvalr _ _ _ (sing_pair_is_fn (S(x)) (F[y])) 
          (_rec_union_fn _ _ _ _ _ _ P1 P2 P3 P4 P5 P6) Q3)).
        apply (eq_cl (λ s, `{⟨S(x), F[y]⟩}[S(n)] = F[s]) 
          (union2_fvall _ _ _ Q7 (_rec_union_fn _ _ _ _ _ _ P1 P2 P3 P4 P5 P6) Q6)).
        apply eq_s.
        apply fval_i.
        * apply sing_pair_is_fn.
        * apply sing_i2.
          apply opair_eq_i.
          ++apply (eq_cr (λ x, S(n) = S(x)) Q5).
            apply eq_r.
          ++apply (eq_cl (λ x, F[f[x]] = F[y]) Q5).
            apply (eq_cl (λ x, F[x] = F[y]) (fval_i _ _ _ Q7 P4)).
            apply eq_r. }
Qed.

Lemma _rec_dom: ∀ A, ∀ a, ∀ F, a ∈ A → fnm F A A →
  dom(∪{x: 𝒫(ω ⨉ A)| _rec_accept F A a x}) = ω.
Proof.
  intros A a F P1 S1.
  pose (_rec_accept F A a) as P.
  pose ({x: 𝒫(ω ⨉ A)| P x}) as H.
  pose (∪H) as h.
  assert (inductive (dom(h))) as P2.
  { split.
    + apply dom_i.
      exists a.
      apply union_i.
      exists (`{⟨∅, a⟩}).
      split.
      - apply (_rec_single_pair_accept _ _ _ P1). 
      - apply sing_i.
    + intros x P2.
      destruct (dom_e _ _ P2) as [y P3].
      destruct (union_e _ _ P3) as [f [P4 P5]].
      apply dom_i.
      destruct (LEM (S(x) ∈ dom(f))) as [P6 | P6].
      - exists (f[S(x)]).
        apply union_i.
        exists f.
        split.
        * apply P4.
        * destruct (sub_e _ _ _ P4) as [_ [P7 _]].
          apply (fval_i2 _ _ P7 P6).
      - pose (f ∪ `{⟨S(x), F[y]⟩}) as g.
        exists (g[S(x)]).
        apply union_i.
        exists (f ∪ `{⟨S(x), F[y]⟩}).
        assert (x ∈ ω) as P7. 
        { destruct (sub_e _ _ _ P4) as [_ [_ [P7 _]]].
          apply P7.
          apply dom_i.
          exists y.
          apply P5. }
        split.
        * apply (_rec_union_accept _ _ _ _ _ _ P1 S1 P6 P5 P7 P4).
        * destruct (sub_e _ _ _ P4) as [_ [P8 _]].
          apply fval_i2.
          apply (_rec_union_fn _ _ _ _ _ _ P1 S1 P6 P5 P7 P4).
          apply (eq_cr (λ s, S(x) ∈ s) (union2_dom f (`{⟨S(x), F[y]⟩}))).
          apply union2_ir.
          apply (eq_cr (λ s, S(x) ∈ s) (sing_pair_dom (S(x)) (F[y]))).
          apply sing_i. }
  assert (dom(h) ⊆ ω) as P3.
  { intros x P3.
    destruct (dom_e _ _ P3) as [y P4].
    destruct (union_e _ _ P4) as [f [P5 P6]].
    destruct (sub_e _ _ _ P5) as [_ [_ [P7 _]]].
    apply (P7 _ (dom_i _ _ _ P6)). }
  apply (inductive_subset_omega_coincident _ P3 P2).
Qed.

Lemma _rec_ran: ∀ A, ∀ a, ∀ F, a ∈ A 
  → ran(∪{x: 𝒫(ω ⨉ A)| _rec_accept F A a x}) ⊆ A.
Proof.
  intros A a F P1 y P2.
  destruct (ran_e _ _ P2) as [x P3].
  destruct (union_e _ _ P3) as [f [P4 P5]].
  destruct (sub_e _ _ _ P4) as [_ [_ [_ [P6 _]]]].
  apply (P6 _ (ran_i _ _ _ P5)). 
Qed.

Theorem recursion_thm: ∀ A, ∀ a, ∀ F, ∃ h, a ∈ A → fnm F A A 
  → fnm h ω A ∧ h[∅] = a ∧ (∀ n, n ∈ ω → h[S(n)] = F[h[n]]).
Proof.
  intros A a F.
  pose (_rec_accept F A a) as P.
  pose ({x: 𝒫(ω ⨉ A)| P x}) as H.
  pose (∪H) as h.
  exists h.
  intros P1 P2.
  split.
  (* fover h ω A *)
  { split.
    + apply _rec_fun.
    + split.
      - apply (_rec_dom _ _ _ P1 P2).
      - apply (_rec_ran _ _ _ P1). }
  split.
  { apply eq_s.
    apply fval_i.
    + apply _rec_fun.
    + apply union_i.
      exists (`{⟨∅, a⟩}).
      split.
      - apply (_rec_single_pair_accept _ _ _ P1).
      - apply sing_i. } 
  { intros n P3.
    pose (eq_cr (λ x, S(n) ∈ x) (_rec_dom A a F P1 P2) (suc_is_nat _ P3)) as P4.
    destruct (dom_e _ _ P4) as [y P5].
    destruct (union_e _ _ P5) as [f [P6 P7]].
    destruct (sub_e _ _ _ P6) as [_ [P8 [_ [_ [_ [_ P9]]]]]].
    destruct (P9 n P3 (dom_i _ _ _ P7)) as [P10 P11].
    apply (eq_cl (λ x, x = F[h[n]]) 
      (union_fval _ _ _ P6 P8 (_rec_fun A a F) (dom_i _ _ _ P7))).
    apply (eq_cl (λ x, f[S(n)] = F[x]) (union_fval _ _ _ P6 P8 (_rec_fun A a F) P10)).
    apply P11. }
Qed.
(*----------------------------------------------------------------------------*)
