Require Import Init.Init.
Require Import Relation.Relation_.
Require Import Relation.Function.

(* Combination of Functions *)
Lemma union2_rel: ∀ F, ∀ G, rel F → rel G → rel (F ∪ G).
Proof.
  intros F G P1 P2 r P3.
  destruct (union2_e _ _ _ P3) as [P4 | P4].
  + apply (P1 r P4).
  + apply (P2 r P4).
Qed.

Lemma union_rel: ∀ F, (∀ f, f ∈ F → rel f) → rel (∪(F)).
Proof.
  intros F P1 r P2.
  destruct (union_e _ _ P2) as [s [P3 P4]].
  apply (P1 s P3 r P4).
Qed.

Lemma union2_dom: ∀ F, ∀ G, dom(F ∪ G) = dom(F) ∪ dom(G).
Proof.
  intros F G.
  apply sub_a.
  split.
  + intros x P1.
    destruct (dom_e _ _ P1) as [f P2].
    destruct (union2_e _ _ _ P2) as [P3 | P3].
    - apply union2_il.
      apply (dom_i _ _ _ P3).
    - apply union2_ir.
      apply (dom_i _ _ _ P3).
  + intros x P1.
    destruct (union2_e _ _ _ P1) as [P2 | P2].
    - destruct (dom_e _ _ P2) as [f P3].
      apply (dom_i _ _ f).
      apply (union2_il _ _ _ P3).
    - destruct (dom_e _ _ P2) as [f P3]. 
      apply (dom_i _ _ f).
      apply (union2_ir _ _ _ P3).
Qed.

Lemma union_dom_e: ∀ H, ∀ x, x ∈ dom(∪H) → ∃ f, x ∈ dom(f) ∧ f ∈ H.
Proof.
  intros H x P1.
  destruct (dom_e _ _ P1) as [y P2].
  destruct (union_e _ _ P2) as [f [P3 P4]].
  exists f.
  split.
  + apply (dom_i _ _ _ P4).
  + apply P3.
Qed.

Lemma union_dom_i: ∀ H, ∀ f, ∀ x, x ∈ dom(f) → f ∈ H → x ∈ dom(∪H).
Proof.
  intros H f x P1 P2.
  destruct (dom_e _ _ P1) as [y P3].
  apply (dom_i _ _ y).
  apply union_i.
  exists f.
  split.
  + apply P2.
  + apply P3.
Qed.

Lemma union2_ran: ∀ F, ∀ G, ran(F ∪ G) = ran(F) ∪ ran(G).
Proof.
  intros F G.
  apply sub_a.
  split.
  + intros x P1.
    destruct (ran_e _ _ P1) as [f P2].
    destruct (union2_e _ _ _ P2) as [P3 | P3].
    - apply union2_il.
      apply (ran_i _ _ _ P3).
    - apply union2_ir.
      apply (ran_i _ _ _ P3).
  + intros x P1.
    destruct (union2_e _ _ _ P1) as [P2 | P2].
    - destruct (ran_e _ _ P2) as [f P3]. 
      apply (ran_i _ f).
      apply (union2_il _ _ _ P3).
    - destruct (ran_e _ _ P2) as [f P3]. 
      apply (ran_i _ f).
      apply (union2_ir _ _ _ P3).
Qed.

Lemma disjoint_dom_rel: ∀ F, ∀ G, rel F → rel G → dom(F) ∩ dom(G) = ∅ 
  → F ∩ G = ∅.
Proof. 
  intros F G P1 P2 P3.
  apply empty_unique.
  intros s P4.
  destruct (inter2_e _ _ _ P4) as [P5 P6].
  destruct (P1 _ P5) as [a1 [b1 P7]].
  apply (empty_i a1).
  apply (eq_cl _ P3).
  apply inter2_i.
  + apply (dom_i _ _ _ (eq_cl (λ s, s ∈ F) P7 P5)).
  + apply (dom_i _ _ _ (eq_cl (λ s, s ∈ G) P7 P6)).
Qed.

(* union2_function *)
Lemma piecewise_function: ∀ F, ∀ G, fn F → fn G → (dom(F) ∩ dom(G)) = ∅ 
  → fn (F ∪ G).
Proof.
  intros F G [P1 P3] [P2 P4] P5.
  split.
  + apply (union2_rel F G P1 P2).
  + intros a b1 b2 P6 P7.
    destruct (disjoint_selection _ _ _(disjoint_dom_rel _ _ P1 P2 P5) P6)
      as [[P8 P9] | [P8 P9]].
    - destruct (disjoint_selection _ _ _(disjoint_dom_rel _ _ P1 P2 P5) P7)
        as [[P10 P11] | [P10 P11]].
      * apply (P3 _ _ _ P8 P10).
      * apply bot_e. 
        apply (empty_i a).
        apply (eq_cl _ P5).
        apply inter2_i.
        ++apply (dom_i _ _ _ P8).
        ++apply (dom_i _ _ _ P10).
    - destruct (disjoint_selection _ _ _(disjoint_dom_rel _ _ P1 P2 P5) P7)
        as [[P10 P11] | [P10 P11]].
      * apply bot_e.
        apply (empty_i a).
        apply (eq_cl _ P5).
        apply inter2_i.
        ++apply (dom_i _ _ _ P10).
        ++apply (dom_i _ _ _ P8).
      * apply (P4 _ _ _ P8 P10).
Qed.

Lemma union2_bij: ∀ F, ∀ G, ∀ A, ∀ B, ∀ C, ∀ D, F ∈ A ↦ᵇ B → G ∈ C ↦ᵇ D
  → A ∩ C = ∅ → B ∩ D = ∅ → F ∪ G ∈ (A ∪ C) ↦ᵇ (B ∪ D).
Proof.
  intros F G A B C D P1 P2 P3 P4.
  assert (ran(F) ∩ ran(G) = ∅) as P5.
  { apply (eq_cr (λ x, x ∩ _ = ∅) (bij_ran _ _ _ P1)).
    apply (eq_cr (λ x, _ ∩ x = ∅) (bij_ran _ _ _ P2) P4). }
  apply bij_i.
  + apply piecewise_function.
    - apply (bij_fn _ _ _ P1).
    - apply (bij_fn _ _ _ P2).
    - apply (eq_cr (λ x, x ∩ _ = ∅) (bij_dom _ _ _ P1)).
      apply (eq_cr (λ x, _ ∩ x = ∅) (bij_dom _ _ _ P2) P3).
  + apply (eq_cr (λ x, x = A ∪ C) (union2_dom _ _)).
    apply (eq_cr (λ x, x ∪ _ = _) (bij_dom _ _ _ P1)).
    apply (eq_cr (λ x, _ ∪ x = _) (bij_dom _ _ _ P2) (eq_r _)).
  + apply (eq_cr (λ x, x = B ∪ D) (union2_ran _ _)).
    apply (eq_cr (λ x, x ∪ _ = _) (bij_ran _ _ _ P1)).
    apply (eq_cr (λ x, _ ∪ x = _) (bij_ran _ _ _ P2) (eq_r _)).
  + intros x1 x2 yy P6 P7.
    destruct (union2_e _ _ _ P6) as [P8 | P8].
    - destruct (union2_e _ _ _ P7) as [P9 | P9].
      * apply ((bij_sing_rot _ _ _ P1) _ _ _ P8 P9).
      * apply bot_e.
        apply (eq_cr (λ x, yy ∉ x) P5 (empty_i _)).
        apply (inter2_i _ _ _ (ran_i _ _ _ P8) (ran_i _ _ _ P9)).
    - destruct (union2_e _ _ _ P7) as [P9 | P9].
      * apply bot_e.
        apply (eq_cr (λ x, yy ∉ x) P5 (empty_i _)).
        apply (inter2_i _ _ _ (ran_i _ _ _ P9) (ran_i _ _ _ P8)).
      * apply ((bij_sing_rot _ _ _ P2) _ _ _ P8 P9).
Qed.

Lemma union_fval: ∀ f, ∀ H, ∀ x, f ∈ H → fn f → fn (∪(H)) → x ∈ dom(f) 
  → f[x] = (∪(H))[x].
Proof.
  intros f H x P1 P2 P3 P4.
  destruct (dom_e _ _ P4) as [y P5].
  apply (eq_cr (λ y, y = (∪ H)[x]) (fval_i _ _ _ P2 P5)).
  apply eq_s.
  apply fval_i.
  + apply P3.
  + apply union_i.
    exists f.
    split.
    - apply P1.
    - apply P5.
Qed.

Lemma union2_fvall: ∀ F, ∀ G, ∀ x, fn F → fn (F ∪ G) → x ∈ dom(F) 
  → F[x] = (F ∪ G)[x].
Proof. 
  intros F G x P1 P2 P3.
  destruct (dom_e _ _ P3) as [y P4].
  apply (eq_cr (λ y, y = (F ∪ G)[x]) (fval_i _ _ _ P1 P4)).
  apply eq_s.
  apply fval_i.
  + apply P2.
  + apply union2_il.
    apply P4.
Qed.

Lemma union2_fvalr: ∀ F, ∀ G, ∀ x, fn G → fn (F ∪ G) → x ∈ dom(G) 
  → G[x] = (F ∪ G)[x].
Proof. 
  intros F G x P1 P2 P3.
  apply (eq_cl (λ y, G[x] = y[x]) (union2_s G F)).
  pose (eq_cl (λ y, fn y) (union2_s F G) P2) as P4.
  apply (union2_fvall G F x P1 P4 P3).
Qed.
(*----------------------------------------------------------------------------*)

(* Function Mix *)
Lemma fmap_mix: ∀ F, ∀ G, ∀ A, ∀ B, ∀ A', F ∈ A ↦ B → G ∈ A ↦ B → A' ⊆ A
  → F↾A' ∪ G↾(A \ A') ∈ A ↦ B.
Proof.
  intros F G A B A' P1 P2 P3.
  apply fmap_i.
  + apply piecewise_function.
    - apply restr_fn.
      apply (fmap_fn _ _ _ P1).
    - apply restr_fn.
      apply (fmap_fn _ _ _ P2).
    - apply empty_unique.
      intros x P4.
      destruct (inter2_e _ _ _ P4) as [P5 P6].
      destruct (restr_dom_e _ _ _ P5) as [P7 _].
      destruct (restr_dom_e _ _ _ P6) as [P8 _].
      destruct (compl_e _ _ _ P8) as [_ P9].
      apply (P9 P7).
  + apply (eq_cr (λ x, x = A) (union2_dom _ _)).
    apply (eq_cr (λ x, x       ∪ _       = A) (restr_dom _ _)).
    apply (eq_cr (λ x, (x ∩ _) ∪ _       = A) (fmap_dom _ _ _ P1)).
    apply (eq_cr (λ x, _       ∪ x       = A) (restr_dom _ _)).
    apply (eq_cr (λ x, _       ∪ (x ∩ _) = A) (fmap_dom _ _ _ P2)).
    apply (eq_cr (λ x, _       ∪ x       = A) (compl_inter2_2 _ _)).
    apply (eq_cr (λ x, x       ∪ _       = A) (inter2_absorb_r _ _ P3)).
    apply (eq_cr (λ x, x = A) (union2_s _ _)).
    apply (eq_cr (λ x, x = A) (compl_union2_annihilate _ _ P3) (eq_r _)).
  + apply (eq_cr (λ x, x ⊆ B) (union2_ran _ _)).
    apply (union2_sub).
    - apply (sub_t _ _ _ (image_ran _ _) (fmap_ran _ _ _ P1)).
    - apply (sub_t _ _ _ (image_ran _ _) (fmap_ran _ _ _ P2)).
Qed.

(* Exten One Value *)
Lemma rel_exten: ∀ F, ∀ x, ∀ y, rel F → rel (F ∪ `{⟨x, y⟩}).
Proof.
  intros F x y P1.
  apply union2_rel.
  + apply P1.
  + intros s P2.
    exists x.
    exists y.
    apply (eq_s (sing_e _ _ P2)).
Qed.

Lemma sing_val_exten: ∀ F, ∀ x, ∀ y, sing_val F → x ∉ dom(F)
  → sing_val (F ∪ `{⟨x, y⟩}).
Proof.
  intros F x y P1 P2 xx y1 y2 P3 P4.
  destruct (union2_e _ _ _ P3) as [P5 | P5].
  - destruct (union2_e _ _ _ P4) as [P6 | P6].
    * apply (P1 _ _ _ P5 P6).
    * apply bot_e.
      apply P2.
      apply (eq_cr (λ x, x ∈ dom(F)) (opair_eq_el _ _ _ _ (sing_e _ _ P6))).
      apply (dom_i _ _ _ P5).
  - destruct (union2_e _ _ _ P4) as [P6 | P6].
    * apply bot_e.
      apply P2.
      apply (eq_cr (λ x, x ∈ dom(F)) (opair_eq_el _ _ _ _ (sing_e _ _ P5))).
      apply (dom_i _ _ _ P6).
    * apply (eq_cl (λ x, x = y2) (opair_eq_er _ _ _ _ (sing_e _ _ P5))).
      apply (opair_eq_er _ _ _ _ (sing_e _ _ P6)).
Qed.

Lemma sing_rot_exten: ∀ F, ∀ x, ∀ y, sing_rot F → y ∉ ran(F) 
  → sing_rot (F ∪ `{⟨x, y⟩}).
Proof.
  intros F x y P1 P2 x1 x2 yy P3 P4.
  destruct (union2_e _ _ _ P3) as [P5 | P5].
  - destruct (union2_e _ _ _ P4) as [P6 | P6].
    * apply (P1 _ _ _ P5 P6).
    * apply bot_e.
      apply P2.
      apply (eq_cr (λ y, y ∈ ran(F)) (opair_eq_er _ _ _ _ (sing_e _ _ P6))).
      apply (ran_i _ _ _ P5).
  - destruct (union2_e _ _ _ P4) as [P6 | P6].
    * apply bot_e.
      apply P2.
      apply (eq_cr (λ y, y ∈ ran(F)) (opair_eq_er _ _ _ _ (sing_e _ _ P5))).
      apply (ran_i _ _ _ P6).
    * apply (eq_cl (λ x, x = x2) (opair_eq_el _ _ _ _ (sing_e _ _ P5))).
      apply (opair_eq_el _ _ _ _ (sing_e _ _ P6)).
Qed.

Lemma dom_exten: ∀ F, ∀ x, ∀ y, dom(F ∪ `{⟨x, y⟩}) = dom(F) ∪ `{x}.
Proof.
  intros F x y.
  apply sub_a.
  split.
  + intros xx P1.
    destruct (dom_e _ _ P1) as [yy P2].
    destruct (union2_e _ _ _ P2) as [P3 | P3].
    - apply union2_il.
      apply (dom_i _ _ _ P3).
    - apply union2_ir.
      apply sing_i2.
      apply (eq_s (opair_eq_el _ _ _ _ (sing_e _ _ P3))).
  + intros xx P1.
    destruct (union2_e _ _ _ P1) as [P2 | P2].
    - destruct (dom_e _ _ P2) as [yy P3].
      apply (dom_i _ _ yy).
      apply union2_il.
      apply P3.
    - apply (dom_i _ _ y).
      apply union2_ir.
      apply (eq_cr (λ x, ⟨xx, y⟩ ∈ `{⟨x, y⟩}) (sing_e _ _ P2)).
      apply sing_i.
Qed.

Lemma ran_exten: ∀ F, ∀ x, ∀ y, ran(F ∪ `{⟨x, y⟩}) = ran(F) ∪ `{y}.
Proof.
  intros F x y.
  apply sub_a.
  split.
  + intros yy P1.
    destruct (ran_e _ _ P1) as [xx P2].
    destruct (union2_e _ _ _ P2) as [P3 | P3].
    - apply union2_il.
      apply (ran_i _ _ _ P3).
    - apply union2_ir.
      apply sing_i2.
      apply (eq_s (opair_eq_er _ _ _ _ (sing_e _ _ P3))).
  + intros yy P1.
    destruct (union2_e _ _ _ P1) as [P2 | P2].
    - destruct (ran_e _ _ P2) as [xx P3].
      apply (ran_i _ xx).
      apply union2_il.
      apply P3.
    - apply (ran_i _ x).
      apply union2_ir.
      apply (eq_cr (λ y, ⟨x, yy⟩ ∈ `{⟨x, y⟩}) (sing_e _ _ P2)).
      apply sing_i.
Qed.

Lemma fn_exten: ∀ F, ∀ x, ∀ y, fn F → x ∉ dom(F) → fn (F ∪ `{⟨x, y⟩}).
Proof.
  intros F x y [P1 P2] P3.
  split.
  + apply (rel_exten _ _ _ P1).
  + apply (sing_val_exten _ _ _ P2 P3).
Qed.

Lemma fmap_exten: ∀ F, ∀ A, ∀ B, ∀ x, ∀ y, x ∉ A → F ∈ A ↦ B 
  → (F ∪ `{⟨x, y⟩}) ∈ (A ∪ `{x}) ↦ (B ∪ `{y}).
Proof.
  intros F A B x y P1 P2.
  apply fmap_i.
  + pose (eq_cr (λ y, x ∉ y) (fmap_dom _ _ _ P2) P1) as Q1.
    apply (fn_exten _ _ _ (fmap_fn _ _ _ P2) Q1).
  + apply (eq_cl (λ s, _ = s ∪ _) (fmap_dom _ _ _ P2)).
    apply dom_exten.
  + intros yy P5.
    destruct (ran_e _ _ P5) as [xx P6].
    destruct (union2_e _ _ _ P6) as [P7 | P7].
    - apply union2_il.
      apply (fmap_ran _ _ _ P2).
      apply (ran_i _ _ _ P7).
    - apply union2_ir.
      apply (eq_cr (λ y, yy ∈ `{y}) (opair_eq_er _ _ _ _ (sing_e _ _ P7))).
      apply sing_i.
Qed.

Lemma inj_exten: ∀ F, ∀ A, ∀ B, ∀ x, ∀ y, F ∈ A ↦ⁱ B → x ∉ A → y ∉ ran(F) 
  → (F ∪ `{⟨x, y⟩}) ∈ (A ∪ `{x}) ↦ⁱ (B ∪ `{y}).
Proof.
  intros F A B x y P1 P2 P3.
  apply inj_i2.
  + apply (fmap_exten _ _ _ _ _ P2 (inj_fmap _ _ _ P1)).
  + apply (sing_rot_exten _ _ _ (inj_sing_rot _ _ _ P1) P3).
Qed.

Lemma surj_exten: ∀ F, ∀ A, ∀ B, ∀ x, ∀ y, F ∈ A ↦ˢ B → x ∉ A
  → (F ∪ `{⟨x, y⟩}) ∈ (A ∪ `{x}) ↦ˢ (B ∪ `{y}).
Proof.
  intros F A B x y P1 P2.
  apply surj_i2.
  + apply (fmap_exten _ _ _ _ _ P2 (surj_fmap _ _ _ P1)).
  + apply (eq_cl (λ s, _ = s ∪ _) (surj_ran _ _ _ P1)).
    apply ran_exten.
Qed.

Lemma bij_exten: ∀ F, ∀ A, ∀ B, ∀ x, ∀ y, F ∈ A ↦ᵇ B → x ∉ A → y ∉ B 
  → (F ∪ `{⟨x, y⟩}) ∈ (A ∪ `{x}) ↦ᵇ (B ∪ `{y}).
Proof.
  intros F A B x y P1 P2 P3.
  destruct (bij_e _ _ _ P1) as [P4 P5].
  apply bij_i3.
  + apply (surj_exten _ _ _ _ _ P4 P2).
  + apply (inj_exten _ _ _ _ _ P5 P2).
    apply (eq_cr (λ x, y ∉ x) (bij_ran _ _ _ P1)).
    apply P3.
Qed.
(*----------------------------------------------------------------------------*)

(* Kick One Value *)
Lemma rel_kick: ∀ F, ∀ x, ∀ y, rel F → rel (F \ `{⟨x, y⟩}).
Proof.
  intros F x y P1 xx P2.
  destruct (compl_e _ _ _ P2) as [P3 _].
  apply (P1 _ P3).
Qed.

Lemma sing_val_kick: ∀ F, ∀ x, ∀ y, sing_val F → sing_val (F \ `{⟨x, y⟩}).
Proof.
  intros F x y P1 xx y1 y2 P2 P3.
  destruct (compl_e _ _ _ P2) as [P4 _].
  destruct (compl_e _ _ _ P3) as [P5 _].
  apply (P1 _ _ _ P4 P5).
Qed.

Lemma sing_rot_kick: ∀ F, ∀ x, ∀ y, sing_rot F → sing_rot (F \ `{⟨x, y⟩}).
Proof.
  intros F x y P1 xx y1 y2 P2 P3.
  destruct (compl_e _ _ _ P2) as [P4 _].
  destruct (compl_e _ _ _ P3) as [P5 _].
  apply (P1 _ _ _ P4 P5).
Qed.

Lemma dom_kick: ∀ F, ∀ x, fn F → dom(F \ `{⟨x, F[x]⟩}) = dom(F) \ `{x}.
Proof.
  intros F x P1.
  apply sub_a.
  split.
  + intros xx P2.
    destruct (dom_e _ _ P2) as [yy P3].
    destruct (compl_e _ _ _ P3) as [P4 P5].
    apply compl_i.
    - apply (dom_i _ _ _ P4).
    - intros P6.
      apply P5.
      apply (eq_cl (λ xx, ⟨xx, yy⟩ ∈ `{⟨x, F[x]⟩}) (sing_e _ _ P6)).
      pose (eq_cr (λ xx, ⟨xx, yy⟩ ∈ F) (sing_e _ _ P6) P4) as P7.
      apply (eq_cl (λ yy, ⟨x, yy⟩ ∈ `{⟨x, F[x]⟩}) (fval_i _ _ _ P1 P7)).
      apply sing_i.
  + intros xx P2.
    destruct (compl_e _ _ _ P2) as [P3 P4].
    destruct (dom_e _ _ P3) as [yy P5].
    apply (dom_i _ _ yy).
    apply compl_i.
    - apply P5.
    - intros P6.
      apply P4.
      apply (eq_cr (λ x, xx ∈ `{x}) (opair_eq_el _ _ _ _ (sing_e _ _ P6))).
      apply sing_i.
Qed.

Lemma ran_kick: ∀ F, ∀ x, fn F → sing_rot F → x ∈ dom(F) 
  → ran(F \ `{⟨x, F[x]⟩}) = ran(F) \ `{F[x]}.
Proof.
  intros F x P1 P2 P3.
  apply sub_a.
  split.
  + intros yy Q1.
    destruct (ran_e _ _ Q1) as [xx Q2].
    destruct (compl_e _ _ _ Q2) as [Q3 Q4].
    apply compl_i.
    - apply (ran_i _ _ _ Q3).
    - intros Q5.
      apply Q4.
      apply sing_i2.
      apply opair_eq_i.
      * pose (fval_e1 _ _ _ (sing_e _ _ Q5) P1 P3) as Q6.
        apply (P2 _ _ _ Q3 Q6).
      * apply (eq_s (sing_e _ _ Q5)).
  + intros yy Q1.
    destruct (compl_e _ _ _ Q1) as [Q2 Q3].
    destruct (ran_e _ _ Q2) as [xx Q4].
    apply (ran_i _ xx).
    apply compl_i.
    - apply Q4.
    - intros Q5.
      apply Q3.
      apply sing_i2.
      apply (eq_s (opair_eq_er _ _ _ _ (sing_e _ _ Q5))).
Qed.

Lemma fn_kick: ∀ F, ∀ x, fn F → fn (F \ `{⟨x, F[x]⟩}).
Proof.
  intros F x [P1 P2].
  split.
  + apply (rel_kick _ _ _ P1).
  + apply (sing_val_kick _ _ _ P2).
Qed.

Lemma fmap_kick: ∀ F, ∀ A, ∀ B, ∀ x, F ∈ A ↦ B 
  → (F \ `{⟨x, F[x]⟩}) ∈ (A \ `{x}) ↦ B.
Proof.
  intros F A B x P1.
  apply fmap_i.
  + apply (fn_kick _ _ (fmap_fn _ _ _ P1)).
  + apply (eq_cl (λ s, _ = s \ `{x}) (fmap_dom _ _ _ P1)).
    apply (dom_kick _ _ (fmap_fn _ _ _ P1)).
  + intros yy P4.
    destruct (ran_e _ _ P4) as [xx P5].
    destruct (compl_e _ _ _ P5) as [P6 _].
    apply (fmap_ran _ _ _ P1).
    apply (ran_i _ _ _ P6).
Qed.

Lemma inj_kick: ∀ F, ∀ A, ∀ B, ∀ x, F ∈ A ↦ⁱ B → x ∈ A
  → (F \ `{⟨x, F[x]⟩}) ∈ (A \ `{x}) ↦ⁱ(B \ `{F[x]}).
Proof.
  intros F A B x P1 P2.
  pose (fmap_kick _ _ _ x (inj_fmap _ _ _ P1)) as P3.
  apply inj_i.
  + apply (fmap_fn _ _ _ P3).
  + apply (fmap_dom _ _ _ P3).
  + intros yy Q1.
    destruct (ran_e _ _ Q1) as [xx Q2].
    destruct (compl_e _ _ _ Q2) as [Q3 Q4].
    apply compl_i.
    - apply (inj_ran _ _ _ P1).
      apply (ran_i _ _ _ Q3).
    - intros Q5.
      apply Q4.
      apply sing_i2.
      apply opair_eq_i.
      * apply (fval_inj _ _ _ _ _ P1).
        ++apply (eq_cl (λ x, _ ∈ x) (inj_dom _ _ _ P1) (dom_i _ _ _ Q3)).
        ++apply P2.
        ++apply (eq_t (fval_i _ _ _ (inj_fn _ _ _ P1) Q3) 
            (eq_s (sing_e _ _ Q5))).
      * apply (eq_s (sing_e _ _ Q5)).
  + apply (sing_rot_kick _ _ _ (inj_sing_rot _ _ _ P1)).
Qed.
              
(*Lemma surj_kick: ∀ F, ∀ A, ∀ B, ∀ x, surj F A B → x ∉ A*)
  (*→ surj (F \ `{⟨x, F[x]⟩}) (A \ `{x}) B.*)

Lemma bij_kick: ∀ F, ∀ A, ∀ B, ∀ x, F ∈ A ↦ᵇ B → x ∈ A →
  (F \ `{⟨x, F[x]⟩}) ∈ (A \ `{x}) ↦ᵇ (B \ `{F[x]}).
Proof.
  intros F A B x P1 P2.
  apply bij_i.
  + apply (fn_kick _ _ (bij_fn _ _ _ P1)).
  + apply (eq_cl (λ s, _ = s \ _) (bij_dom _ _ _ P1)).
    apply (dom_kick _ _ (bij_fn _ _ _ P1)).
  + apply (eq_cl (λ s, _ = s \ _) (bij_ran _ _ _ P1)).
    apply (ran_kick _ _ (bij_fn _ _ _ P1) (bij_sing_rot _ _ _ P1)).
    apply (eq_cr (λ y, x ∈ y) (bij_dom _ _ _ P1) P2).
  + apply (sing_rot_kick _ _ _ (bij_sing_rot _ _ _ P1)).
Qed.

Lemma kick_fval: ∀ F, ∀ x1, ∀ x2, fn F → x2 ∈ dom(F) → x1 ≠ x2
  → (F \ `{⟨x1, F[x1]⟩})[x2] = F[x2].
Proof.
  intros F x1 x2 P1 P2 P3.
  apply fval_i.
  + apply (fn_kick _ _ P1).
  + apply compl_i.
    - apply (fval_i2 _ _ P1 P2).
    - intros P4.
      apply P3.
      apply (opair_eq_el _ _ _ _ (sing_e _ _ P4)).
Qed.
(*----------------------------------------------------------------------------*)

(* Function Swap *)
Lemma fn_swap_ran: ∀ F, ∀ x1, ∀ x2, fn F → x1 ∈ dom(F) → x2 ∈ dom(F) → 
  ran(F \ `{⟨x1, F[x1]⟩} \ `{⟨x2, F[x2]⟩} ∪ `{⟨x2, F[x1]⟩} ∪ `{⟨x1, F[x2]⟩})
    = ran(F).
Proof.
  intros F x1 x2 P1 P2 P3.
  apply sub_a.
  split.
  + intros y P4.
    destruct (ran_e _ _ P4) as [x P5].
    destruct (union2_e _ _ _ P5) as [P6 | P6].
    - destruct (union2_e _ _ _ P6) as [P7 | P7].
      * destruct (compl_e _ _ _ P7) as [P8 _].
        destruct (compl_e _ _ _ P8) as [P9 _].
        apply (ran_i _ _ _ P9).
      * apply (eq_cl (λ y, y ∈ ran(F)) (opair_eq_er _ _ _ _ (sing_e _ _ P7))).
        apply (fval_ran _ _ P1 P2).
    - apply (eq_cl (λ y, y ∈ ran(F)) (opair_eq_er _ _ _ _ (sing_e _ _ P6))).
      apply (fval_ran _ _ P1 P3).
  + intros y P4.
    destruct (ran_e _ _ P4) as [x P5].
    destruct (LEM (x = x2)) as [P6 | P6].
    - apply (ran_i _ x1).
      apply union2_ir.
      apply sing_i2.
      apply (opair_eq_i _ _ _ _ (eq_r _)).
      apply eq_s.
      apply (fval_i _ _ _ P1).
      apply (eq_cl (λ x, ⟨x, y⟩ ∈ F) P6 P5).
    - destruct (LEM (x = x1)) as [P7 | P7].
      * apply (ran_i _ x2).
        apply union2_il.
        apply union2_ir.
        apply sing_i2.
        apply (opair_eq_i _ _ _ _ (eq_r _)).
        apply eq_s.
        apply (fval_i _ _ _ P1).
        apply (eq_cl (λ x, ⟨x, y⟩ ∈ F) P7 P5).
      * apply (ran_i _ x).
        apply union2_il.
        apply union2_il.
        apply compl_i.
        ++apply compl_i.
          --apply P5.
          --intros P8.
            apply P7.
            apply (eq_s (opair_eq_el _ _ _ _ (sing_e _ _ P8))).
        ++intros P8.
          apply P6.
          apply (eq_s (opair_eq_el _ _ _ _ (sing_e _ _ P8))).
Qed.

Lemma fn_swap_inj: ∀ F, ∀ A, ∀ B, ∀ x1, ∀ x2, F ∈ A ↦ⁱ B → x1 ∈ A → x2 ∈ A 
  → x1 ≠ x2 
  → (F \ `{⟨x1, F[x1]⟩} \ `{⟨x2, F[x2]⟩} ∪ `{⟨x2, F[x1]⟩} ∪ `{⟨x1, F[x2]⟩})
    ∈ A ↦ⁱ B.
Proof.
  intros F A B x1 x2 P1 P2 P3 P4.
  pose (inj_fn _ _ _ P1) as P5.
  pose (inj_dom _ _ _ P1) as P6.
  pose (inj_ran _ _ _ P1) as P7.
  pose (inj_kick _ _ _ _ P1 P2) as Q1.
  assert (x2 ∈ A \ `{x1}) as Q2.
  { apply compl_i.
    + apply P3.
    + intros R1.
      apply P4.
      apply (sing_e _ _ R1). }
  pose (inj_kick _ _ _ _ Q1 Q2) as Q3.
  assert ((F \ `{⟨x1, F[x1]⟩})[x2] = F[x2]) as Q4.
  { apply kick_fval.
    + apply P5.
    + apply (eq_cr (λ x, x2 ∈ x) P6 P3).
    + apply P4. }
  pose (eq_cl (λ x, (F \ `{⟨x1, F[x1]⟩} \ `{⟨x2, x⟩})
    ∈ (A \ `{x1} \ `{x2}) ↦ⁱ (B \ `{F[x1]} \ `{x})) Q4 Q3) as Q5.
  assert (x2 ∉ (A \ `{x1} \ `{x2})) as Q6.
  { intros R1.
    destruct (compl_e _ _ _ R1) as [_ R2].
    apply R2.
    apply sing_i. }
  assert (∀ F, ∀ A, ∀ B, ∀ x, F ∈ A ↦ⁱ B → x ∉ B → x ∉ ran(F)) as Q7.
  { intros F0 A0 B0 x R1 R2 R3.
    apply R2.
    apply ((inj_ran _ _ _ R1) _ R3). }
  assert (F[x1] ∉ (B \ `{F[x1]} \ `{F[x2]})) as Q8.
  { intros R1.
    destruct (compl_e _ _ _ R1) as [R2 _].
    destruct (compl_e _ _ _ R2) as [_ R3].
    apply R3.
    apply sing_i. }
  pose (inj_exten _ _ _ _ _ Q5 Q6 (Q7 _ _ _ _ Q5 Q8)) as Q9.
  assert (A \ `{x1} \ `{x2} ∪ `{x2} = A \ `{x1}) as Q10.
  { apply compl_union2_annihilate.
    intros x R1.
    pose (sing_e _ _ R1) as R2.
    apply compl_i.
    + apply (eq_cl (λ x, x ∈ A) R2 P3).
    + intros R3.
      apply P4.
      apply (eq_t (sing_e _ _ R3) (eq_s R2)). }
  assert (B \ `{F[x2]} \ `{F[x1]} ∪ `{F[x1]} = B \ `{F[x2]}) as Q11.
  { apply compl_union2_annihilate.
    intros x R1.
    pose (sing_e _ _ R1) as R2.
    apply compl_i.
    + apply (eq_cl (λ x, x ∈ B) R2).
      apply P7.
      apply (fval_ran _ _ P5).
      apply (eq_cr (λ x, x1 ∈ x) P6 P2).
    + intros R3.
      apply P4.
      apply (fval_inj _ _ _ _ _ P1 P2 P3).
      - apply (eq_t (sing_e _ _ R1) (eq_s (sing_e _ _ R3))). }
  pose (eq_cl (λ x, _ ∈ x ↦ⁱ _) Q10 Q9) as Q12.
  pose (eq_cl (λ x, _ ∈ _ ↦ⁱ (x ∪ _)) (compl_exchange _ _ _) Q12) as Q13.
  pose (eq_cl (λ x, _ ∈ _ ↦ⁱ x) Q11 Q13) as Q14.
  assert (x1 ∉ A \ `{x1}) as Q15.
  { intros R1.
    destruct (compl_e _ _ _ R1) as [_ R2].
    apply R2.
    apply sing_i. }
  assert (F[x2] ∉ (B \ `{F[x2]})) as Q16.
  { intros R1.
    destruct (compl_e _ _ _ R1) as [_ R2].
    apply R2.
    apply sing_i. }
  pose (inj_exten _ _ _ _ _ Q14 Q15 (Q7 _ _ _ _ Q14 Q16)) as Q17.
  assert (A \ `{x1} ∪ `{x1} = A) as Q18.
  { apply compl_union2_annihilate.
    intros x R1.
    pose (sing_e _ _ R1) as R2.
    apply (eq_cl (λ x, x ∈ A) R2 P2). }
  assert (B \ `{F[x2]} ∪ `{F[x2]} = B) as Q19.
  { apply compl_union2_annihilate.
    intros x R1.
    pose (sing_e _ _ R1) as R2.
    apply (eq_cl (λ x, x ∈ B) R2).
    apply P7.
    apply (fval_ran _ _ P5).
    apply (eq_cr (λ x, x2 ∈ x) P6 P3). }
  pose (eq_cl (λ x, _ ∈ x ↦ⁱ _) Q18 Q17) as Q20.
  apply (eq_cl (λ x, _ ∈ A ↦ⁱ x) Q19 Q20).
Qed.

Lemma fn_swap_fval: ∀ F, ∀ A, ∀ B, ∀ x1, ∀ x2, F ∈ A ↦ⁱ B → x1 ∈ A → x2 ∈ A 
  → x1 ≠ x2 
  → (F \ `{⟨x1, F[x1]⟩} \ `{⟨x2, F[x2]⟩} ∪ `{⟨x2, F[x1]⟩} ∪ `{⟨x1, F[x2]⟩})[x1]
    = F[x2].
Proof.
  intros F A B x1 x2 P1 P2 P3 P4.
  apply fval_i.
  + apply (inj_fn _ _ _ (fn_swap_inj _ _ _ _ _ P1 P2 P3 P4)).
  + apply union2_ir.
    apply sing_i.
Qed.
