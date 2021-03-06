Require Import Init.Init.
Require Import Relation.Relation_.
Require Import Relation.Function.

Definition id (A: J)      := {s: A ⨉ A| ∃ x, s = ⟨x, x⟩}.
Definition const (A c: J) := A ⨉ `{c}.


(* Empty Function *)
Lemma empty_is_rel: rel ∅.
Proof.
  intros x P1.
  apply bot_e.
  apply (empty_i _ P1).
Qed.

Lemma empty_is_sing_val: sing_val ∅.
Proof.
  intros a b1 b2 P1 P2.
  apply bot_e.
  apply (empty_i _ P1).
Qed.

Lemma empty_is_sing_rot: sing_rot ∅.
Proof.
  intros a1 a2 b P1 P2.
  apply bot_e.
  apply (empty_i _ P1).
Qed.

Lemma empty_is_fn: fn ∅.
Proof.
  split.
  + apply empty_is_rel.
  + apply empty_is_sing_val.
Qed.

Lemma empty_dom: dom(∅) = ∅.
Proof.
  apply sub_a.
  split.
  + intros x P1.
    destruct (dom_e _ _ P1) as [y P2].
    apply bot_e.
    apply (empty_i _ P2).
  + intros x P1.
    apply bot_e.
    apply (empty_i _ P1).
Qed.

Lemma empty_ran: ran(∅) = ∅.
Proof.
  apply sub_a.
  split.
  + intros y P1.
    destruct (ran_e _ _ P1) as [x P2].
    apply bot_e.
    apply (empty_i _ P2).
  + intros y P1.
    apply bot_e.
    apply (empty_i _ P1).
Qed.

Lemma empty_fmap: ∀ B, ∅ ∈ ∅ ↦ B.
Proof.
  intros B.
  apply fmap_i.
  + apply empty_is_fn.
  + apply empty_dom.
  + apply (eq_cr (λ y, y ⊆ B) empty_ran).
    apply empty_i1.
Qed.

Lemma empty_is_inj: ∀ B, ∅ ∈ ∅ ↦ⁱ B.
Proof.
  intros B.
  apply inj_i2.
  + apply empty_fmap.
  + apply empty_is_sing_rot.
Qed.

Lemma fspace_empty_dom: ∀ B, ∅ ↦ B = `{∅}.
Proof.
  intros B.
  apply sub_a.
  split.
  + intros x P1.
    assert (x = ∅) as P2.
    { apply empty_unique.
      intros s P2.
      destruct (fmap_fn _ _ _ P1) as [P3 _].
      destruct (P3 _ P2) as [p [q P4]].
      apply bot_e.
      apply (empty_i p).
      apply (eq_cl _ (fmap_dom _ _ _ P1)).
      apply (dom_i _ _ _ (eq_cl (λ s, s ∈ x) P4 P2)). }
    apply (eq_cr (λ x, x ∈ `{ ∅}) P2).
    apply sing_i.
  + intros x P1.
    apply (eq_cl (λ x, x ∈ _) (sing_e _ _ P1)).
    apply fmap_i.
    - apply empty_is_fn.
    - apply empty_dom.
    - apply (eq_cr (λ x, x ⊆ B) empty_ran).
      apply empty_i1.
Qed.

Lemma fspace_empty_ran: ∀ A, A ≠ ∅ → A ↦ ∅ = ∅.
Proof.
  intros A P1.
  apply sub_a.
  split.
  + intros x P2.
    destruct (nempty_ex _ P1) as [a Q1].
    destruct (dom_e _ _ (eq_cr _ (fmap_dom _ _ _ P2) Q1)) as [b Q2].
    apply bot_e.
    apply (empty_i b).
    apply (fmap_ran _ _ _ P2).
    apply (ran_i _ _ _ Q2).
  + intros x P2.
    apply bot_e.
    apply (empty_i x).
    apply P2.
Qed.

Lemma empty_dom_empty_ran: ∀ F, fn F → dom(F) = ∅ → ran(F) = ∅.
Proof. 
  intros F P1 P2.
  pose (eq_cl (λ x, F ∈ x ↦ ran(F)) P2 (fmap_r _ P1)) as P3.
  pose (eq_cl (λ x, F ∈ x) (fspace_empty_dom _) P3) as P4.
  apply (eq_cl (λ x, ran(x) = ∅) (sing_e _ _ P4)).
  apply empty_ran.
Qed.

Lemma nempty_dom_nempty_ran: ∀ F, fn F → dom(F) ≠ ∅ → ran(F) ≠ ∅.
Proof. 
  intros F P1 P2.
  destruct (nempty_ex _ P2) as [x P3].
  destruct (dom_e _ _ P3) as [y P4].
  apply ex_nempty.
  exists y.
  apply (ran_i _ _ _ P4).
Qed.
(*----------------------------------------------------------------------------*)

(* Single Pair Function *)
Lemma sing_pair_is_fn: ∀ x, ∀ y, fn `{⟨x, y⟩}.
Proof.
  intros x y.
  split.
  + intros s P1.
    exists x.
    exists y.
    symmetry.
    apply (sing_e _ _ P1).
  + intros a0 b1 b2 P1 P2.
    apply (eq_t (eq_s (opair_eq_er _ _ _ _ (sing_e _ _ P1)))
                (opair_eq_er _ _ _ _ (sing_e _ _ P2))).
Qed.

Lemma sing_pair_dom: ∀ x, ∀ y, dom(`{⟨x, y⟩}) = `{x}.
Proof. 
  intros x y.
  apply sub_a.
  split.
  + intros s P1.
    destruct (dom_e _ _ P1) as [t P2].
    apply (sing_i2 _ _ (eq_s (opair_eq_el _ _ _ _ (sing_e _ _ P2)))).
  + intros s P1.
    apply (dom_i _ _ y).
    apply sing_i2.
    apply (eq_cr (λ x, ⟨s, y⟩ = ⟨x, y⟩) (sing_e _ _ P1)).
    apply eq_r.
Qed.

Lemma sing_pair_ran: ∀ x, ∀ y, ran(`{⟨x, y⟩}) = `{y}.
Proof. 
  intros x y.
  apply sub_a.
  split.
  + intros s P1.
    destruct (ran_e _ _ P1) as [t P2].
    apply (sing_i2 _ _ (eq_s (opair_eq_er _ _ _ _ (sing_e _ _ P2)))).
  + intros s P1.
    apply (ran_i _ x).
    apply (sing_i2).
    apply (eq_cr (λ y, ⟨x, s⟩ = ⟨x, y⟩) (sing_e _ _ P1)).
    apply eq_r.
Qed.

Lemma sing_pair_fval: ∀ x, ∀ y, `{⟨x, y⟩}[x] = y.
Proof.
  intros x y.
  apply fval_i.
  + apply sing_pair_is_fn.
  + apply sing_i.
Qed.

Lemma sing_pair_bij: ∀ x, ∀ y, `{⟨x, y⟩} ∈ `{x} ↦ᵇ `{y}.
Proof.
  intros x y.
  apply bij_i.
  + apply sing_pair_is_fn.
  + apply sing_pair_dom.
  + apply sing_pair_ran.
  + intros x1 x2 yy P1 P2.
    apply (eq_t (eq_s (opair_eq_el _ _ _ _ (sing_e _ _ P1))) 
      (opair_eq_el _ _ _ _ (sing_e _ _ P2))).
Qed.
(*----------------------------------------------------------------------------*)

(* Identify Function *)
Lemma id_i: ∀ A, ∀ x, x ∈ A → ⟨x, x⟩ ∈ id A.
Proof.
  intros A x P1.
  apply sub_i.
  + apply (cp_i _ _ _ _ P1 P1). 
  + exists x.
    apply eq_r.
Qed.

Lemma id_e: ∀ A, ∀ s, s ∈ id A → ∃ x, x ∈ A ∧ s = ⟨x, x⟩.
Proof. 
  intros A s P1.
  destruct (sub_e _ _ _ P1) as [P2 [x P3]].
  exists x.
  split.
  + destruct (cp_e2 _ _ _ _ (eq_cl (λ x, x ∈ A ⨉ A) P3 P2)) as [P4 _].
    apply P4.
  + apply P3.
Qed.

Lemma id_e2: ∀ A, ∀ x, ∀ y, ⟨x, y⟩ ∈ id A → x = y ∧ x ∈ A ∧ y ∈ A.
Proof.
  intros A x y P1.
  destruct (id_e _ _ P1) as [a [P2 P3]].
  repeat split.
  + apply (eq_cr (λ y, x = y) (opair_eq_er _ _ _ _ P3)).
    apply (opair_eq_el _ _ _ _ P3).
  + apply (eq_cr (λ x, x ∈ A) (opair_eq_el _ _ _ _ P3)).
    apply P2.
  + apply (eq_cr (λ y, y ∈ A) (opair_eq_er _ _ _ _ P3)).
    apply P2.
Qed.

Lemma id_is_rel: ∀ A, rel (id A).
Proof.
  intros A x P1.
  destruct (id_e _ _ P1) as [s [_ P2]].
  exists s.
  exists s.
  apply P2.
Qed.

Lemma id_is_sing_val: ∀ A, sing_val (id A).
Proof.
  intros A a b1 b2 P1 P2.
  destruct (id_e _ _ P1) as [s1 [_ P3]].
  destruct (id_e _ _ P2) as [s2 [_ P4]].
  apply (eq_t (opair_eq_er _ _ _ _ P3)).
  apply (eq_t (eq_s (opair_eq_el _ _ _ _ P3))).
  apply (eq_cl _ (eq_s (opair_eq_er _ _ _ _ P4))).
  apply (opair_eq_el _ _ _ _ P4).
Qed.

Lemma id_is_sing_rot: ∀ A, sing_rot (id A).
Proof.
  intros A a1 a2 b P1 P2.
  destruct (id_e _ _ P1) as [s1 [_ P3]].
  destruct (id_e _ _ P2) as [s2 [_ P4]].
  apply (eq_t (opair_eq_el _ _ _ _ P3)).
  apply (eq_t (eq_s (opair_eq_er _ _ _ _ P3))).
  apply (eq_cl _ (eq_s (opair_eq_el _ _ _ _ P4))).
  apply (opair_eq_er _ _ _ _ P4).
Qed.

Lemma id_is_fn: ∀ A, fn (id A).
Proof.
  intros A.
  split.
  + apply id_is_rel.
  + apply id_is_sing_val.
Qed.

Lemma id_dom: ∀ A, dom(id A) = A.
Proof.
  intros A.
  apply sub_a.
  split.
  + intros x P1.
    destruct (dom_e _ _ P1) as [y P2].
    destruct (id_e _ _ P2) as [s [P3 P4]].
    apply (eq_cr (λ x, x ∈ A) (opair_eq_el _ _ _ _ P4)).
    apply P3.
  + intros x P1. 
    apply (dom_i _ _ _ (id_i A x P1)).
Qed.

Lemma id_ran: ∀ A, ran(id A) = A.
Proof.
  intros A.
  apply sub_a.
  split.
  + intros y P1.
    destruct (ran_e _ _ P1) as [x P2].
    destruct (id_e _ _ P2) as [s [P3 P4]].
    apply (eq_cr (λ y, y ∈ A) (opair_eq_er _ _ _ _ P4)).
    apply P3.
  + intros y P1.
    apply (ran_i _ _ _ (id_i A y P1)).
Qed.

Lemma id_fmap: ∀ A, (id A) ∈ A ↦ A.
Proof.
  intros A.
  apply fmap_i.
  + apply id_is_fn.
  + apply id_dom.
  + apply (eq_cr (λ x, x ⊆ A) (id_ran A)).
    apply sub_r.
Qed.

Lemma id_is_inj: ∀ A, (id A) ∈ A ↦ⁱ A.
Proof.
  intros A.
  apply inj_i2.
  + apply id_fmap.
  + apply id_is_sing_rot.
Qed.

Lemma id_inj_exten: ∀ A, ∀ B, A ⊆ B → (id A) ∈ A ↦ⁱ B.
Proof.
  intros A B P1.
  apply (inj_ran_exten _ _ A).
  + apply id_is_inj.
  + apply P1.
Qed.

Lemma id_fval: ∀ A, ∀ x, x ∈ A → (id A)[x] = x.
Proof.
  intros A x P1.
  apply fval_i.
  + apply (id_is_fn A).
  + apply (id_i _ _ P1).
Qed.

Lemma id_is_surj: ∀ A, (id A) ∈ A ↦ˢ A.
Proof.
  intros A.
  apply surj_i2.
  + apply id_fmap.
  + apply (eq_cr (λ x, x = A) (id_ran _) (eq_r _)).
Qed.

Lemma id_is_bij: ∀ A, (id A) ∈ A ↦ᵇ A.
Proof.
  intros A.
  apply bij_i3.
  + apply id_is_surj.
  + apply id_is_inj.
Qed.

Lemma id_inv: ∀ A, id A = (id A)⁻¹.
Proof.
  intros A.
  apply sub_a.
  split.
  + intros x P1.
    destruct (id_e _ _ P1) as [y [_ P2]].
    apply (eq_cr (λ x, x ∈ inv (id A)) P2).
    apply inv_i.
    apply (eq_cl (λ x, x ∈ id A) P2).
    apply P1.
  + intros x P1.
    destruct (inv_rel (id A) x P1) as [a [b P2]].
    pose (eq_cl (λ x, x ∈ inv (id A)) P2 P1) as P3.
    destruct (id_e _ _ (inv_e _ _ _ P3)) as [z [P4 P5]].
    apply (eq_cr (λ x, x ∈ id A) P2).
    apply (eq_cr (λ x, x ∈ id A) (opair_eq_swap _ _ _ _ P5)).
    apply (id_i _ _ P4).
Qed.

Lemma id_image: ∀ A, (id A)⟦A⟧ = A.
Proof.
  intros A.
  apply sub_a.
  split.
  intros y P1.
  + destruct (image_e _ _ _ P1) as [x [P2 P3]].
    destruct (id_e2 _ _ _ P2) as [_ [_ P4]].
    apply P4.
  + intros x P1.
    apply image_i.
    exists x.
    split.
    - apply (id_i _ _ P1).
    - apply P1.
Qed.
(*----------------------------------------------------------------------------*)
    
(* Constant Function *)
Lemma const_i: ∀ A, ∀ c, ∀ x, x ∈ A → ⟨x, c⟩ ∈ const A c.
Proof.
  intros A c x P1.
  apply cp_i.
  + apply P1.
  + apply sing_i.
Qed.

Lemma const_e: ∀ A, ∀ c, ∀ s, s ∈ const A c → ∃ x, x ∈ A ∧ s = ⟨x, c⟩.
Proof.
  intros A c s P1.
  destruct (cp_e _ _ _ P1) as [a [b [P2 [P3 P4]]]].
  exists a.
  split.
  + apply P2.
  + apply (eq_cr (λ x, s = ⟨a, x⟩) (sing_e _ _ P3)).
    apply P4.
Qed.

Lemma const_is_rel: ∀ A, ∀ c, rel (const A c).
Proof.
  intros A c x P1.
  destruct (const_e _ _ _ P1) as [a [_ P2]].
  exists a.
  exists c.
  apply P2.
Qed.

Lemma const_is_sing_val: ∀ A, ∀ c, sing_val (const A c).
Proof. 
  intros A c a b1 b2 P1 P2.
  destruct (const_e _ _ _ P1) as [a1 [_ P3]].
  destruct (const_e _ _ _ P2) as [a2 [_ P4]].
  apply (eq_t (opair_eq_er _ _ _ _ P3)).
  apply (eq_s (opair_eq_er _ _ _ _ P4)).
Qed.

Lemma const_is_fn: ∀ A, ∀ c, fn (const A c).
Proof.
  intros A c.
  split.
  + apply const_is_rel. 
  + apply const_is_sing_val. 
Qed.

Lemma const_dom: ∀ A, ∀ c, dom(const A c) = A.
Proof.
  intros A c.
  apply sub_a.
  split.
  + intros x P1.
    destruct (dom_e _ _ P1) as [a P2].
    destruct (const_e _ _ _ P2) as [b [P3 P4]].
    apply (eq_cr (λ x, x ∈ A) (opair_eq_el _ _ _ _ P4)).
    apply P3.
  + intros x P1.
    apply (dom_i _ _ c).
    apply (const_i _ _ _ P1).
Qed.

Lemma const_ran: ∀ A, ∀ c, A ≠ ∅ → ran(const A c) = `{c}.
  intros A c P1.
  apply sub_a.
  split.
  + intros x P2.
    destruct (ran_e _ _ P2) as [a P3].
    destruct (const_e _ _ _ P3) as [b [_ P4]].
    apply (eq_cr (λ x, x ∈ `{c}) (opair_eq_er _ _ _ _ P4)).
    apply sing_i.
  + intros x P2.
    destruct (nempty_ex _ P1) as [a P3].
    apply (ran_i _ a).
    apply (eq_cl (λ x, ⟨a, x⟩ ∈ const A c) (sing_e _ _ P2)).
    apply (const_i _ _ _ P3).
Qed.

Lemma const_fval: ∀ A, ∀ c, ∀ x, x ∈ A → (const A c)[x] = c.
Proof. 
  intros A c x P1.
  apply fval_i.
  + apply const_is_fn.
  + apply (const_i _ _ _ P1).
Qed.
(*----------------------------------------------------------------------------*)
