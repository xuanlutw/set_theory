Require Import Init.Init.
Require Import Relation.Relation_.

(* Function *)
Definition sing_val (R: J) := ∀ a, ∀ b1, ∀ b2, ⟨a, b1⟩ ∈ R → ⟨a, b2⟩ ∈ R 
  → b1 = b2.
Definition sing_rot (R: J) := ∀ a1, ∀ a2, ∀ b, ⟨a1, b⟩ ∈ R → ⟨a2, b⟩ ∈ R
  → a1 = a2.
Definition fn   (F: J)     := rel F ∧ sing_val F.
Definition fnm  (F A B: J) := (fn F) ∧ (dom(F) = A) ∧ (ran(F) ⊆ B).
Definition surj (F A B: J) := (fnm F A B) ∧ (ran(F) = B).
Definition inj  (F A B: J) := (fnm F A B) ∧ (sing_rot F).
Definition bij  (F A B: J) := (fnm F A B) ∧ (ran(F) = B) ∧ (sing_rot F).

Definition in_restr (x F A: J) := (∃ a, ∃ b, ⟨a, b⟩ ∈ F ∧ x = ⟨a, b⟩ ∧ a ∈ A).
Definition restr (F A: J)      := {x: F| in_restr x F A}.
Notation   "F ↾ A"             := (restr F A).

Definition image (F A: J) := ran(restr F A).
Notation   "F ⟦ A ⟧"      := (image F A).

Definition in_inv (x R: J) := (∃ a, ∃ b, ⟨a, b⟩ ∈ R ∧ x = ⟨b, a⟩).
Definition inv    (R: J)   := {x: ran(R) ⨉ dom(R)| in_inv x R}.

Definition in_comp (x F G: J) := 
  (∃ a, ∃ b, ∃ c, ⟨a, b⟩ ∈ F ∧ ⟨b, c⟩ ∈ G ∧ x = ⟨a, c⟩).
Definition comp (F G: J)      := {x: dom(F) ⨉ ran(G)| in_comp x F G}.
Notation   "A ∘ B"            := (comp B A).

Definition fspace (A B: J) := {s: 𝒫(A ⨉ B)| fnm s A B}.

Lemma fnm_i: ∀ F, fn F → fnm F (dom(F)) (ran(F)).
Proof.
  intros F P1.
  split.
  + apply P1.
  + split.
    - apply eq_r.
    - apply sub_r.
Qed.

Lemma surj_i: ∀ F, fn F → surj F (dom(F)) (ran(F)).
Proof.
  intros F P1.
  split.
  + apply (fnm_i _ P1).
  + apply eq_r.
Qed.

Lemma bij_e: ∀ F, ∀ A, ∀ B, bij F A B → surj F A B ∧ inj F A B.
Proof.
  intros F A B [P1 [P2 P3]].
  split.
  + split.
    - apply P1.
    - apply P2.
  + split.
    - apply P1.
    - apply P3.
Qed.

Lemma bij_i: ∀ F, ∀ A, ∀ B, surj F A B → inj F A B → bij F A B.
Proof.
  intros F A B [P1 P2] [_ P3].
  split.
  + apply P1.
  + split.
    - apply P2.
    - apply P3.
Qed.
(*----------------------------------------------------------------------------*)

(* Function Value *)
Theorem fval_exist: ∀ F, ∀ x, ∃ y, fn F → x ∈ dom(F) →
  ⟨x, y⟩ ∈ F ∧ (∀ z, ⟨x, z⟩ ∈ F → y = z).
Proof.
  intros F x.
  destruct (LEM (x ∈ dom(F))) as [P1 | P1].
  + destruct (dom_e _ _ P1) as [y P2].
    exists y.
    intros P3 P4.
    split.
    - apply P2.
    - intros z P5.
      destruct P3 as [_ P3].
      apply (P3 x y z P2 P5).
  + exists x.
    intros _ P2.
    apply (bot_e _ (P1 P2)).
Qed.

Definition fval (F x: J) := (ex_outl (fval_exist F x)).
Notation "F [ x ]" := (fval F x).

(* Need Better Notation *)
(*[> Binary Function <]*)
(*Notation " x +[ r ] y" := (r[⟨x, y⟩]) (at level 63, left associativity).*)
(*[>----------------------------------------------------------------------------<]*)

Lemma fval_e: ∀ F, ∀ x, ∀y, y = F[x] → fn F → x ∈ dom(F) →
  ⟨x, y⟩ ∈ F ∧ (∀ y2, ⟨x, y2⟩ ∈ F → y = y2).
Proof.
  intros F x y P1.
  apply (eq_cl 
    (λ y, fn F → x ∈ dom( F) → ⟨ x, y ⟩ ∈ F ∧ (∀ y2, ⟨ x, y2 ⟩ ∈ F → y = y2))   
    (eq_s P1)).
  apply (ex_outr (fval_exist F x)).
Qed.

Lemma fval_e1: ∀ F, ∀ x, ∀ y, y = F[x] → fn F → x ∈ dom(F) → ⟨x, y⟩ ∈ F.
Proof.
  intros F x y P1 P2 P3.
  destruct (fval_e F x y P1 P2 P3) as [P4 _].
  apply P4.
Qed.

Lemma fval_e2: ∀ F, ∀ x, ∀ y, y = F[x] → fn F → x ∈ dom(F) → 
  (∀ y2, ⟨x, y2⟩ ∈ F → y = y2).
Proof.
  intros F x y P1 P2 P3.
  destruct (fval_e F x y P1 P2 P3) as [_ P4].
  apply P4.
Qed.

Theorem fval_i: ∀ F, ∀ x, ∀ y, fn F → ⟨x, y⟩ ∈ F → y = F[x].
Proof.
  intros F x y P1 P2.
  destruct (ex_outr (fval_exist F x) P1 (dom_i2 _ _ _ P2)) as [_ P3].
  apply eq_s.
  apply (P3 _ P2).
Qed.

Lemma fval_i2: ∀ F, ∀ x, fn F → x ∈ dom(F) → ⟨x, F[x]⟩ ∈ F.
Proof.
  intros F x P1 P2.
  destruct (dom_e _ _ P2) as [y P3].
  apply (eq_cl (λ y, ⟨x, y⟩ ∈ F) (fval_i _ _ _ P1 P3)).
  apply P3.
Qed.

Lemma fval_i_fnm: ∀ F, ∀ A, ∀ B, ∀ x, fnm F A B → x ∈ A → ⟨x, F[x]⟩ ∈ F.
Proof. 
  intros F A B x [P1 [P2 _]] P3.
  apply (fval_i2 _ _ P1).
  apply (eq_cl _ (eq_s P2)).
  apply P3.
Qed.

(*Lemma fval_intro_fonto: forall F A B x, fonto F A B -> x ∈ A -> ⟨x, F[x]⟩ ∈ F.*)
(*Proof.*)
  (*intros F A B x P1 P2.*)
  (*apply (fval_intro_fover F A B x (fonto_fover F A B P1) P2).*)
(*Qed.*)

Lemma fval_ran: ∀ F, ∀ x, fn F → x ∈ dom(F) → F[x] ∈ ran(F).
Proof.
  intros F x P1 P2.
  apply ran_i.
  exists x.
  apply (fval_i2 F x P1 P2).
Qed.

Lemma fval_codom: ∀ F, ∀ A, ∀ B, ∀ x, fnm F A B → x ∈ A → F[x] ∈ B.
Proof.
  intros F A B x [P1 [P2 P3]] P4.
  apply P3.
  apply (fval_ran _ _ P1).
  apply (eq_cr (λ y, x ∈ y) P2).
  apply P4.
Qed.

(*Lemma fval_ran_fonto: forall F A B x, fonto F A B -> x ∈ A -> F[x] ∈ B.*)
(*Proof.*)
  (*intros F A B x P1 P2.*)
  (*apply (fval_ran_fover F A B x (fonto_fover F A B P1) P2).*)
(*Qed.*)

Lemma fval_inj: ∀ F, ∀ A, ∀ B, ∀ x, ∀ y, inj F A B → x ∈ dom(F) → y ∈ dom(F)
  → F[x] = F[y] → x = y.
Proof.
  intros F A B x y [[P1 _] P2] P3 P4 P5.
  apply (P2 x y (F[x])).
  + apply (fval_i2 _ _ P1 P3).
  + apply (eq_cr (λ x, ⟨y, x⟩ ∈ F) P5).
    apply (fval_i2 _ _ P1 P4).
Qed. 

Lemma fval_sub: ∀ F, ∀ G, ∀ x, fn F → fn G → F ⊆ G → x ∈ dom(F) → F[x] = G[x].
Proof.
  intros F G x P1 P2 P3 P4.
  destruct (dom_e _ _ P4) as [y P5].
  apply (eq_cl (λ y, y = G[x]) (fval_i _ _ _ P1 P5)).
  apply (eq_cl (λ x, y = x) (fval_i _ _ _ P2 (P3 _ P5))).
  apply eq_r.
Qed.

Lemma fn_eq: ∀ F, ∀ G, fn F → fn G → dom(F) = dom(G) 
  → (∀ x, x ∈ dom(F) → F[x] = G[x]) → F = G.
Proof.
  intros F G [P1 P2] [P3 P4] P5 P6.
  apply sub_a.
  split.
  + intros s P7.
    destruct (P1 _ P7) as [x [y P8]].
    apply (eq_cr (λ s, s ∈ G) P8).
    pose (eq_cl (λ s, s ∈ F) P8 P7) as P9.
    apply (eq_cr (λ y, ⟨x, y⟩ ∈ G) (fval_i _ _ _ (and_i P1 P2) P9)).
    apply (eq_cr (λ y, ⟨x, y⟩ ∈ G) (P6 _ (dom_i2 _ _ _ P9))). 
    apply (fval_i2 _ _ (and_i P3 P4)).
    apply (eq_cl (λ y, x ∈ y) P5).
    apply (dom_i2 _ _ _ P9).
  + intros s P7.
    destruct (P3 _ P7) as [x [y P8]].
    apply (eq_cr (λ s, s ∈ F) P8).
    pose (eq_cl (λ s, s ∈ G) P8 P7) as P9.
    apply (eq_cr (λ y, ⟨x, y⟩ ∈ F) (fval_i _ _ _ (and_i P3 P4) P9)).
    apply (eq_cl (λ y, ⟨x, y⟩ ∈ F) 
      (P6 _ (eq_cr (λ y, x ∈ y) P5 (dom_i2 _ _ _ P9)))).
    apply (fval_i2 _ _ (and_i P1 P2)).
    apply (eq_cr (λ y, x ∈ y) P5).
    apply (dom_i2 _ _ _ P9).
Qed.
(*----------------------------------------------------------------------------*)

(* Restriction *)
Theorem restr_i: ∀ x, ∀ y, ∀ F, ∀ A, ⟨x, y⟩ ∈ F → x ∈ A → ⟨x, y⟩ ∈ F↾A.
Proof.
  intros x y F A P1 P2.
  apply (sub_i _ _ _ P1).
  exists x.
  exists y.
  repeat split.
  + apply P1.
  + apply P2.
Qed.

Lemma restr_e: ∀ x, ∀ y, ∀ F, ∀ A, ⟨x, y⟩ ∈ F↾A → ⟨x, y⟩ ∈ F ∧ x ∈ A.
Proof.
  intros x y F A P1.
  destruct (sub_e _ _ _ P1) as [P2 [a [b [_ [P3 P4]]]]].
  split.
  + apply P2.
  + apply (eq_cr (λ x, x ∈ A) (opair_eq_el _ _ _ _ P3)).
    apply P4.
Qed.

Lemma restr_e2: ∀ s, ∀ F, ∀ A, s ∈ F↾A 
  → ∃ x, ∃ y, ⟨x, y⟩ ∈ F ∧ s = ⟨x, y⟩ ∧x ∈ A.
Proof.
  intros s F A P1.
  destruct (sub_e _ _ _ P1) as [_ P2].
  apply P2.
Qed.

Lemma restr_rel: ∀ F, ∀ A, rel (F↾A).
Proof.
  intros F A r P1.
  destruct (sub_e _ _ _ P1) as [_ [a [b [_ [P2 _]]]]].
  exists a.
  exists b.
  apply P2.
Qed.

Lemma sub_restr_eq: ∀ F, ∀ G, ∀ R, fn F → fn G → F ⊆ G → R ⊆ dom(F) → F↾R = G↾R.
Proof.
  intros F G R P1 P2 P3 P4.
  apply sub_a.
  split.
  + intros s P5.
    destruct (restr_e2 _ _ _ P5) as [x [y [P6 [P7 P8]]]].
    apply (eq_cr (λ s, s ∈ G↾R) P7).
    apply (restr_i).
    - apply (P3 _ P6).
    - apply P8.
  + intros s P5.
    destruct (restr_e2 _ _ _ P5) as [x [y [P6 [P7 P8]]]].
    apply (eq_cr (λ s, s ∈ F↾R) P7).
    apply (restr_i).
    - apply (eq_cr (λ y, ⟨x, y⟩ ∈ F) (fval_i _ _ _ P2 P6)). 
      apply (eq_cl (λ y, ⟨x, y⟩ ∈ F) (fval_sub _ _ _ P1 P2 P3 (P4 _ P8))).
      apply (fval_i2 _ _ P1 (P4 _ P8)). 
    - apply P8.
Qed.

Lemma restr_over: ∀ F, ∀ R, rel F → dom(F) ⊆ R → F↾R = F.
Proof.
  intros F R P1 P2.
  apply sub_a.
  split.
  + intros s P3.
    destruct (restr_e2 _ _ _ P3) as [x [y [P4 [P5 P6]]]].
    apply (eq_cr (λ x, x ∈ F) P5).
    apply P4.
  + intros s P3.
    destruct (P1 _ P3) as [x [y P4]].
    apply (eq_cr (λ x, x ∈ F↾R) P4).
    apply restr_i.
    - apply (eq_cl (λ x, x ∈ F) P4).
      apply P3.
    - pose (dom_i2 _ _ _ (eq_cl (λ x, x ∈ F) P4 P3)) as P5.
      apply (P2 _ P5).
Qed.
(*----------------------------------------------------------------------------*)

(* Image *)
Theorem image_i: ∀ y, ∀ F, ∀ A, (∃ x, ⟨x, y⟩ ∈ F ∧ x ∈ A) → y ∈ F⟦A⟧.
Proof.
  intros y F A [x [P1 P2]].
  apply ran_i.
  exists x.
  apply (restr_i _ _ _ _ P1 P2).
Qed.

Lemma image_i2: ∀ x, ∀ F, ∀ A, fn F → x ∈ dom(F) → x ∈ A → F[x] ∈ F⟦A⟧.
Proof.
  intros x F A P1 P2 P3.
  apply image_i.
  exists x.
  split.
  + apply (fval_i2 _ _ P1 P2).
  + apply P3.
Qed.

Lemma image_e: ∀ y, ∀ F, ∀ A, y ∈ F⟦A⟧ → (∃ x, ⟨x, y⟩ ∈ F ∧ x ∈ A).
Proof.
  intros y F A P1.
  destruct (ran_e _ _ P1) as [x P2].
  destruct (restr_e _ _ _ _ P2) as [P3 P4].
  exists x.
  split.
  + apply P3.
  + apply P4.
Qed.

(* 3K *)
Lemma image_union2: ∀ F, ∀ A, ∀ B, F⟦A ∪ B⟧ = F⟦A⟧ ∪ F⟦B⟧.
Proof.
  intros F A B.
  apply sub_a.
  split.
  + intros y P1.
    destruct (image_e _ _ _ P1) as [x [P2 P3]].
    destruct (union2_e _ _ _ P3) as [P4 | P4].
    - apply union2_il.
      apply image_i.
      exists x.
      apply (and_i P2 P4).
    - apply union2_ir.
      apply image_i.
      exists x.
      apply (and_i P2 P4).
  + intros y P2.
    apply image_i.
    destruct (union2_e _ _ _ P2) as [P3 | P3].
    - destruct (image_e _ _ _ P3) as [x [P4 P5]].
      exists x.
      split.
      * apply P4.
      * apply union2_il.
        apply P5.
    - destruct (image_e _ _ _ P3) as [x [P4 P5]].
      exists x.
      split.
      * apply P4.
      * apply union2_ir.
        apply P5.
Qed.

Lemma image_inter2: ∀ F, ∀ A, ∀ B, F⟦A ∩ B⟧ ⊆ F⟦A⟧ ∩ F⟦B⟧.
Proof.
  intros F A B y P1.
  destruct (image_e _ _ _ P1) as [x [P2 P3]].
  destruct (inter2_e _ _ _ P3) as [P4 P5].
  apply inter2_i.
  + apply image_i.
    exists x.
    apply (and_i P2 P4).
  + apply image_i.
    exists x.
    apply (and_i P2 P5).
Qed.

Lemma image_compl: ∀ F, ∀ A, ∀ B, (F⟦A⟧) \ (F⟦B⟧) ⊆ F⟦(A \ B)⟧.
Proof.
  intros F A B y P1.
  destruct (compl_e _ _ _ P1) as [P2 P3].
  apply image_i.
  destruct (image_e _ _ _ P2) as [x [P4 P5]].
  exists x.
  split.
  + apply P4.
  + apply (compl_i _ _ _ P5).
    intros P6.
    apply P3.
    apply image_i.
    exists x.
    apply (and_i P4 P6).
Qed.

Lemma image_ran: ∀ F, ∀ A, F⟦A⟧ ⊆ ran(F).
Proof.
  intros F A y P1.
  destruct (image_e _ _ _ P1) as [x [P2 P3]].
  apply (ran_i2 _ _ _ P2).
Qed.

Lemma image_dom: ∀ F, F⟦dom(F)⟧ = ran(F).
Proof.
  intros F.
  apply sub_a.
  split.
  + apply image_ran.
  + intros y P1.
    destruct (ran_e _ _ P1) as [x P2].
    apply image_i.
    exists x.
    split.
    - apply P2.
    - apply (dom_i2 _ _ _ P2).
Qed.

Lemma image_surj: ∀ F, ∀ A, ∀ B, surj F A B → F⟦A⟧ = B.
Proof.
  intros F A B [[_ [P1 _]] P2].
  apply sub_a.
  split.
  + apply (eq_cl _ P2).
    apply image_ran.
  + intros y P3.
    destruct (ran_e _ _ (eq_cr _ P2 P3)) as [x P4].
    apply image_i.
    exists x.
    split.
    - apply P4.
    - apply (eq_cl _ P1).
      apply (dom_i2 _ _ _ P4).
Qed.
(*----------------------------------------------------------------------------*)

(* Inverse *)
Theorem inv_superset: ∀ x, ∀ R, in_inv x R → x ∈ (ran(R)) ⨉ (dom(R)).
Proof.
  intros x R P1.
  destruct P1 as [a [b [P1 P2]]].
  apply (eq_cr (λ x, x ∈ (ran(R)) ⨉ (dom(R))) P2).
  apply cp_i.
  + apply (ran_i2 _ _ _ P1).
  + apply (dom_i2 _ _ _ P1).
Qed.

Lemma inv_i: ∀ x, ∀ y, ∀ R, ⟨x, y⟩ ∈ R → ⟨y, x⟩ ∈ inv R.
Proof.
  intros x y R P1.
  assert (in_inv (⟨y, x⟩) R) as P2.
  { exists x.
    exists y.
    split.
    + apply P1.
    + apply eq_r. }
  apply sub_i.
  + apply (inv_superset _ _ P2).
  + apply P2.
Qed.

Lemma inv_e: ∀ x, ∀ y, ∀ R, ⟨x, y⟩ ∈ inv R → ⟨y, x⟩ ∈ R.
Proof.
  intros x y R P1.
  destruct (sub_e _ _ _ P1) as [_ [a [b [P2 P3]]]].
  apply (eq_cr (λ x, ⟨y, x⟩ ∈ R) (opair_eq_el _ _ _ _ P3)).
  apply (eq_cr (λ y, ⟨y, b⟩ ∈ R) (opair_eq_er _ _ _ _ P3)).
  apply P2.
Qed.

(* 3F *)
Theorem inv_dom: ∀ F, dom(inv F) = ran(F).
Proof.
  intros F.
  apply sub_a.
  split.
  + intros x P1.
    destruct (dom_e _ _ P1) as [y P2].
    apply ran_i.
    exists y.
    apply (inv_e _ _ _ P2).
  + intros x P1.
    destruct (ran_e _ _ P1) as [y P2].
    apply dom_i.
    exists y.
    apply (inv_i _ _ _ P2).
Qed.
    
Theorem inv_ran: ∀ F, ran(inv F) = dom(F).
Proof.
  intros F.
  apply sub_a.
  split.
  + intros x P1.
    destruct (ran_e _ _ P1) as [y P2].
    apply dom_i.
    exists y.
    apply (inv_e _ _ _ P2).
  + intros x P1.
    destruct (dom_e _ _ P1) as [y P2].
    apply ran_i.
    exists y.
    apply (inv_i _ _ _ P2).
Qed.

Theorem inv_rel: ∀ R, rel (inv R).
Proof.
  intros R x P1.
  destruct (sub_e _ _ _ P1) as [P2 _].
  destruct (cp_e _ _ _ P2) as [a [b [_ [_ P3]]]]. 
  exists a.
  exists b.
  apply P3.
Qed.

Lemma inv_sing_rot: ∀ R, sing_rot R → sing_val (inv R).
Proof.
  intros R P1 a b1 b2 P2 P3.
  apply (P1 _ _ _ (inv_e _ _ _ P2) (inv_e _ _ _ P3)).
Qed.

Lemma inv_sing_val: ∀ R, sing_val R → sing_rot (inv R).
Proof.
  intros R P1 a b1 b2 P2 P3.
  apply (P1 _ _ _ (inv_e _ _ _ P2) (inv_e _ _ _ P3)).
Qed.

Lemma sing_rot_inv: ∀ R, sing_val (inv R) → sing_rot R.
Proof.
  intros R P1 a1 a2 b P2 P3.
  apply (P1 _ _ _ (inv_i _ _ _ P2) (inv_i _ _ _ P3)).
Qed.

Lemma sing_val_inv: ∀ R, sing_rot (inv R) → sing_val R.
Proof.
  intros R P1 a1 a2 b P2 P3.
  apply (P1 _ _ _ (inv_i _ _ _ P2) (inv_i _ _ _ P3)).
Qed.

Theorem inv_inv: ∀ F, rel F → inv (inv F) = F.
Proof.
  intros F P1.
  apply sub_a.
  split.
  + intros x P2.
    destruct ((inv_rel (inv F)) x P2) as [a [b P3]].
    apply (eq_cr (λ x, x ∈ F) P3).
    apply inv_e.
    apply inv_e.
    apply (eq_cl (λ x, x ∈ inv(inv F)) P3).
    apply P2.
  + intros x P2.
    destruct (P1 x P2) as [a [b P3]].
    apply (eq_cr (λ x, x ∈ inv(inv F)) P3).
    apply inv_i.
    apply inv_i.
    apply (eq_cl (λ x, x ∈ F) P3).
    apply P2.
Qed.

(* 3F *)
Lemma inv_fn: ∀ F, sing_rot F ↔ fn (inv F).
Proof.
  intros F.
  split.
  + intros P1.
    split.
    - apply inv_rel.
    - apply (inv_sing_rot _ P1).
  + intros [_ P1] a1 a2 b P2 P3.
    apply (P1 b a1 a2).
    - apply (inv_i _ _ _ P2).
    - apply (inv_i _ _ _ P3).
Qed.

Lemma fn_inv: ∀ F, rel F → (fn F ↔ sing_rot (inv F)).
Proof.
  intros F P1.
  split.
  + intros [_ P2] a1 a2 b P3 P4.
    apply (P2 b a1 a2).
    - apply (inv_e _ _ _ P3). 
    - apply (inv_e _ _ _ P4).
  + intros P2.
    split.
    - apply P1.
    - intros a b1 b2 P3 P4.
      apply (P2 b1 b2 a).
      * apply (inv_i _ _ _ P3).
      * apply (inv_i _ _ _ P4).
Qed.

(* 3G *)
Lemma inv_fn_ex1: ∀ F, ∀ A, ∀ B, ∀ x, inj F A B → x ∈ dom(F) 
  → (inv F)[F[x]] = x.
Proof.
  intros F A B x [[P1 _] P2] P3.
  apply eq_s.
  apply fval_i.
  + destruct (inv_fn F) as [P4 _].
    apply (P4 P2).
  + apply inv_i.
    apply (fval_i2 _ _ P1 P3).
Qed.

Lemma inv_fn_ex2: ∀ F, ∀ A, ∀ B, ∀ x, inj F A B → x ∈ ran(F) 
  → F[(inv F)[x]] = x.
Proof.
  intros F A B x [[P1 _] P2] P3.
  apply eq_s.
  apply fval_i.
  + apply P1.
  + apply inv_e.
    destruct (inv_fn F) as [P4 _].
    apply (fval_i2 _ _ (P4 P2)).
    apply (eq_cr _ (inv_dom F)).
    apply P3.
Qed.

Lemma inv_bij: ∀ F, ∀ A, ∀ B, bij F A B → bij (inv F) B A.
Proof.
  intros F A B [[[P1 P2] [P3 _]] [P4 P5]].
  repeat split.
  + apply inv_rel.
  + apply (inv_sing_rot _ P5).
  + apply (eq_cr (λ x, x = B) (inv_dom F)).
    apply P4.
  + apply (eq_cl (λ x, ran(inv F) ⊆ x) P3).
    apply (eq_cl (λ x, ran(inv F) ⊆ x) (inv_ran F)).
    apply (sub_r).
  + apply (eq_cr (λ x, x = A) (inv_ran F)).
    apply P3.
  + apply (inv_sing_val _ P2).
Qed.

(*Lemma inv_bijection_function: forall F A B, bijection F A B → function (inv F).*)
(*Proof.*)
  (*intros F A B P1.*)
  (*destruct (inv_bijection _ _ _ P1) as [[P2 _] _].*)
  (*apply P2.*)
(*Qed.*)

Lemma inv_image_ran: ∀ F, ∀ A, (inv F)⟦A⟧ ⊆ dom(F).
Proof. 
  intros F A.
  apply (eq_cl _ (inv_ran F)).
  apply (image_ran).
Qed.
(*----------------------------------------------------------------------------*)

(* Composition *)
(* Only consider composition of two functions *)
Theorem comp_superset: ∀ x, ∀ F, ∀ G, in_comp x F G → x ∈ dom(F) ⨉ ran(G).
Proof.
  intros x F G [a [b [c [P1 [P2 P3]]]]].
  apply (eq_cr (λ y, y ∈ dom(F) ⨉ ran(G)) P3).
  apply cp_i.
  + apply (dom_i2 _ _ _ P1).
  + apply (ran_i2 _ _ _ P2).
Qed.

Theorem comp_i: ∀ x, ∀ z, ∀ F, ∀ G, (∃ y, ⟨x, y⟩ ∈ F ∧ ⟨y, z⟩ ∈ G) → 
  ⟨x, z⟩ ∈ G ∘ F.
Proof.
  intros x z F G [y [P1 P2]].
  assert (in_comp (⟨x, z⟩) F G) as P3.
  { exists x.
    exists y.
    exists z.
    repeat split.
    + apply P1.
    + apply P2. }
  apply sub_i.
  + apply (comp_superset _ _ _ P3).
  + apply P3.
Qed.

Lemma comp_e: ∀ x, ∀ z, ∀ F, ∀ G, ⟨x, z⟩ ∈ G ∘ F → 
  (∃ y, ⟨x, y⟩ ∈ F ∧ ⟨y, z⟩ ∈ G).
Proof.
  intros x z F G P1.
  destruct (sub_e _ _ _ P1) as [_ [a [b [c [P2 [P3 P4]]]]]].
  exists b.
  split.
  + apply (eq_cr (λ x, ⟨x, b⟩ ∈ F) (opair_eq_el _ _ _ _ P4)).
    apply P2.
  + apply (eq_cr (λ z, ⟨b, z⟩ ∈ G) (opair_eq_er _ _ _ _ P4)).
    apply P3.
Qed.

Theorem comp_rel: ∀ F, ∀ G, rel(G ∘ F).
Proof.
  intros F G.
  apply (sub_rel (dom(F) ⨉ ran(G))).
  + apply (cp_rel).
  + apply (sub_e1 (λ x, in_comp x F G) (dom(F) ⨉ ran(G))).
Qed.

Lemma comp_e2: ∀ s, ∀ F, ∀ G, s ∈ G ∘ F → 
  (∃ x, ∃ y, ∃ z, s = ⟨x, z⟩ ∧ ⟨x, y⟩ ∈ F ∧ ⟨y, z⟩ ∈ G).
Proof. 
  intros s F G P1.
  destruct (comp_rel _ _ _ P1) as [x [z P2]].
  destruct (comp_e _ _ _ _ (eq_cl (λ s, s ∈ G ∘ F) P2 P1)) as [y P3].
  exists x.
  exists y.
  exists z.
  apply (and_i P2 P3). 
Qed.
  
(* 3H *)
Lemma comp_sing_val: ∀ F, ∀ G, sing_val F → sing_val G → sing_val (G ∘ F).
Proof. 
  intros F G P1 P2 a b1 b2 P3 P4.
  destruct (comp_e _ _ _ _ P3) as [e1 [P5 P6]].
  destruct (comp_e _ _ _ _ P4) as [e2 [P7 P8]].
  apply (P2 _ _ _ P6).
  apply (eq_cr (λ x, ⟨x, b2⟩ ∈ G) (P1 _ _ _ P5 P7)).
  apply P8.
Qed.

Lemma comp_sing_rot: ∀ F, ∀ G, sing_rot F → sing_rot G → sing_rot (G ∘ F).
Proof. 
  intros F G P1 P2 a1 a2 b P3 P4.
  destruct (comp_e _ _ _ _ P3) as [e1 [P5 P6]].
  destruct (comp_e _ _ _ _ P4) as [e2 [P7 P8]].
  apply (P1 _ _ _ P5).
  apply (eq_cr (λ x, ⟨a2, x⟩ ∈ F) (P2 _ _ _ P6 P8)).
  apply P7.
Qed.

Lemma comp_fn: ∀ F, ∀ G, fn F → fn G → fn (G ∘ F).
Proof.
  intros F G [_ P1] [_ P2].
  split.
  + apply comp_rel.
  + apply (comp_sing_val _ _ P1 P2).
Qed.

Lemma comp_dom: ∀ F, ∀ G, dom(G ∘ F) ⊆ dom(F). 
Proof.
  intros F G x P1.
  destruct (dom_e _ _ P1) as [z P2].
  destruct (comp_e _ _ _ _ P2) as [y [P3 _]].
  apply (dom_i2 _ _ y P3).
Qed.

Lemma comp_coin_dom: ∀ F, ∀ G, ran(F) = dom(G) → dom(G ∘ F) = dom(F).
Proof.
  intros F G P1.
  apply sub_a.
  split.
  + apply comp_dom.
  + intros x P2.
    destruct (dom_e _ _ P2) as [y P3].
    pose (eq_cl _ P1 (ran_i2 _ _ _ P3)) as P4.
    destruct (dom_e _ _ P4) as [z P5].
    apply dom_i.
    exists z.
    apply comp_i.
    exists y.
    apply (and_i P3 P5).
Qed.

Lemma comp_coin_dom_weak: ∀ F, ∀ G, ran(F) ⊆ dom(G) → dom(G ∘ F) = dom(F).
Proof.
  intros F G P1.
  apply sub_a.
  split.
  + apply comp_dom.
  + intros x P2.
    destruct (dom_e _ _ P2) as [y P3].
    pose (P1 _ (ran_i2 _ _ _ P3)) as P4.
    destruct (dom_e _ _ P4) as [z P5].
    apply dom_i.
    exists z.
    apply comp_i.
    exists y.
    apply (and_i P3 P5).
Qed.

Lemma comp_dom_fnm: ∀ F, ∀ G, ∀ A, ∀ B, ∀ C, fnm F A B → fnm G B C 
  → dom (G ∘ F) = A.
Proof.
  intros F G A B C [_ [P1 P2]] [_ [P3 _]].
  apply (eq_cl (λ x, dom(G ∘ F) = x) P1).
  apply comp_coin_dom_weak.
  apply (eq_cr (λ x, ran(F) ⊆ x) P3).
  apply P2.
Qed.
  
Lemma comp_dom_e: ∀ F, ∀ G, ∀ x, fn F → fn G → x ∈ dom(G ∘ F) → F[x] ∈ dom(G).
Proof.
  intros F G x P1 P2 P3.
  destruct (dom_e _ _ P3) as [z P4].
  destruct (comp_e _ _ _ _ P4) as [y [P5 P6]].
  apply dom_i.
  exists z.
  apply (eq_cl (λ x, ⟨x, z⟩ ∈ G) (fval_i _ _ _ P1 P5)).
  apply P6.
Qed.

Lemma comp_ran: ∀ F, ∀ G, ran(G ∘ F) ⊆ ran(G).
Proof.
  intros F G z P1.
  destruct (ran_e _ _ P1) as [x P2].
  destruct (comp_e _ _ _ _ P2) as [y [_ P3]].
  apply (ran_i2 _ y _ P3).
Qed.

Lemma comp_ran2: ∀ F, ∀ G, ran(G ∘ F) = G⟦ran(F)⟧.
Proof.
  intros F G.
  apply sub_a.
  split.
  + intros z P1.
    destruct (ran_e _ _ P1) as [x P2].
    destruct (comp_e _ _ _ _ P2) as [y [P3 P4]].
    apply image_i.
    exists y.
    split.
    - apply P4.
    - apply (ran_i2 _ _ _ P3).
  + intros z P1.
    destruct (image_e _ _ _ P1) as [y [P2 P3]].
    destruct (ran_e _ _ P3) as [x P4].
    apply (ran_i2 _ x _).
    apply (comp_i).
    exists y.
    apply (and_i P4 P2).
Qed.

Lemma comp_fnm: ∀ F, ∀ G, ∀ A, ∀ B, ∀ C, fnm F A B → fnm G B C 
  → fnm (G ∘ F) A C.
Proof.
  intros F G A B C [P1 [P2 P3]] [P4 [P5 P6]].
  split.
  + apply (comp_fn _ _ P1 P4).
  + split.
    - apply (eq_cl _ P2). 
      apply comp_coin_dom_weak.
      apply (eq_cr _ P5).
      apply P3.
    - apply (sub_t _ (ran(G)) _).
      * apply comp_ran.
      * apply P6.
Qed.

Lemma comp_fval: ∀ F, ∀ G, ∀ x, fn F → fn G → x ∈ dom(G ∘ F) → 
  G[F[x]] = (G ∘ F)[x].
Proof.
  intros F G x P1 P2 P3.
  apply (fval_i _ _ _ (comp_fn _ _ P1 P2)).
  apply (comp_i).
  exists (F[x]).
  split.
  + apply (fval_i2 _ _ P1).
    apply (comp_dom _ _ _ P3).
  + apply (fval_i2 _ _ P2).
    apply (comp_dom_e _ _ _ P1 P2 P3).
Qed.

Lemma comp_inj: ∀ F, ∀ G, ∀ A, ∀ B, ∀ C, inj F A B → inj G B C 
  → inj (G ∘ F) A C.
Proof.
  intros F G A B C [P1 P2] [P3 P4].
  split.
  + apply (comp_fnm _ _ _ _ _ P1 P3).
  + apply (comp_sing_rot _ _ P2 P4).
Qed.

Lemma comp_surj: ∀ F, ∀ G, ∀ A, ∀ B, ∀ C, surj F A B → surj G B C 
  → surj (G ∘ F) A C.
Proof. 
  intros F G A B C [P1 P2] [P3 P4]. 
  split.
  + apply (comp_fnm _ _ _ _ _ P1 P3).
  + destruct P3 as [_ [P3 _]].
    apply (eq_cr (λ x, x  = C) (comp_ran2 F G)).
    apply (eq_cr (λ x, G⟦x⟧ = C) P2).
    apply (eq_cl (λ x, G⟦x⟧ = C) P3).
    apply (eq_cl (λ x, G⟦dom(G)⟧ = x) P4).
    apply image_dom.
Qed.

Lemma comp_bij: ∀ F, ∀ G, ∀ A, ∀ B, ∀ C, bij F A B → bij G B C 
  → bij (G ∘ F) A C.
Proof.
  intros F G A B C P1 P2.
  destruct (bij_e _ _ _ P1) as [P3 P4].
  destruct (bij_e _ _ _ P2) as [P5 P6].
  apply bij_i.
  + apply (comp_surj _ _ _ _ _ P3 P5).
  + apply (comp_inj _ _ _ _ _ P4 P6).
Qed.

(* 3I *)
Theorem comp_inv: ∀ F, ∀ G, inv (G ∘ F) = (inv F) ∘ (inv G).
Proof.
  intros F G.
  apply sub_a.
  split.
  + intros r P1.
    destruct (inv_rel _ r P1) as [x [z P2]].
    destruct (comp_e _ _ _ _ (inv_e _ _ _ (eq_cl (λ r, r ∈ inv (G ∘ F)) P2 P1)))
      as [y [P3 P4]].
    apply (eq_cr (λ r, r ∈ inv F ∘ inv G) P2).
    apply comp_i.
    exists y.
    split.
    - apply (inv_i _ _ _ P4).
    - apply (inv_i _ _ _ P3).
  + intros r P1.
    destruct (comp_rel _ _ r P1) as [x [z P2]].
    apply (eq_cr (λ r, r ∈ inv (G ∘ F)) P2).
    destruct (comp_e _ _ _ _ (eq_cl (λ r, r ∈ inv F ∘ inv G) P2 P1))
      as [y [P3 P4]] .
    apply inv_i.
    apply comp_i.
    exists y.
    split.
    - apply (inv_e _ _ _ P4).
    - apply (inv_e _ _ _ P3).
Qed.
(*----------------------------------------------------------------------------*)

(* Function Space *)
Lemma fspace_superset: ∀ F, ∀ A, ∀ B, fnm F A B → F ∈ 𝒫(cp A B).
Proof.
  intros F A B [[P1 _] [P2 P3]].
  apply power_i.
  intros x P4.
  destruct (P1 x P4) as [a [b P5]].
  apply (eq_cr (λ x, x ∈ A ⨉ B) P5).
  apply cp_i.
  + apply (eq_cl _ P2).
    apply (dom_i2 _ _ _ (eq_cl (λ x, x ∈ F) P5 P4)).
  + apply P3.
    apply (ran_i2 _ _ _ (eq_cl (λ x, x ∈ F) P5 P4)).
Qed.

Lemma fspace_i: ∀ F, ∀ A, ∀ B, fnm F A B → (F ∈ (fspace A B)).
Proof.
  intros F A B P1.
  apply sub_i.
  + apply (fspace_superset _ _ _ P1).
  + apply P1.
Qed.

Lemma fspace_e: ∀ F, ∀ A, ∀ B, F ∈ fspace A B → fnm F A B.
Proof.
  intros F A B P1.
  destruct (sub_e _ _ _ P1) as [_ P2].
  apply P2.
Qed.

Lemma fspace_dom: ∀ F, ∀ A, ∀ B, F ∈ fspace A B → dom(F) = A.
Proof.
  intros F A B P1.
  destruct (fspace_e _ _ _ P1) as [_ [P2 _]].
  apply P2.
Qed.

Lemma fspace_ran: ∀ F, ∀ A, ∀ B, F ∈ fspace A B → ran(F) ⊆ B.
Proof.
  intros F A B P1.
  destruct (fspace_e _ _ _ P1) as [_ [_ P2]].
  apply P2.
Qed.
(*----------------------------------------------------------------------------*)

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

Lemma rel_exten: ∀ F, ∀ x, ∀ y, rel F → rel (F ∪ J{⟨x, y⟩}).
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
  → sing_val (F ∪ J{⟨x, y⟩}).
Proof.
  intros F x y P1 P2 xx y1 y2 P3 P4.
  destruct (union2_e _ _ _ P3) as [P5 | P5].
  - destruct (union2_e _ _ _ P4) as [P6 | P6].
    * apply (P1 _ _ _ P5 P6).
    * apply bot_e.
      apply P2.
      apply (eq_cr (λ x, x ∈ dom(F)) (opair_eq_el _ _ _ _ (sing_e _ _ P6))).
      apply (dom_i2 _ _ _ P5).
  - destruct (union2_e _ _ _ P4) as [P6 | P6].
    * apply bot_e.
      apply P2.
      apply (eq_cr (λ x, x ∈ dom(F)) (opair_eq_el _ _ _ _ (sing_e _ _ P5))).
      apply (dom_i2 _ _ _ P6).
    * apply (eq_cl (λ x, x = y2) (opair_eq_er _ _ _ _ (sing_e _ _ P5))).
      apply (opair_eq_er _ _ _ _ (sing_e _ _ P6)).
Qed.

Lemma fn_exten: ∀ F, ∀ x, ∀ y, fn F → x ∉ dom(F) → fn (F ∪ J{⟨x, y⟩}).
Proof.
  intros F x y [P1 P2] P3.
  split.
  + apply (rel_exten _ _ _ P1).
  + apply (sing_val_exten _ _ _ P2 P3).
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
      apply (dom_i2 _ _ _ P3).
    - apply union2_ir.
      apply (dom_i2 _ _ _ P3).
  + intros x P1.
    apply dom_i.
    destruct (union2_e _ _ _ P1) as [P2 | P2].
    - destruct (dom_e _ _ P2) as [f P3]. 
      exists f.
      apply (union2_il _ _ _ P3).
    - destruct (dom_e _ _ P2) as [f P3]. 
      exists f.
      apply (union2_ir _ _ _ P3).
Qed.

Lemma union_dom_e: ∀ H, ∀ x, x ∈ dom(∪H) → ∃ f, x ∈ dom(f) ∧ f ∈ H.
Proof.
  intros H x P1.
  destruct (dom_e _ _ P1) as [y P2].
  destruct (union_e _ _ P2) as [f [P3 P4]].
  exists f.
  split.
  + apply (dom_i2 _ _ _ P4).
  + apply P3.
Qed.

Lemma union_dom_i: ∀ H, ∀ f, ∀ x, x ∈ dom(f) → f ∈ H → x ∈ dom(∪H).
Proof.
  intros H f x P1 P2.
  destruct (dom_e _ _ P1) as [y P3].
  apply dom_i.
  exists y.
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
      apply (ran_i2 _ _ _ P3).
    - apply union2_ir.
      apply (ran_i2 _ _ _ P3).
  + intros x P1.
    apply ran_i.
    destruct (union2_e _ _ _ P1) as [P2 | P2].
    - destruct (ran_e _ _ P2) as [f P3]. 
      exists f.
      apply (union2_il _ _ _ P3).
    - destruct (ran_e _ _ P2) as [f P3]. 
      exists f.
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
  + apply (dom_i2 _ _ _ (eq_cl (λ s, s ∈ F) P7 P5)).
  + apply (dom_i2 _ _ _ (eq_cl (λ s, s ∈ G) P7 P6)).
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
        ++apply (dom_i2 _ _ _ P8).
        ++apply (dom_i2 _ _ _ P10).
    - destruct (disjoint_selection _ _ _(disjoint_dom_rel _ _ P1 P2 P5) P7)
        as [[P10 P11] | [P10 P11]].
      * apply bot_e.
        apply (empty_i a).
        apply (eq_cl _ P5).
        apply inter2_i.
        ++apply (dom_i2 _ _ _ P10).
        ++apply (dom_i2 _ _ _ P8).
      * apply (P4 _ _ _ P8 P10).
Qed.

Lemma union_fval: ∀ f, ∀ H, ∀ x, f ∈ H → fn f → fn (∪(H)) → x ∈ dom(f) 
  → f[x] = (∪(H))[x].
Proof.
  intros f H x P1 P2 P3 P4.
  destruct (dom_e _ _ P4) as [y P5].
  apply (eq_cl (λ y, y = (∪ H)[x]) (fval_i _ _ _ P2 P5)).
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
  apply (eq_cl (λ y, y = (F ∪ G)[x]) (fval_i _ _ _ P1 P4)).
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