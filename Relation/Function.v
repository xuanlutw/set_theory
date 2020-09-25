Require Import Init.Init.
Require Import Relation.Relation_.

(* Function *)
Definition sing_val (R: J) := ∀ a, ∀ b1, ∀ b2, ⟨a, b1⟩ ∈ R → ⟨a, b2⟩ ∈ R 
  → b1 = b2.
Definition sing_rot (R: J) := ∀ a1, ∀ a2, ∀ b, ⟨a1, b⟩ ∈ R → ⟨a2, b⟩ ∈ R
  → a1 = a2.

Definition fn    (F: J)   := rel F ∧ sing_val F.
Definition fmap (A B: J) := {s: 𝒫(A ⨉ B)| fn s ∧ dom(s) = A ∧ ran(s) ⊆ B}.
Notation   "A ↦ B"      := (fmap A B).

Definition surjs (A B: J) := {s: 𝒫(A ⨉ B)| fn s ∧ dom(s) = A ∧ ran(s) = B}.
Definition injs  (A B: J)
  := {s: 𝒫(A ⨉ B)| fn s ∧ dom(s) = A ∧ ran(s) ⊆ B ∧ (sing_rot s)}.
Definition bijs  (A B: J)
  := {s: 𝒫(A ⨉ B)| fn s ∧ dom(s) = A ∧ ran(s) = B ∧ (sing_rot s)}.

Notation "A ↦ˢ B" := (surjs A B).
Notation "A ↦ⁱ B" := (injs A B).
Notation "A ↦ᵇ B" := (bijs A B).

Definition restr (F A: J) := {x: F| ∃ a, ∃ b, ⟨a, b⟩ ∈ F ∧ x = ⟨a, b⟩ ∧ a ∈ A}.
Notation   "F ↾ A"        := (restr F A).

Definition image (F A: J) := ran(restr F A).
Notation   "F ⟦ A ⟧"      := (image F A).

Definition inv (R: J) := {x: ran(R) ⨉ dom(R)| ∃ a, ∃ b, ⟨a, b⟩ ∈ R ∧ x = ⟨b, a⟩}.
Notation   "R ⁻¹"     := (inv R).
  
Definition comp (F G: J) 
  := {x: dom(F) ⨉ ran(G)| ∃ a, ∃ b, ∃ c, ⟨a, b⟩ ∈ F ∧ ⟨b, c⟩ ∈ G ∧ x = ⟨a, c⟩}.
Notation   "A ∘ B"       := (comp B A).

(* Function and Function Over *)
Lemma fn_i: ∀ F, rel F → sing_val F → fn F.
Proof.
  intros F P1 P2.
  apply (and_i P1 P2).
Qed.

Lemma fn_rel: ∀ F, fn F → rel F.
Proof.
  intros F [P1 _].
  apply P1.
Qed.

Lemma fn_sing_val: ∀ F, fn F → sing_val F.
Proof.
  intros F [_ P1].
  apply P1.
Qed.

Lemma fmap_fn: ∀ F, ∀ A, ∀ B, F ∈ A ↦ B → fn F.
Proof.
  intros F A B P1.
  destruct (sub_e _ _ _ P1) as [_ [P2 _]].
  apply P2.
Qed.

Lemma fmap_dom: ∀ F, ∀ A, ∀ B, F ∈ A ↦ B → dom(F) = A.
Proof.
  intros F A B P1.
  destruct (sub_e _ _ _ P1) as [_ [_ [P2 _]]].
  apply P2.
Qed.

Lemma fmap_ran: ∀ F, ∀ A, ∀ B, F ∈ A ↦ B → ran(F) ⊆ B.
Proof.
  intros F A B P1.
  destruct (sub_e _ _ _ P1) as [_ [_ [_ P2]]].
  apply P2.
Qed.

Lemma fmap_i: ∀ F, ∀ A, ∀ B, fn F → dom(F) = A → ran(F) ⊆ B → F ∈ A ↦ B.
Proof.
  intros F A B P1 P2 P3.
  apply sub_i.
  + apply power_i.
    intros x Q1.
    destruct (fn_rel _ P1 _ Q1) as [a [b Q2]].
    pose (eq_cl (λ x, x ∈ F) Q2 Q1) as Q3.
    apply (eq_cr (λ x, x ∈ _) Q2).
    apply cp_i.
    - apply (eq_cl (λ x, _ ∈ x) P2).
      apply (dom_i _ _ _ Q3).
    - apply P3.
      apply (ran_i _ _ _ Q3).
  + repeat split.
    - apply P1.
    - apply P1.
    - apply P2.
    - apply P3.
Qed.

Lemma fmap_r: ∀ F, fn F → F ∈ dom(F) ↦ ran(F).
Proof.
  intros F P1.
  apply sub_i.
  + apply power_i.
    intros x Q1.
    destruct (fn_rel _ P1 _ Q1) as [a [b Q2]].
    pose (eq_cl (λ x, x ∈ F) Q2 Q1) as Q3.
    apply (eq_cr (λ x, x ∈ _) Q2).
    apply cp_i.
    - apply (dom_i _ _ _ Q3).
    - apply (ran_i _ _ _ Q3).
  + repeat split.
    - apply P1.
    - apply P1.
    - apply sub_r.
Qed.

Lemma fmap_ran_exten: ∀ F, ∀ A, ∀ B, ∀ B', F ∈ A ↦ B → B ⊆ B' → F ∈ A ↦ B'.
Proof.
  intros F A B B' P1 P2.
  apply fmap_i.
  + apply (fmap_fn _ _ _ P1).
  + apply (fmap_dom _ _ _ P1).
  + pose (fmap_ran _ _ _ P1) as Q1.
    apply (sub_t _ _ _ Q1 P2).
Qed.
(*----------------------------------------------------------------------------*)

(* Surjective *)
Lemma surj_fn: ∀ F, ∀ A, ∀ B, F ∈ A ↦ˢ B → fn F.
Proof.
  intros F A B P1.
  destruct (sub_e _ _ _ P1) as [_ [P2 _]].
  apply P2.
Qed.

Lemma surj_dom: ∀ F, ∀ A, ∀ B, F ∈ A ↦ˢ B → dom(F) = A.
Proof.
  intros F A B P1.
  destruct (sub_e _ _ _ P1) as [_ [_ [P2 _]]].
  apply P2.
Qed.

Lemma surj_ran: ∀ F, ∀ A, ∀ B, F ∈ A ↦ˢ B → ran(F) = B.
Proof.
  intros F A B P1.
  destruct (sub_e _ _ _ P1) as [_ [_ [_ P2]]].
  apply P2.
Qed.

Lemma surj_fmap: ∀ F, ∀ A, ∀ B, F ∈ A ↦ˢ B → F ∈ A ↦ B.
Proof.
  intros F A B P1.
  apply fmap_i.
  + apply (surj_fn _ _ _ P1).
  + apply (surj_dom _ _ _ P1).
  + apply (eq_cr (λ x, x ⊆ _) (surj_ran _ _ _ P1)).
    apply sub_r.
Qed.

Lemma surj_i: ∀ F, ∀ A, ∀ B, fn F → dom(F) = A → ran(F) = B → F ∈ A ↦ˢ B.
Proof.
  intros F A B P1 P2 P3.
  apply sub_i.
  + apply power_i.
    intros x Q1.
    destruct (fn_rel _ P1 _ Q1) as [a [b Q2]].
    pose (eq_cl (λ x, x ∈ F) Q2 Q1) as Q3.
    apply (eq_cr (λ x, x ∈ _) Q2).
    apply cp_i.
    - apply (eq_cl (λ x, _ ∈ x) P2).
      apply (dom_i _ _ _ Q3).
    - apply (eq_cl (λ x, _ ∈ x) P3).
      apply (ran_i _ _ _ Q3).
  + repeat split.
    - apply P1.
    - apply P1.
    - apply P2.
    - apply P3.
Qed.

Lemma surj_i2: ∀ F, ∀ A, ∀ B, F ∈ A ↦ B → ran(F) = B → F ∈ A ↦ˢ B.
Proof.
  intros F A B P1 P2.
  apply surj_i.
  + apply (fmap_fn _ _ _ P1).
  + apply (fmap_dom _ _ _ P1).
  + apply P2.
Qed.

Lemma surj_r: ∀ F, fn F → F ∈ dom(F) ↦ˢ ran(F).
Proof.
  intros F P1.
  apply sub_i.
  + apply power_i.
    intros x Q1.
    destruct (fn_rel _ P1 _ Q1) as [a [b Q2]].
    pose (eq_cl (λ x, x ∈ F) Q2 Q1) as Q3.
    apply (eq_cr (λ x, x ∈ _) Q2).
    apply cp_i.
    - apply (dom_i _ _ _ Q3).
    - apply (ran_i _ _ _ Q3).
  + repeat split.
    - apply P1.
    - apply P1.
Qed.
(*----------------------------------------------------------------------------*)

(* Injective *)
Lemma inj_fn: ∀ F, ∀ A, ∀ B, F ∈ A ↦ⁱ B → fn F.
Proof.
  intros F A B P1.
  destruct (sub_e _ _ _ P1) as [_ [P2 _]].
  apply P2.
Qed.

Lemma inj_dom: ∀ F, ∀ A, ∀ B, F ∈ A ↦ⁱ B → dom(F) = A.
Proof.
  intros F A B P1.
  destruct (sub_e _ _ _ P1) as [_ [_ [P2 _]]].
  apply P2.
Qed.

Lemma inj_ran: ∀ F, ∀ A, ∀ B, F ∈ A ↦ⁱ B → ran(F) ⊆ B.
Proof.
  intros F A B P1.
  destruct (sub_e _ _ _ P1) as [_ [_ [_ [P2 _]]]].
  apply P2.
Qed.

Lemma inj_sing_rot: ∀ F, ∀ A, ∀ B, F ∈ A ↦ⁱ B → sing_rot F.
Proof.
  intros F A B P1.
  destruct (sub_e _ _ _ P1) as [_ [_ [_ [_ P2]]]].
  apply P2.
Qed.

Lemma inj_fmap: ∀ F, ∀ A, ∀ B, F ∈ A ↦ⁱ B → F ∈ A ↦ B.
Proof.
  intros F A B P1.
  apply fmap_i.
  + apply (inj_fn _ _ _ P1).
  + apply (inj_dom _ _ _ P1).
  + apply (inj_ran _ _ _ P1).
Qed.

Lemma inj_i: ∀ F, ∀ A, ∀ B, fn F → dom(F) = A → ran(F) ⊆ B → sing_rot F
  → F ∈ A ↦ⁱ B.
Proof.
  intros F A B P1 P2 P3 P4.
  apply sub_i.
  + apply power_i.
    intros x Q1.
    destruct (fn_rel _ P1 _ Q1) as [a [b Q2]].
    pose (eq_cl (λ x, x ∈ F) Q2 Q1) as Q3.
    apply (eq_cr (λ x, x ∈ _) Q2).
    apply cp_i.
    - apply (eq_cl (λ x, _ ∈ x) P2).
      apply (dom_i _ _ _ Q3).
    - apply P3.
      apply (ran_i _ _ _ Q3).
  + repeat split.
    - apply P1.
    - apply P1.
    - apply P2.
    - apply P3.
    - apply P4.
Qed.

Lemma inj_i2: ∀ F, ∀ A, ∀ B, F ∈ A ↦ B → sing_rot F → F ∈ A ↦ⁱ B.
Proof.
  intros F A B P1 P2.
  apply inj_i.
  + apply (fmap_fn _ _ _ P1).
  + apply (fmap_dom _ _ _ P1).
  + apply (fmap_ran _ _ _ P1).
  + apply P2.
Qed.

Lemma inj_ran_exten: ∀ F, ∀ A, ∀ B, ∀ B', F ∈ A ↦ⁱ B → B ⊆ B' → F ∈ A ↦ⁱ B'.
Proof.
  intros F A B B' P1 P2.
  apply inj_i2.
  + apply (fmap_ran_exten _ _ _ _ (inj_fmap _ _ _ P1) P2).
  + apply (inj_sing_rot _ _ _ P1).
Qed.
(*----------------------------------------------------------------------------*)

(* Bijective *)
Lemma bij_fn: ∀ F, ∀ A, ∀ B, F ∈ A ↦ᵇ B → fn F.
Proof.
  intros F A B P1.
  destruct (sub_e _ _ _ P1) as [_ [P2 _]].
  apply P2.
Qed.

Lemma bij_dom: ∀ F, ∀ A, ∀ B, F ∈ A ↦ᵇ B → dom(F) = A.
Proof.
  intros F A B P1.
  destruct (sub_e _ _ _ P1) as [_ [_ [P2 _]]].
  apply P2.
Qed.

Lemma bij_ran: ∀ F, ∀ A, ∀ B, F ∈ A ↦ᵇ B → ran(F) = B.
Proof.
  intros F A B P1.
  destruct (sub_e _ _ _ P1) as [_ [_ [_ [P2 _]]]].
  apply P2.
Qed.

Lemma bij_sing_rot: ∀ F, ∀ A, ∀ B, F ∈ A ↦ᵇ B → sing_rot F.
Proof.
  intros F A B P1.
  destruct (sub_e _ _ _ P1) as [_ [_ [_ [_ P2]]]].
  apply P2.
Qed.

Lemma bij_fmap: ∀ F, ∀ A, ∀ B, F ∈ A ↦ᵇ B → F ∈ A ↦ B.
Proof.
  intros F A B P1.
  apply fmap_i.
  + apply (bij_fn _ _ _ P1).
  + apply (bij_dom _ _ _ P1).
  + apply (eq_cr (λ x, x ⊆ _) (bij_ran _ _ _ P1)).
    apply sub_r.
Qed.

Lemma bij_i: ∀ F, ∀ A, ∀ B, fn F → dom(F) = A → ran(F) = B → sing_rot F
  → F ∈ A ↦ᵇ B.
Proof.
  intros F A B P1 P2 P3 P4.
  apply sub_i.
  + apply power_i.
    intros x Q1.
    destruct (fn_rel _ P1 _ Q1) as [a [b Q2]].
    pose (eq_cl (λ x, x ∈ F) Q2 Q1) as Q3.
    apply (eq_cr (λ x, x ∈ _) Q2).
    apply cp_i.
    - apply (eq_cl (λ x, _ ∈ x) P2).
      apply (dom_i _ _ _ Q3).
    - apply (eq_cl (λ x, _ ∈ x) P3).
      apply (ran_i _ _ _ Q3).
  + repeat split.
    - apply P1.
    - apply P1.
    - apply P2.
    - apply P3.
    - apply P4.
Qed.

Lemma bij_i2: ∀ F, ∀ A, ∀ B, F ∈ A ↦ B → ran(F) = B → sing_rot F → F ∈ A ↦ᵇ B.
Proof.
  intros F A B P1 P2 P3.
  apply bij_i.
  + apply (fmap_fn _ _ _ P1).
  + apply (fmap_dom _ _ _ P1).
  + apply P2.
  + apply P3.
Qed.

Lemma bij_i3: ∀ F, ∀ A, ∀ B, F ∈ A ↦ˢ B → F ∈ A ↦ⁱ B → F ∈ A ↦ᵇ B.
Proof.
  intros F A B P1 P2.
  apply bij_i.
  + apply (surj_fn _ _ _ P1).
  + apply (surj_dom _ _ _ P1).
  + apply (surj_ran _ _ _ P1).
  + apply (inj_sing_rot _ _ _ P2).
Qed.

Lemma bij_e: ∀ F, ∀ A, ∀ B, F ∈ A ↦ᵇ B → F ∈ A ↦ˢ B ∧ F ∈ A ↦ⁱ B.
Proof.
  intros F A B P1.
  split.
  + apply surj_i.
    - apply (bij_fn _ _ _ P1).
    - apply (bij_dom _ _ _ P1).
    - apply (bij_ran _ _ _ P1).
  + apply inj_i.
    - apply (bij_fn _ _ _ P1).
    - apply (bij_dom _ _ _ P1).
    - apply (eq_cr (λ x, x ⊆ _) (bij_ran _ _ _ P1)).
      apply sub_r.
    - apply (bij_sing_rot _ _ _ P1).
Qed.

Lemma inj_bij: ∀ F, ∀ A, ∀ B, F ∈ A ↦ⁱ B → F ∈ A ↦ᵇ ran(F).
Proof.
  intros F A B P1.
  apply bij_i.
  + apply (inj_fn _ _ _ P1).
  + apply (inj_dom _ _ _ P1).
  + apply eq_r.
  + apply (inj_sing_rot _ _ _ P1).
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
Notation   "F [ x ]"     := (fval F x).

(* Need Better Notation *)
(*[> Binary Function <]*)
(*Notation " x +[ r ] y" := (r[⟨x, y⟩]) (at level 63, left associativity).*)

Lemma fval_e: ∀ F, ∀ x, ∀y, F[x] = y → fn F → x ∈ dom(F) →
  ⟨x, y⟩ ∈ F ∧ (∀ y2, ⟨x, y2⟩ ∈ F → y = y2).
Proof.
  intros F x y P1.
  apply (eq_cr (λ y, _ → _ → ⟨ x, y ⟩ ∈ F ∧ (∀ y2, _ → y = y2)) (eq_s P1)).
  apply (ex_outr (fval_exist F x)).
Qed.

Lemma fval_e1: ∀ F, ∀ x, ∀ y, F[x] = y → fn F → x ∈ dom(F) → ⟨x, y⟩ ∈ F.
Proof.
  intros F x y P1 P2 P3.
  destruct (fval_e F x y P1 P2 P3) as [P4 _].
  apply P4.
Qed.

Lemma fval_e2: ∀ F, ∀ x, ∀ y, F[x] = y → fn F → x ∈ dom(F) → 
  (∀ y2, ⟨x, y2⟩ ∈ F → y = y2).
Proof.
  intros F x y P1 P2 P3.
  destruct (fval_e F x y P1 P2 P3) as [_ P4].
  apply P4.
Qed.

Lemma fval_i: ∀ F, ∀ x, ∀ y, fn F → ⟨x, y⟩ ∈ F → F[x] = y.
Proof.
  intros F x y P1 P2.
  destruct (ex_outr (fval_exist F x) P1 (dom_i _ _ _ P2)) as [_ P3].
  apply (P3 _ P2).
Qed.

Lemma fval_i2: ∀ F, ∀ x, fn F → x ∈ dom(F) → ⟨x, F[x]⟩ ∈ F.
Proof.
  intros F x P1 P2.
  destruct (dom_e _ _ P2) as [y P3].
  apply (eq_cr (λ y, ⟨x, y⟩ ∈ F) (fval_i _ _ _ P1 P3)).
  apply P3.
Qed.

Lemma fval_i3: ∀ F, ∀ A, ∀ B, ∀ x, F ∈ A ↦ B → x ∈ A → ⟨x, F[x]⟩ ∈ F.
Proof.
  intros F A B x P1 P2.
  apply fval_i2.
  + apply (fmap_fn _ _ _ P1).
  + apply (eq_cr _ (fmap_dom _ _ _ P1)).
    apply P2.
Qed.

Lemma fval_ran: ∀ F, ∀ x, fn F → x ∈ dom(F) → F[x] ∈ ran(F).
Proof.
  intros F x P1 P2.
  apply (ran_i _ x).
  apply (fval_i2 F x P1 P2).
Qed.

Lemma fval_codom: ∀ F, ∀ A, ∀ B, ∀ x, F ∈ A ↦ B → x ∈ A → F[x] ∈ B.
Proof.
  intros F A B x P1 P2.
  apply (fmap_ran _ _ _ P1).
  apply fval_ran.
  + apply (fmap_fn _ _ _ P1).
  + apply (eq_cr _ (fmap_dom _ _ _ P1)).
    apply P2.
Qed.

Lemma fval_inj: ∀ F, ∀ A, ∀ B, ∀ x, ∀ y, F ∈ A ↦ⁱ B → x ∈ A → y ∈ A
  → F[x] = F[y] → x = y.
Proof.
  intros F A B x y P1 P2 P3 P4.
  apply ((inj_sing_rot _ _ _ P1) _ _ (F[x])).
  + apply (fval_i2 _ _ (inj_fn _ _ _ P1)).
    apply (eq_cr _ (inj_dom _ _ _ P1) P2).
  + apply (eq_cr (λ x, ⟨y, x⟩ ∈ F) P4).
    apply (fval_i2 _ _ (inj_fn _ _ _ P1)).
    apply (eq_cr _ (inj_dom _ _ _ P1) P3).
Qed. 

Lemma fval_sub: ∀ F, ∀ G, ∀ x, fn F → fn G → F ⊆ G → x ∈ dom(F) → F[x] = G[x].
Proof.
  intros F G x P1 P2 P3 P4.
  destruct (dom_e _ _ P4) as [y P5].
  apply (eq_cr (λ y, y = G[x]) (fval_i _ _ _ P1 P5)).
  apply (eq_cr (λ x, y = x) (fval_i _ _ _ P2 (P3 _ P5))).
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
    apply (eq_cl (λ y, ⟨x, y⟩ ∈ G) (fval_i _ _ _ (and_i P1 P2) P9)).
    apply (eq_cr (λ y, ⟨x, y⟩ ∈ G) (P6 _ (dom_i _ _ _ P9))). 
    apply (fval_i2 _ _ (and_i P3 P4)).
    apply (eq_cl (λ y, x ∈ y) P5).
    apply (dom_i _ _ _ P9).
  + intros s P7.
    destruct (P3 _ P7) as [x [y P8]].
    apply (eq_cr (λ s, s ∈ F) P8).
    pose (eq_cl (λ s, s ∈ G) P8 P7) as P9.
    apply (eq_cl (λ y, ⟨x, y⟩ ∈ F) (fval_i _ _ _ (and_i P3 P4) P9)).
    apply (eq_cl (λ y, ⟨x, y⟩ ∈ F) 
      (P6 _ (eq_cr (λ y, x ∈ y) P5 (dom_i _ _ _ P9)))).
    apply (fval_i2 _ _ (and_i P1 P2)).
    apply (eq_cr (λ y, x ∈ y) P5).
    apply (dom_i _ _ _ P9).
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
  → ∃ x, ∃ y, ⟨x, y⟩ ∈ F ∧ s = ⟨x, y⟩ ∧ x ∈ A.
Proof.
  intros s F A P1.
  destruct (sub_e _ _ _ P1) as [_ P2].
  apply P2.
Qed.

Lemma restr_dom_e: ∀ x, ∀ F, ∀ A, x ∈ dom(F↾A) → x ∈ A ∧ ∃ y, ⟨x, y⟩ ∈ F.
Proof.
  intros x F A P1.
  destruct (dom_e _ _ P1) as [y P2].
  destruct (restr_e _ _ _ _ P2) as [P3 P4].
  split.
  + apply P4.
  + exists y.
    apply P3.
Qed.

Lemma restr_sub: ∀ F, ∀ A, ∀ B, A ⊆ B → F↾A ⊆ F↾B.
Proof.
  intros F A B P1 s P2.
  destruct (restr_e2 _ _ _ P2) as [x [y [P3 [P4 P5]]]].
  apply (eq_cr (λ x, x ∈ F↾B) P4).
  apply restr_i.
  + apply P3.
  + apply (P1 _ P5).
Qed.

Lemma restr_rel: ∀ F, ∀ A, rel (F↾A).
Proof.
  intros F A r P1.
  destruct (sub_e _ _ _ P1) as [_ [a [b [_ [P2 _]]]]].
  exists a.
  exists b.
  apply P2.
Qed.

Lemma restr_sing_val: ∀ F, ∀ A, sing_val F → sing_val (F↾A).
Proof.
  intros F A P1 x y1 y2 P2 P3.
  destruct (restr_e _ _ _ _ P2) as [P4 _].
  destruct (restr_e _ _ _ _ P3) as [P5 _].
  apply (P1 _ _ _ P4 P5).
Qed.

Lemma restr_sing_rot: ∀ F, ∀ A, sing_rot F → sing_rot (F↾A).
Proof.
  intros F A P1 x y1 y2 P2 P3.
  destruct (restr_e _ _ _ _ P2) as [P4 _].
  destruct (restr_e _ _ _ _ P3) as [P5 _].
  apply (P1 _ _ _ P4 P5).
Qed.

Lemma restr_fn: ∀ F, ∀ A, fn F → fn (F↾A).
Proof.
  intros F A [_ P1].
  split.
  + apply restr_rel.
  + apply (restr_sing_val _ _ P1).
Qed.

Lemma restr_dom: ∀ F, ∀ A, dom(F↾A) = dom(F) ∩ A.
Proof.
  intros F A.
  apply sub_a.
  split.
  + intros x P1.
    destruct (dom_e _ _ P1) as [y P2].
    destruct (restr_e _ _ _ _ P2) as [P3 P4].
    apply inter2_i.
    - apply (dom_i _ _ _ P3).
    - apply P4.
  + intros x P1.
    destruct (inter2_e _ _ _ P1) as [P2 P3].
    destruct (dom_e _ _ P2) as [y P4].
    apply (dom_i _ _ y).
    apply restr_i.
    - apply P4.
    - apply P3.
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
    - apply (eq_cl (λ y, ⟨x, y⟩ ∈ F) (fval_i _ _ _ P2 P6)). 
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
    - pose (dom_i _ _ _ (eq_cl (λ x, x ∈ F) P4 P3)) as P5.
      apply (P2 _ P5).
Qed.

Lemma restr_bij: ∀ F, ∀ A, ∀ B, ∀ A', F ∈ A ↦ᵇ B → A' ⊆ A
  → F↾A' ∈ A' ↦ᵇ F⟦A'⟧.
Proof.
  intros F A B A' P1 P2.
  apply bij_i.
  + apply (restr_fn _ _ (bij_fn _ _ _ P1)).
  + apply (eq_cr (λ x, x = A') (restr_dom _ _)).
    apply inter2_absorb_r.
    apply (eq_cr (λ x, A' ⊆ x) (bij_dom _ _ _ P1) P2).
  + apply eq_r.
  + apply (restr_sing_rot _ _ (bij_sing_rot _ _ _ P1)).
Qed.

Lemma restr_fval: ∀ F, ∀ A, ∀ x, fn F → x ∈ dom(F) → x ∈ A → F[x] = (F↾A)[x].
Proof.
  intros F A x P1 P2 P3.
  apply eq_s.
  apply fval_i.
  + apply (restr_fn _ _ P1).
  + apply restr_i.
    - apply (fval_i2 _ _ P1 P2).
    - apply P3.
Qed.

Lemma restr_fval2: ∀ F, ∀ A, ∀ x, fn F → x ∈ dom(F) → x ∈ A
  → ⟨x, F[x]⟩ ∈ (F↾A).
Proof.
  intros F A x P1 P2 P3.
  apply restr_i.
  + apply (fval_i2 _ _ P1 P2).
  + apply P3.
Qed.
(*----------------------------------------------------------------------------*)

(* Image *)
Theorem image_i: ∀ y, ∀ F, ∀ A, (∃ x, ⟨x, y⟩ ∈ F ∧ x ∈ A) → y ∈ F⟦A⟧.
Proof.
  intros y F A [x [P1 P2]].
  apply (ran_i _ x).
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

Lemma image_e2: ∀ x, ∀ F, ∀ A, ∀ B, ∀ C, F ∈ A ↦ⁱ B → x ∈ A → F[x] ∈ F⟦C⟧
  → x ∈ C.
Proof.
  intros x F A B C P1 P2 P3.
  destruct (image_e _ _ _ P3) as [x' [P4 P5]].
  assert (x = x') as P6.
  { apply (fval_inj _ _ _ _ _ P1 P2).
    + apply (eq_cl (λ x, x' ∈ x) (inj_dom _ _ _ P1)).
      apply (dom_i _ _ _ P4).
    + apply eq_s.
      apply fval_i.
      - apply (inj_fn _ _ _ P1).
      - apply P4. }
  apply (eq_cr (λ x, x ∈ C) P6 P5).
Qed.

Lemma image_sub: ∀ F, ∀ A, ∀ B, A ⊆ B → F⟦A⟧ ⊆ F⟦B⟧.
Proof.
  intros F A B P1 y P2.
  destruct (image_e _ _ _ P2) as [x [P3 P4]].
  apply image_i.
  exists x.
  split.
  + apply P3.
  + apply (P1 _ P4).
Qed.

Lemma image_fmap: ∀ F, ∀ A, ∀ B, ∀ C, F ∈ A ↦ B → F⟦C⟧ ⊆ B.
Proof.
  intros F A B C P1 y P2.
  destruct (image_e _ _ _ P2) as [x [P3 P4]].
  apply (fmap_ran _ _ _ P1).
  apply (ran_i _ _ _ P3).
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
  apply (ran_i _ _ _ P2).
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
    - apply (dom_i _ _ _ P2).
Qed.

Lemma image_sub_dom_eq: ∀ F, ∀ G, ∀ A, fn G → F ⊆ G → A ⊆ dom(F) 
  → F⟦A⟧ = G⟦A⟧.
Proof.
  intros F G A P2 P3 P4.
  apply sub_a.
  split.
  + intros y P5.
    destruct (image_e _ _ _ P5) as [x [P6 P7]].
    apply image_i.
    exists x.
    split.
    - apply (P3 _ P6).
    - apply P7.
  + intros y P5.
    destruct (image_e _ _ _ P5) as [x [P6 P7]].
    apply image_i.
    exists x.
    split.
    - destruct (dom_e _ _ (P4 _ P7)) as [y' P8].
      destruct P2 as [_ P2].
      apply (eq_cr (λ y, ⟨x, y⟩ ∈ F) (P2 _ _ _ P6 (P3 _ P8))).
      apply P8.
    - apply P7.
Qed.

Lemma image_surj: ∀ F, ∀ A, ∀ B, F ∈ A ↦ˢ B → F⟦A⟧ = B.
Proof.
  intros F A B P1.
  apply sub_a.
  split.
  + apply (eq_cl _ (surj_ran _ _ _ P1)).
    apply image_ran.
  + intros y P3.
    destruct (ran_e _ _ (eq_cr _ (surj_ran _ _ _ P1) P3)) as [x P4].
    apply image_i.
    exists x.
    split.
    - apply P4.
    - apply (eq_cl _ (surj_dom _ _ _ P1)).
      apply (dom_i _ _ _ P4).
Qed.

Lemma image_bij_psub: ∀ F, ∀ A, ∀ A', ∀ B, F ∈ A ↦ᵇ B → A' ⊂ A → F⟦A'⟧ ⊂ B.
Proof.
  intros F A A' B P1 P2.
  apply psub_i.
  + intros y P3.
    destruct (image_e _ _ _ P3) as [x [P4 _]].
    apply (eq_cl (λ x, y ∈ x) (bij_ran _ _ _ P1)).
    apply (ran_i _ _ _ P4).
  + destruct (psub_e2 _ _ P2) as [x [P3 P4]].
    apply neq_s.
    apply (neq_i _ _ (F[x])).
    - apply (eq_cl (λ y, _ ∈ y) (bij_ran _ _ _ P1)).
      apply fval_ran.
      * apply (bij_fn _ _ _ P1).
      * apply (eq_cr (λ y, x ∈ y) (bij_dom _ _ _ P1) P4).
    - intros P5.
      destruct (image_e _ _ _ P5) as [x' [P6 P7]].
      assert (x' = x) as P8.
      { destruct (bij_e _ _ _ P1) as [_ Q1].
        apply (fval_inj _ _ _ _ _ Q1 (psub_e _ _ P2 _ P7) P4).
        + apply fval_i.
          - apply (bij_fn _ _ _ P1).
          - apply P6. }
      apply P3.
      apply (eq_cl (λ x, x ∈ A') P8 P7).
Qed.
(*----------------------------------------------------------------------------*)

(* Inverse *)
Lemma inv_i: ∀ x, ∀ y, ∀ R, ⟨x, y⟩ ∈ R → ⟨y, x⟩ ∈ R⁻¹.
Proof.
  intros x y R P1.
  apply sub_i.
  + apply cp_i.
    - apply (ran_i _ _ _ P1).
    - apply (dom_i _ _ _ P1).
  + exists x.
    exists y.
    split.
    - apply P1.
    - apply eq_r.
Qed.

Lemma inv_e: ∀ x, ∀ y, ∀ R, ⟨x, y⟩ ∈ R⁻¹ → ⟨y, x⟩ ∈ R.
Proof.
  intros x y R P1.
  destruct (sub_e _ _ _ P1) as [_ [a [b [P2 P3]]]].
  apply (eq_cr (λ x, ⟨y, x⟩ ∈ R) (opair_eq_el _ _ _ _ P3)).
  apply (eq_cr (λ y, ⟨y, b⟩ ∈ R) (opair_eq_er _ _ _ _ P3)).
  apply P2.
Qed.

Lemma inv_rel: ∀ R, rel (R⁻¹).
Proof.
  intros R x P1.
  destruct (sub_e _ _ _ P1) as [P2 _].
  destruct (cp_e _ _ _ P2) as [a [b [_ [_ P3]]]]. 
  exists a.
  exists b.
  apply P3.
Qed.

Theorem inv_inv: ∀ F, rel F → (F⁻¹)⁻¹ = F.
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
Lemma inv_dom: ∀ F, dom(F⁻¹) = ran(F).
Proof.
  intros F.
  apply sub_a.
  split.
  + intros x P1.
    destruct (dom_e _ _ P1) as [y P2].
    apply (ran_i _ y).
    apply (inv_e _ _ _ P2).
  + intros x P1.
    destruct (ran_e _ _ P1) as [y P2].
    apply (dom_i _ _ y).
    apply (inv_i _ _ _ P2).
Qed.
    
Lemma inv_ran: ∀ F, ran(F⁻¹) = dom(F).
Proof.
  intros F.
  apply sub_a.
  split.
  + intros x P1.
    destruct (ran_e _ _ P1) as [y P2].
    apply (dom_i _ _ y).
    apply (inv_e _ _ _ P2).
  + intros x P1.
    destruct (dom_e _ _ P1) as [y P2].
    apply (ran_i _ y).
    apply (inv_i _ _ _ P2).
Qed.

Lemma inv_sing_rot: ∀ R, sing_rot R → sing_val (R⁻¹).
Proof.
  intros R P1 a b1 b2 P2 P3.
  apply (P1 _ _ _ (inv_e _ _ _ P2) (inv_e _ _ _ P3)).
Qed.

Lemma inv_sing_val: ∀ R, sing_val R → sing_rot (R⁻¹).
Proof.
  intros R P1 a b1 b2 P2 P3.
  apply (P1 _ _ _ (inv_e _ _ _ P2) (inv_e _ _ _ P3)).
Qed.

Lemma sing_rot_inv: ∀ R, sing_val (R⁻¹) → sing_rot R.
Proof.
  intros R P1 a1 a2 b P2 P3.
  apply (P1 _ _ _ (inv_i _ _ _ P2) (inv_i _ _ _ P3)).
Qed.

Lemma sing_val_inv: ∀ R, sing_rot (R⁻¹) → sing_val R.
Proof.
  intros R P1 a1 a2 b P2 P3.
  apply (P1 _ _ _ (inv_i _ _ _ P2) (inv_i _ _ _ P3)).
Qed.

(* 3F *)
Lemma inv_fn: ∀ F, sing_rot F → fn (F⁻¹).
Proof.
  intros F P1.
  split.
  + apply inv_rel.
  + apply (inv_sing_rot _ P1).
Qed.

Lemma inv_fn_sing_rot: ∀ F, fn (F⁻¹) → sing_rot F.
Proof.
  intros F [_ P1] a1 a2 b P2 P3.
  apply (P1 b a1 a2).
  + apply (inv_i _ _ _ P2).
  + apply (inv_i _ _ _ P3).
Qed.

Lemma fn_inv_sing_rot: ∀ F, fn F → sing_rot (F⁻¹).
Proof.
  intros F [_ P1] a1 a2 b P2 P3.
  apply (P1 b a1 a2).
  + apply (inv_e _ _ _ P2).
  + apply (inv_e _ _ _ P3).
Qed.

Lemma inv_sing_rot_fn: ∀ F, rel F → sing_rot (F⁻¹) → fn F.
Proof.
  intros F P1 P2.
  split.
  + apply P1.
  + apply (sing_val_inv _ P2).
Qed.

(* 3G *)
Lemma inv_fval_cancel1: ∀ F, ∀ A, ∀ B, ∀ x, F ∈ A ↦ⁱ B → x ∈ A → F⁻¹[F[x]] = x.
Proof.
  intros F A B x P1 P2.
  apply fval_i.
  + apply inv_fn.
    apply (inj_sing_rot _ _ _ P1).
  + apply inv_i.
    apply (fval_i2 _ _ (inj_fn _ _ _ P1)).
    apply (eq_cr _ (inj_dom _ _ _ P1) P2).
Qed.

Lemma inv_fval_cancel2: ∀ F, ∀ A, ∀ B, ∀ x, F ∈ A ↦ⁱ B → x ∈ ran(F)
  → F[F⁻¹[x]] = x.
Proof.
  intros F x A B P1 P2.
  apply fval_i.
  + apply (inj_fn _ _ _ P1).
  + apply inv_e.
    apply fval_i2.
    - apply (inv_fn _ (inj_sing_rot _ _ _ P1)).
    - apply (eq_cr _ (inv_dom F) P2).
Qed.

Lemma inv_bij: ∀ F, ∀ A, ∀ B, F ∈ A ↦ᵇ B → F⁻¹ ∈ B ↦ᵇ A.
Proof.
  intros F A B P1.
  apply bij_i.
  + apply (inv_fn _ (bij_sing_rot _ _ _ P1)).
  + apply (eq_cr (λ x, x = B) (inv_dom F)).
    apply (bij_ran _ _ _ P1).
  + apply (eq_cr (λ x, x = A) (inv_ran F)).
    apply (bij_dom _ _ _ P1).
  + apply inv_sing_val.
    apply (bij_fn _ _ _ P1).
Qed.

Lemma inv_image_ran: ∀ F, ∀ A, F⁻¹⟦A⟧ ⊆ dom(F).
Proof. 
  intros F A.
  apply (eq_cl _ (inv_ran F)).
  apply image_ran.
Qed.
(*----------------------------------------------------------------------------*)

(* Composition *)
(* Only consider composition of two functions *)
Lemma comp_i: ∀ x, ∀ z, ∀ F, ∀ G, (∃ y, ⟨x, y⟩ ∈ F ∧ ⟨y, z⟩ ∈ G)
  → ⟨x, z⟩ ∈ G ∘ F.
Proof.
  intros x z F G [y [P1 P2]].
  apply sub_i.
  + apply cp_i.
    - apply (dom_i _ _ _ P1).
    - apply (ran_i _ _ _ P2).
  + exists x. exists y. exists z.
    repeat split.
    - apply P1.
    - apply P2.
Qed.

Lemma comp_e: ∀ x, ∀ z, ∀ F, ∀ G, ⟨x, z⟩ ∈ G ∘ F
  → (∃ y, ⟨x, y⟩ ∈ F ∧ ⟨y, z⟩ ∈ G).
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

Lemma comp_rel: ∀ F, ∀ G, rel(G ∘ F).
Proof.
  intros F G.
  apply cp_sub_rel.
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
  apply (dom_i _ _ y P3).
Qed.

Lemma comp_coin_dom: ∀ F, ∀ G, ran(F) = dom(G) → dom(G ∘ F) = dom(F).
Proof.
  intros F G P1.
  apply sub_a.
  split.
  + apply comp_dom.
  + intros x P2.
    destruct (dom_e _ _ P2) as [y P3].
    pose (eq_cl _ P1 (ran_i _ _ _ P3)) as P4.
    destruct (dom_e _ _ P4) as [z P5].
    apply (dom_i _ _ z).
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
    pose (P1 _ (ran_i _ _ _ P3)) as P4.
    destruct (dom_e _ _ P4) as [z P5].
    apply (dom_i _ _ z).
    apply comp_i.
    exists y.
    apply (and_i P3 P5).
Qed.

Lemma comp_dom_fmap: ∀ F, ∀ G, ∀ A, ∀ B, ∀ C, F ∈ A ↦ B → G ∈ B ↦ C 
  → dom (G ∘ F) = A.
Proof.
  intros F G A B C P1 P2.
  apply (eq_cl (λ x, _ = x) (fmap_dom _ _ _ P1)).
  apply comp_coin_dom_weak.
  apply (eq_cr (λ x, _ ⊆ x) (fmap_dom _ _ _ P2)).
  apply (fmap_ran _ _ _ P1).
Qed.

Lemma comp_dom_e: ∀ F, ∀ G, ∀ x, fn F → fn G → x ∈ dom(G ∘ F) → F[x] ∈ dom(G).
Proof.
  intros F G x P1 P2 P3.
  destruct (dom_e _ _ P3) as [z P4].
  destruct (comp_e _ _ _ _ P4) as [y [P5 P6]].
  apply (dom_i _ _ z).
  apply (eq_cr (λ x, ⟨x, z⟩ ∈ G) (fval_i _ _ _ P1 P5)).
  apply P6.
Qed.

Lemma comp_ran: ∀ F, ∀ G, ran(G ∘ F) ⊆ ran(G).
Proof.
  intros F G z P1.
  destruct (ran_e _ _ P1) as [x P2].
  destruct (comp_e _ _ _ _ P2) as [y [_ P3]].
  apply (ran_i _ y _ P3).
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
    - apply (ran_i _ _ _ P3).
  + intros z P1.
    destruct (image_e _ _ _ P1) as [y [P2 P3]].
    destruct (ran_e _ _ P3) as [x P4].
    apply (ran_i _ x _).
    apply (comp_i).
    exists y.
    apply (and_i P4 P2).
Qed.

Lemma comp_fmap: ∀ F, ∀ G, ∀ A, ∀ B, ∀ C, F ∈ A ↦ B → G ∈ B ↦ C → G ∘ F ∈ A ↦ C.
Proof.
  intros F G A B C P1 P2.
  apply fmap_i.
  + apply (comp_fn _ _ (fmap_fn _ _ _ P1) (fmap_fn _ _ _ P2)).
  + apply (eq_cl _ (fmap_dom _ _ _ P1)). 
    apply comp_coin_dom_weak.
    apply (eq_cr _ (fmap_dom _ _ _ P2)).
    apply (fmap_ran _ _ _ P1).
  + apply (sub_t _ (ran(G)) _).
    - apply comp_ran.
    - apply (fmap_ran _ _ _ P2).
Qed.

Lemma comp_fval: ∀ F, ∀ G, ∀ x, fn F → fn G → x ∈ dom(G ∘ F) → 
  G[F[x]] = (G ∘ F)[x].
Proof.
  intros F G x P1 P2 P3.
  apply eq_s.
  apply (fval_i _ _ _ (comp_fn _ _ P1 P2)).
  apply comp_i.
  exists (F[x]).
  split.
  + apply (fval_i2 _ _ P1).
    apply (comp_dom _ _ _ P3).
  + apply (fval_i2 _ _ P2).
    apply (comp_dom_e _ _ _ P1 P2 P3).
Qed.

Lemma comp_inj: ∀ F, ∀ G, ∀ A, ∀ B, ∀ C, F ∈ A ↦ⁱ B → G ∈ B ↦ⁱ C 
  → G ∘ F ∈ A ↦ⁱ C.
Proof.
  intros F G A B C P1 P2.
  apply inj_i2.
  + apply (comp_fmap _ _ _ _ _ (inj_fmap _ _ _ P1) (inj_fmap _ _ _ P2)).
  + apply (comp_sing_rot _ _ (inj_sing_rot _ _ _ P1) (inj_sing_rot _ _ _ P2)).
Qed.

Lemma comp_surj: ∀ F, ∀ G, ∀ A, ∀ B, ∀ C, F ∈ A ↦ˢ B → G ∈ B ↦ˢ C 
  → G ∘ F ∈ A ↦ˢ C.
Proof.
  intros F G A B C P1 P2.
  apply surj_i2.
  + apply (comp_fmap _ _ _ _ _ (surj_fmap _ _ _ P1) (surj_fmap _ _ _ P2)).
  + apply (eq_cr (λ x, x  = C) (comp_ran2 F G)).
    apply (eq_cr (λ x, G⟦x⟧ = C) (surj_ran _ _ _ P1)).
    apply (eq_cl (λ x, G⟦x⟧ = C) (surj_dom _ _ _ P2)).
    apply (eq_cl (λ x, G⟦dom(G)⟧ = x) (surj_ran _ _ _ P2)).
    apply image_dom.
Qed.

Lemma comp_bij: ∀ F, ∀ G, ∀ A, ∀ B, ∀ C, F ∈ A ↦ᵇ B → G ∈ B ↦ᵇ C 
  → G ∘ F ∈ A ↦ᵇ C.
Proof.
  intros F G A B C P1 P2.
  destruct (bij_e _ _ _ P1) as [P3 P4].
  destruct (bij_e _ _ _ P2) as [P5 P6].
  apply bij_i3.
  + apply (comp_surj _ _ _ _ _ P3 P5).
  + apply (comp_inj _ _ _ _ _ P4 P6).
Qed.

Lemma comp_bij_weak: ∀ F, ∀ G, ∀ A, ∀ B1, ∀ B2, ∀ C, F ∈ A ↦ᵇ B1 → G ∈ B2 ↦ᵇ C 
  → B1 ⊆ B2 → G ∘ F ∈ A ↦ᵇ G⟦B1⟧.
Proof.
  intros F G A B1 B2 C P1 P2 P3.
  apply bij_i.
  + apply (comp_fn _ _ (bij_fn _ _ _ P1) (bij_fn _ _ _ P2)).
  + apply sub_a.
    split.
    - apply (eq_cl (λ x, _ ⊆ x) (bij_dom _ _ _ P1)).
      apply comp_dom.
    - intros x P4.
      apply (dom_i _ _ (G[F[x]])).
      apply comp_i.
      exists (F[x]).
      split.
      * apply fval_i2.
        ++apply (bij_fn _ _ _ P1).
        ++apply (eq_cr (λ y, x ∈ y) (bij_dom _ _ _ P1) P4).
      * apply fval_i2.
        ++apply (bij_fn _ _ _ P2).
        ++apply (eq_cr (λ y, F[x] ∈ y) (bij_dom _ _ _ P2)).
          apply P3.
          apply (eq_cl (λ y, F[x] ∈ y) (bij_ran _ _ _ P1)).
          apply (fval_ran _ _ (bij_fn _ _ _ P1)).
          apply (eq_cr (λ y, x ∈ y) (bij_dom _ _ _ P1) P4).
  + apply sub_a.
    split.
    - intros y P4.
      destruct (ran_e _ _ P4) as [x P5].
      destruct (comp_e _ _ _ _ P5) as [s [P6 P7]].
      apply image_i.
      exists s.
      split.
      * apply P7.
      * apply (eq_cl (λ x, s ∈ x) (bij_ran _ _ _ P1)).
        apply (ran_i _ _ _ P6).
    - intros y P4.
      destruct (image_e _ _ _ P4) as [x [P5 P6]].
      apply (ran_i _ ((inv F)[x])).
      apply comp_i.
      exists x.
      split.
      * apply inv_e.
        apply fval_i2.
        ++apply inv_fn.
          apply (bij_sing_rot _ _ _ P1).
        ++apply (eq_cr (λ y, x ∈ y) (inv_dom _)).
          apply (eq_cr (λ s, x ∈ s) (bij_ran _ _ _ P1)).
          apply P6.
      * apply P5.
  + apply comp_sing_rot.
    - apply (bij_sing_rot _ _ _ P1).
    - apply (bij_sing_rot _ _ _ P2).
Qed.

(* 3I *)
Lemma comp_inv: ∀ F, ∀ G, (G ∘ F)⁻¹ = F⁻¹ ∘ G⁻¹.
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
