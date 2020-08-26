Require Import Init.Init.

Definition rel (R: J) := ∀ r, r ∈ R → ∃ a, ∃ b, r = ⟨a, b⟩.

Definition in_dom (x R: J) := ∃ y, ⟨x, y⟩ ∈ R.
Definition dom    (A: J)   := {x: ∪(∪(A))| in_dom x A}.
Notation   "dom( A )"      := (dom A).

Definition in_ran (y R: J) := ∃ x, ⟨x, y⟩ ∈ R.
Definition ran (A: J)      := {x: ∪(∪(A))| in_ran x A}.
Notation   "ran( A )"      := (ran A).

Definition filed (R: J) := (dom(R) ∪ ran(R)).
Notation   "fld( A )"   := (filed A).

Definition r_refl    (R A: J) := ∀ x, x ∈ A → ⟨x, x⟩ ∈ R.
Definition r_irrefl  (R A: J) := ∀ x, x ∈ A → ⟨x, x⟩ ∉ R.
Definition r_sym     (R A: J) := ∀ x, ∀ y, x ∈ A → y ∈ A → ⟨x, y⟩ ∈ R 
  → ⟨y, x⟩ ∈ R.
Definition r_antisym (R A: J) := ∀ x, ∀ y, x ∈ A → y ∈ A → ⟨x, y⟩ ∈ R 
  → ⟨y, x⟩ ∈ R → x = y.
Definition r_asym    (R A: J) := ∀ x, ∀ y, x ∈ A → y ∈ A → ⟨x, y⟩ ∈ R 
  → ⟨y, x⟩ ∉ R.
Definition r_trans   (R A: J) := ∀ x, ∀ y, ∀ z, x ∈ A → y ∈ A → z ∈ A 
  → ⟨x, y⟩ ∈ R → ⟨y, z⟩ ∈ R → ⟨x, z⟩ ∈ R.

Definition r_over (R A: J) := (rel R) ∧ (dom(R) ⊆ A) ∧ (ran(R) ⊆ A).  

(* Relation *)
Lemma sub_rel: ∀ R, ∀ S, rel R → S ⊆ R → rel S.
Proof.
  intros R S P1 P2 x P3.
  apply (P1 _ (P2 _ P3)).
Qed.

Lemma cp_rel: ∀ A, ∀ B, rel (A ⨉ B).
Proof.
  intros A B x P1.
  destruct (cp_e _ _ _ P1) as [a [b [_ [_ P2]]]].
  exists a.
  exists b.
  apply P2.
Qed.

Lemma cp_sub_rel: ∀ₚ P, ∀ A, ∀ B, rel {x: (A ⨉ B)| P x}.
Proof. 
  intros P A B.
  apply (sub_rel (cp A B) _).
  + apply cp_rel.
  + apply sub_e1.
Qed.
(*----------------------------------------------------------------------------*)

(* Domain *)
Lemma dom_superset: ∀ A, ∀ x, in_dom x A → x ∈ ∪(∪(A)).
Proof.
  intros A x [y P1].
  apply union_i.
  exists (J{x, y}).
  split.
  + apply union_i.
    exists (⟨x, y⟩).
    split.
    - apply P1.
    - apply pair_ir.
  + apply pair_il.
Qed.

Lemma in_dom_i: ∀ R, ∀ x, ∀ y, ⟨x, y⟩ ∈ R → in_dom x R.
Proof.
  intros R x y P1.
  exists y.
  apply P1.
Qed.

Lemma dom_i: ∀ R, ∀ x, in_dom x R → x ∈ dom(R).
Proof.
  intros R x [y P1].
  apply sub_i.
  + apply dom_superset.
    exists y.
    apply P1.
  + exists y.
    apply P1.
Qed.

Lemma dom_i2: ∀ R, ∀ x, ∀ y, ⟨x, y⟩ ∈ R → x ∈ dom(R).
Proof.
  intros R x y P1.
  apply dom_i.
  apply (in_dom_i R x y P1).
Qed.

Lemma dom_e: ∀ R, ∀ x, x ∈ dom(R) → in_dom x R.
Proof.
  intros R x P1.
  destruct (sub_e _ _ _ P1) as [_ P2].
  apply P2.
Qed.

Lemma sub_dom: ∀ F, ∀ G, F ⊆ G → dom(F) ⊆ dom(G).
Proof.
  intros F G P1 x P2.
  destruct (dom_e _ _ P2) as [y P3].
  apply (dom_i2 _ _ _ (P1 _ P3)).
Qed.

Lemma nin_dom: ∀ F, ∀ x, x ∉ dom(F) → ∀ y, ⟨x, y⟩ ∉ F.
Proof. 
  intros F x P1 y P2.
  apply P1.
  apply (dom_i2 _ _ _ P2).
Qed.

Lemma cp_dom: ∀ A, ∀ B, B ≠ ∅ → dom(A ⨉ B) = A.
Proof.
  intros A B P1.
  apply sub_a.
  split.
  + intros x P2.
    destruct (dom_e _ _ P2) as [y P3].
    destruct (cp_e2 _ _ _ _ P3) as [P4 _].
    apply P4.
  + intros x P2.
    destruct (nempty_ex _ P1) as [y P3].
    apply (dom_i2 _ _ y).
    apply (cp_i _ _ _ _ P2 P3).
Qed.

Lemma cp_sub_dom: ∀ R, ∀ A, ∀ B, R ⊆ (A ⨉ B) → dom(R) ⊆ A.
Proof.
  intros R A B P1 x P2.
  destruct (dom_e _ _ P2) as [y P3].
  destruct (cp_e2 _ _ _ _ (P1 _ P3)) as [P4 _].
  apply P4.
Qed.
(*----------------------------------------------------------------------------*)

(* Range *)
Lemma ran_superset: ∀ A, ∀ y, in_ran y A → y ∈ ∪(∪(A)).
Proof.
  intros A y [x P1].
  apply union_i.
  exists (J{x, y}).
  split.
  + apply union_i.
    exists (⟨x, y⟩).
    split.
    - apply P1.
    - apply pair_ir.
  + apply pair_ir.
Qed.

Lemma in_ran_i: ∀ R, ∀ x, ∀ y, ⟨x, y⟩ ∈ R → in_ran y R.
Proof.
  intros R x y P1.
  exists x.
  apply P1.
Qed.

Lemma ran_i: ∀ R, ∀ y, in_ran y R → y ∈ ran(R).
Proof.
  intros R y [x P1].
  apply sub_i.
  + apply ran_superset.
    exists x.
    apply P1.
  + exists x.
    apply P1.
Qed.

Lemma ran_i2: ∀ R, ∀ x, ∀ y, ⟨x, y⟩ ∈ R → y ∈ ran(R).
Proof.
  intros R x y P1.
  apply ran_i.
  apply (in_ran_i _ _ _ P1).
Qed.

Lemma ran_e: ∀ R, ∀ y, y ∈ ran(R) → in_ran y R.
Proof.
  intros R y P1.
  destruct (sub_e _ _ _ P1) as [_ P2].
  apply P2.
Qed.

Lemma sub_ran: ∀ F, ∀ G, F ⊆ G → ran(F) ⊆ ran(G).
Proof.
  intros F G P1 y P2.
  destruct (ran_e _ _ P2) as [x P3].
  apply (ran_i2 _ _ _ (P1 _ P3)). 
Qed.

Lemma cp_ran: ∀ A, ∀ B, A ≠ ∅ → ran(A ⨉ B) = B.
Proof.
  intros A B P1.
  apply sub_a.
  split.
  + intros y P2.
    destruct (ran_e _ _ P2) as [x P3].
    destruct (cp_e2 _ _ _ _ P3) as [_ P4].
    apply P4.
  + intros y P2.
    destruct (nempty_ex _ P1) as [x P3].
    apply (ran_i2 _ x _).
    apply (cp_i _ _ _ _ P3 P2).
Qed.

Lemma cp_sub_ran: ∀ R, ∀ A, ∀ B, R ⊆ cp A B → ran(R) ⊆ B.
Proof.
  intros R A B P1 y P2.
  destruct (ran_e _ _ P2) as [x P3].
  destruct (cp_e2 _ _ _ _ (P1 _ P3)) as [_ P4].
  apply P4.
Qed.
(*----------------------------------------------------------------------------*)

(* Filed *)
Lemma fld_e: ∀ x, ∀ A, x ∈ fld(A) → x ∈ dom(A) ∨ x ∈ ran(A).
Proof.
  intros x A P1.
  destruct (union2_e _ _ _ P1) as [P2 | P2].
  + left.
    apply P2.
  + right.
    apply P2.
Qed.

Lemma fld_id: ∀ x, ∀ A, x ∈ dom(A) → x ∈ fld(A).
Proof.
  intros x A P1.
  apply (union2_il _ _ _ P1).
Qed.

Lemma fld_ir: ∀ x, ∀ A, x ∈ ran(A) → x ∈ fld(A).
Proof.
  intros x A P1.
  apply (union2_ir _ _ _ P1).
Qed.
(*----------------------------------------------------------------------------*)
