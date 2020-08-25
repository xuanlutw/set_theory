Set Implicit Arguments.

Require Export Coq.Init.Ltac.
Require Export Init.Notations.

(* Truth *)
Inductive True: Prop :=
  | tt: True.

Inductive False: Prop :=.

Notation "⊤" := True.
Notation "⊥" := False.

(* Implication *)
Notation "A → B" := (forall (_: A), B).

(* Negation *)
Definition not (A: Prop) := A → ⊥.

Notation "~ x" := (not x).

(* Conjunction *)
Inductive and (A B: Prop): Prop :=
  | conj: A → B → and A B.

Notation "A ∧ B" := (and A B).

(* Disjunction *)
Inductive or (A B: Prop): Prop :=
  | inl: A → or A B
  | inr: B → or A B.

Notation "A ∨ B" := (or A B).

(* If and Only If *)
Notation "A ↔ B" := ((A → B) ∧ (B → A)).

(* Basic Properties of Logic *)
Section Logic.
  Variable P Q R S : Prop.
  
  Lemma bot_e: ⊥ → P.
  Proof.
    intros [].
  Qed.

  Lemma and_i: P → Q → P ∧ Q.
  Proof.
    intros P1 P2.
    apply (conj P1 P2).
  Qed.

  Lemma and_el: P ∧ Q → P.
  Proof.
    intros [P1 _].
    apply P1.
  Qed.

  Lemma and_er: P ∧ Q → Q.
  Proof.
    intros [_ P1].
    apply P1.
  Qed.

  Lemma and_s: P ∧ Q → Q ∧ P.
  Proof.
    intros [P1 P2].
    apply (conj P2 P1).
  Qed.

  Lemma and_t: P ∧ Q → Q ∧ R → P ∧ R.
  Proof.
    intros [P1 _] [_ P2].
    apply (conj P1 P2).
  Qed.

  Lemma and_reorder: P ∧ Q → R ∧ S → P ∧ R.
  Proof.
    intros [P1 _] [P2 _].
    apply (conj P1 P2).
  Qed.

  Lemma or_il: P → P ∨ Q.
  Proof.
    intros P1.
    apply (inl _ P1).
  Qed.

  Lemma or_ir: Q → P ∨ Q.
  Proof.
    intros P1.
    apply (inr _ P1).
  Qed.

  Lemma or_s: P ∨ Q → Q ∨ P.
  Proof.
    intros [P1 | P1].
    + apply (inr _ P1).
    + apply (inl _ P1).
  Qed.

  Lemma imp_r: P → P.
  Proof.
    intros P1.
    apply P1.
  Qed.

  Lemma imp_t: (P → Q) → (Q → R) → P → R.
  Proof.
    intros P1 P2 P3.
    apply (P2 (P1 P3)).
  Qed.

  Lemma iff_r: P ↔ P.
  Proof.
    split.
    + apply imp_r.
    + apply imp_r.
  Qed.
  
  Lemma iff_s: (P ↔ Q) → (Q ↔ P).
  Proof.
    intros [P1 P2].
    apply (conj P2 P1).
  Qed.

  Lemma iff_t: (P ↔ Q) → (Q ↔ R) → (P ↔ R).
  Proof.
    intros [P1 P2] [P3 P4].
    split.
    + intros P5.
      apply (P3 (P1 P5)).
    + intros P5.
      apply (P2 (P4 P5)).
  Qed.
End Logic.
(*----------------------------------------------------------------------------*)

(* Set *)
Parameter J    : Prop.
Parameter J_in : J → J → Prop.

Notation "x ∈ y" := (J_in x y).
Notation "x ∉ y" := (~(x ∈ y)).

(* Equality *)
Inductive eq: J → J → Prop :=
  | refl: forall x: J, eq x x.

Notation "x = y" := (eq x y).
Notation "x ≠ y" := (~(x = y)).

(* Basic Properties of Equality *)
Section Equality.
  Variable A B C: J.
  
  Theorem eq_r : A = A.
  Proof.
    apply refl.
  Qed.
  
  Theorem eq_s : A = B → B = A.
  Proof.
    intros [x].
    apply refl.
  Qed.

  Theorem eq_t : A = B → B = C → A = C.
  Proof.
    intros [_] [x].
    apply refl.
  Qed.

  Theorem eq_c : forall P : J → Prop, A = B → P A → P B.
  Proof.
    intros P [x] H1.
    apply H1.
  Qed.

  Theorem eq_w : forall P : J → J, A = B → P A = P B.
  Proof.
    intros P [x].
    apply refl.
  Qed.

  Lemma neq_s: A ≠ B → B ≠ A.
  Proof.
    intros P1 P2.
    destruct P2.
    apply P1.
    apply refl.
  Qed.
End Equality.
(*----------------------------------------------------------------------------*)

(* Quantifier *)
Inductive ex (P: J → Prop): Prop :=
  | ex_i: forall x: J, P x → ex P.

(*Notation "'exists' x , p" := (ex (fun x => p)) (at level 200, right associativity).*)
Notation "∃  A , P" := (ex (fun A => P)).
Notation "∀  A , P" := (forall A: J, P).
Notation "∀ₚ A , P" := (forall A : (J → Prop), P).
Notation "'λ' x , P" := (fun x => P).

Section Exist.
  Variable (P : J → Prop).

  Definition ex_outl (x : ex P) : J :=
    match x with 
      | ex_i _ a _ => a
    end.

  Definition ex_outr (x : ex P) : P (ex_outl x) :=
    match x with
      | ex_i _ _ a => a
    end.
End Exist.
(*----------------------------------------------------------------------------*)

