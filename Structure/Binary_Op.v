Require Import Init.Init.
Require Import Relation.Relation.

Definition binop (A R: J) := R ∈ (A ⨉ A) ↦ A.
Notation   "x +[ R ] y"   := (R[⟨x, y⟩]).

Definition assoc (A R: J) := ∀ x, ∀ y, ∀ z, x ∈ A → y ∈ A → z ∈ A
  → x +[R] y +[R] z = x +[R] (y +[R] z).

Definition identr (A R e: J) := e ∈ A ∧ ∀ x, x ∈ A → x +[R] e = x.
Definition identl (A R e: J) := e ∈ A ∧ ∀ x, x ∈ A → e +[R] x = x.
Definition ident  (A R e: J) := e ∈ A ∧ ∀ x, x ∈ A → x +[R] e = x ∧ e +[R] x = x.

Definition inver (A R e: J) := ∀ x, ∃ y, x ∈ A
  → y ∈ A ∧ x +[R] y = e ∧ y +[R] x = e.

Definition commu (A R: J) := ∀ x, ∀ y, x ∈ A → y ∈ A → x +[R] y = y +[R] x.

Lemma ident_er: ∀ A, ∀ R, ∀ e, ident A R e → identr A R e.
Proof.
  intros A R e [P1 P2].
  split.
  + apply P1.
  + intros x P3.
    apply (P2 _ P3).
Qed.

Lemma ident_el: ∀ A, ∀ R, ∀ e, ident A R e → identl A R e.
Proof.
  intros A R e [P1 P2].
  split.
  + apply P1.
  + intros x P3.
    apply (P2 _ P3).
Qed.

Lemma binop_close: ∀ A, ∀ R, ∀ m, ∀ n, binop A R → m ∈ A → n ∈ A → m +[R] n ∈ A.
Proof.
  intros A R m n P1 P2 P3.
  apply (fval_codom _ _ _ _ P1).
  apply (cp_i _ _ _ _ P2 P3).
Qed.
