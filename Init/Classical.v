Set Implicit Arguments.

Require Import Init.Logic.

Axiom LEM: forall A: Prop, A ∨ ~A.

(* Some Corollaries of LEM *)
Section LEM.
  Variable P Q R S: Prop.

  Lemma nn_i: P → ~~P.
  Proof.
    intros P1 P2.
    apply (P2 P1).
  Qed.

  Lemma nn_e: ~~P → P.
  Proof.
    intros P1.
    destruct (LEM P) as [P2 | P2].
    + apply P2.
    + apply (bot_e _ (P1 P2)).
  Qed.

  Lemma contraposition1: (P → Q) → (~Q → ~P).
  Proof.
    intros P1 P2 P3.
    apply (P2 (P1 P3)).
  Qed.

  Lemma contraposition2: (~P → Q) → (~Q → P).
  Proof.
    intros P1 P2.
    destruct (LEM P) as [P3 | P3].
    + apply P3.
    + apply (bot_e _ (P2 (P1 P3))).
  Qed.

  Lemma contraposition3: (P → ~Q) → (Q → ~P).
  Proof.
    intros P1 P2.
    destruct (LEM P) as [P3 | P3].
    + apply (bot_e _ (P1 P3 P2)).
    + apply P3.
  Qed.

  Lemma contraposition4: (~P → ~Q) → (Q → P).
  Proof.
    intros P1 P2.
    destruct (LEM P) as [P3 | P3].
    + apply P3.
    + apply (bot_e _ (P1 P3 P2)).
  Qed.

  Lemma not_and_or: ~(P ∧ Q) → (~P ∨ ~Q).
  Proof.
    intros P1.
    destruct (LEM P) as [P2 | P2].
    + destruct (LEM Q) as [P3 | P3].
      - apply (bot_e _ (P1 (and_i P2 P3))).
      - right.
        apply P3.
    + left.
      apply P2.
  Qed.

  Lemma not_or_and: ~(P ∨ Q) → ~P ∧ ~Q.
  Proof.
    intros P1.
    split.
    + destruct (LEM P) as [P2 | P2].
      - destruct (P1 (or_il _ P2)).
      - apply P2.
    + destruct (LEM Q) as [P2 | P2].
      - destruct (P1 (or_ir _ P2)).
      - apply P2.
  Qed.

  Lemma and_not_or: ~P ∧ ~Q → ~(P ∨ Q).
  Proof.
    intros [P1 P2] [P3 | P3].
    + apply (P1 P3).
    + apply (P2 P3).
  Qed.

  Lemma or_not_and: ~P ∨ ~Q → ~(P ∧ Q).
  Proof.
    intros [P1 | P1] [P2 P3].
    + apply (P1 P2).
    + apply (P1 P3).
  Qed.
End LEM.

Lemma not_ex_all_not: ∀ x, ∀ₚ P, ~(∃ x, P x) → (∀ x, ~(P x)).
Proof.
  intros x P P1 A P2.
  apply (P1 (ex_i P A P2)).
Qed.

Lemma not_all_ex_not: ∀ x, ∀ₚ P, ~(∀ x, P x) → (∃ x, ~(P x)).
Proof.
  intros x P.
  apply contraposition2.
  intros P1 A.
  apply nn_e.
  apply (not_ex_all_not x _ P1 A).
Qed.

