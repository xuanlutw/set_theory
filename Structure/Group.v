Require Import Init.Init.
Require Import Relation.Relation.
Require Import Structure.Binary_Op.

Definition cmonoid (A R e: J)
  := binop A R ∧ assoc A R ∧ commu A R ∧ ident A R e.

Section cmonoid.
  Variable A R e a b c d: J.
  Variable H0: cmonoid A R e.
  Variable H1: a ∈ A.
  Variable H2: b ∈ A.
  Variable H3: c ∈ A.
  Variable H4: d ∈ A.
  Notation "x + y" := (x +[R] y).

  Lemma cmonoid_assoc: assoc A R.
  Proof.
    apply H0.
  Qed.

  Lemma cmonoid_commu: commu A R.
  Proof.
    apply H0.
  Qed.

  Lemma cmonoid_ident: ident A R e.
  Proof.
    apply H0.
  Qed.

  Lemma cmonoid_identr: identr A R e.
  Proof.
    apply ident_er.
    apply cmonoid_ident.
  Qed.

  Lemma cmonoid_identl: identl A R e.
  Proof.
    apply ident_el.
    apply cmonoid_ident.
  Qed.

  Lemma cmonoid_op_eq: a = b → c = d → a + c = b + d.
  Proof.
    intros P1 P2.
    apply (eq_cl (λ x, _ = x + _) P1).
    apply (eq_cl (λ x, _ = _ + x) P2).
    apply eq_r.
  Qed.

  Lemma cmonoid_op_eq2: a = b → a + c = b + c.
  Proof.
    intros P1.
    apply (eq_cl (λ x, _ = x + _) P1).
    apply eq_r.
  Qed.

  Lemma cmonoid_132: a + b + c = a + c + b.
  Proof.
    apply (eq_cr (λ x, _ = x) (cmonoid_assoc _ _ _ H1 H3 H2)).
    apply (eq_cr (λ x, _ = _ + x) (cmonoid_commu _ _ H3 H2)).
    apply (eq_cl (λ x, _ = x) (cmonoid_assoc _ _ _ H1 H2 H3)).
    apply eq_r.
  Qed.

  Lemma cmonoid_213: a + b + c = b + a + c.
  Proof.
    apply (eq_cr (λ x, _ = x + _) (cmonoid_commu _ _ H2 H1)).
    apply eq_r.
  Qed.

  Lemma cmonoid_231: a + b + c = b + c + a.
  Proof.
    apply (eq_cr (λ x, _ = x) (cmonoid_assoc _ _ _ H2 H3 H1)).
    apply (eq_cr (λ x, _ = _ + x) (cmonoid_commu _ _ H3 H1)).
    apply (eq_cl (λ x, _ = x) (cmonoid_assoc _ _ _ H2 H1 H3)).
    apply cmonoid_213.
  Qed.

  Lemma cmonoid_312: a + b + c = c + a + b.
  Proof.
    apply (eq_cr (λ x, _ = x + _) (cmonoid_commu _ _ H3 H1)).
    apply cmonoid_132.
  Qed.

  Lemma cmonoid_321: a + b + c = c + b + a.
  Proof.
    apply (eq_cr (λ x, _ = x + _) (cmonoid_commu _ _ H3 H2)).
    apply cmonoid_231.
  Qed.
End cmonoid.

