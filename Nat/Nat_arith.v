Require Import Init.Init.
Require Import Relation.Relation.
Require Import Structure.Structure.
Require Import Nat.Inductive.
Require Import Nat.Nature.
Require Import Nat.Recursion.

Require dpdgraph.dpdgraph.

(* Skip exp *)

Definition nat0 := (∅).
Definition nat1 := (S(nat0)).
Definition nat2 := (S(nat1)).
Notation "𝟢"    := (nat0).
Notation "𝟣"    := (nat1).
Notation "𝟤"    := (nat2).

Definition sigma := {x: ω ⨉ ω| ∃ y, x = ⟨y, S(y)⟩}.
Notation   "'σ'" := (sigma).

Definition nat_add_proto (m: J) := (ex_outl (recursion_thm ω m σ)).
Definition nat_mul_proto (m: J) := (ex_outl (recursion_thm ω 𝟢 (nat_add_proto m))).
(*Definition exp_proto (m: J) := (ex_outl (recursion_thm ω 𝟣 (nat_mul_proto m))).*)

Definition nat_add := {x: (ω ⨉ ω) ⨉ ω|
    ∃ a, ∃ b, ∃ c, x = ⟨⟨a, b⟩, c⟩ ∧ ⟨b, c⟩ ∈ (nat_add_proto a)}.
Definition nat_mul := {x: (ω ⨉ ω) ⨉ ω|
    ∃ a, ∃ b, ∃ c, x = ⟨⟨a, b⟩, c⟩ ∧ ⟨b, c⟩ ∈ (nat_mul_proto a)}.

Notation "m +ₙ n" := (nat_add[⟨m, n⟩]).
Notation "m ×ₙ n" := (nat_mul[⟨m, n⟩]).
(*Notation "m ^ₙ n" := ((exp_proto m)[n]).*)

(* Symbols *)
Lemma zero_is_nat: 𝟢 ∈ ω.
Proof.
  apply empty_is_nat.
Qed.

Lemma one_is_nat: 𝟣 ∈ ω.
Proof.
  apply (suc_is_nat _ zero_is_nat).
Qed.
(*----------------------------------------------------------------------------*)

(* Sigma *)
Lemma sigma_is_fn: fn σ.
Proof.
  split.
  + apply cp_sub_rel.
  + intros a b1 b2 P1 P2.
    destruct (sub_e _ _ _ P1) as [_ [y1 P3]].
    destruct (opair_eq_e _ _ _ _ P3) as [P4 P5].
    apply (eq_t P5).
    apply (eq_cl (λ x, S(x) = b2) P4).
    destruct (sub_e _ _ _ P2) as [_ [y2 P6]].
    destruct (opair_eq_e _ _ _ _ P6) as [P7 P8].
    apply (eq_cr (λ x, S(a) = x) P8).
    apply (eq_cr (λ x, S(x) = S(y2)) P7).
    apply eq_r.
Qed.

Lemma sigma_dom: dom(σ) = ω.
Proof.
  apply sub_a.
  split.
  * intros x P1.
    destruct (dom_e _ _ P1) as [y P2].
    destruct (sub_e _ _ _ P2) as [P3 _].
    destruct (cp_e2 _ _ _ _ P3) as [P4 _].
    apply P4.
  * intros x P2.
    apply (dom_i _ _ (S(x))).
    apply sub_i.
    + apply cp_i.
      - apply P2.
      - apply (suc_is_nat _ P2).
    + exists x.
      apply eq_r.
Qed.

Lemma sigma_ran: ran(σ) ⊆ ω.
Proof.
  intros y P1.
  destruct (ran_e _ _ P1) as [x P2].
  destruct (sub_e _ _ _ P2) as [P3 _].
  destruct (cp_e2 _ _ _ _ P3) as [_ P4]. 
  apply P4.
Qed.

Lemma sigma_fmap: σ ∈ ω ↦ ω.
Proof.
  apply fmap_i.
  + apply sigma_is_fn.
  + apply sigma_dom.
  + apply sigma_ran.
Qed.

Lemma sigma_i: ∀ k, k ∈ ω → S(k) = σ[k].
Proof.
  intros k P1.
  apply eq_s.
  apply fval_i.
  + apply sigma_is_fn.
  + apply sub_i.
    - apply cp_i.
      * apply P1.
      * apply (suc_is_nat _ P1).
    - exists k.
      apply eq_r.
Qed.
(*----------------------------------------------------------------------------*)

(* Addition *)
Lemma nat_add_proto_fmap: ∀ m, m ∈ ω → (nat_add_proto m) ∈ ω ↦ ω.
Proof.
  intros m P1.
  destruct (ex_outr (recursion_thm ω m σ) P1 sigma_fmap) as [P2 _].
  apply P2.
Qed.

Lemma nat_add_proto_fn: ∀ m, m ∈ ω → fn (nat_add_proto m).
Proof.
  intros m P1.
  apply (fmap_fn _ _ _ (nat_add_proto_fmap _ P1)).
Qed.

Lemma nat_add_proto_e1: ∀ m, m ∈ ω → (nat_add_proto m)[𝟢] = m.
Proof.
  intros m P1.
  destruct (ex_outr (recursion_thm ω m σ) P1 sigma_fmap) as [_ [P2 _]].
  apply P2.
Qed.

Lemma nat_add_proto_e2: ∀ m, ∀ n, m ∈ ω → n ∈ ω
  → (nat_add_proto m)[S(n)] = S((nat_add_proto m)[n]).
Proof.
  intros m n P1 P2.
  destruct (ex_outr (recursion_thm ω m σ) P1 sigma_fmap) as [P3 [_ P4]].
  apply (eq_cr (λ x, x = _) (P4 _ P2)).
  apply eq_s.
  apply sigma_i.
  apply (fmap_ran _ _ _ P3).
  apply (fval_ran _ _ (fmap_fn _ _ _ P3)).
  apply (eq_cr (λ x, n ∈ x) (fmap_dom _ _ _ P3)).
  apply P2.
Qed.

Lemma nat_add_fn: fn nat_add.
Proof.
  split.
  + apply cp_sub_rel.
  + intros x y1 y2 P1 P2.
    destruct (sub_e _ _ _ P1) as [Q1 [a1 [b1 [c1 [P3 P4]]]]].
    destruct (sub_e _ _ _ P2) as [_  [a2 [b2 [c2 [P5 P6]]]]].
    destruct (cp_e2 _ _ _ _ Q1) as [Q2 _].
    destruct (cp_e2 _ _ _ _ (eq_cl (λ x, x ∈ _) (opair_eq_el _ _ _ _ P3) Q2))
      as [Q3 _].
    apply (eq_cr (λ x, x = _) (opair_eq_er _ _ _ _ P3)).
    apply (eq_cr (λ x, _ = x) (opair_eq_er _ _ _ _ P5)).
    destruct (nat_add_proto_fn _ Q3) as [_ P7].
    apply (P7 b1).
    - apply P4.
    - pose (eq_t (eq_s (opair_eq_el _ _ _ _ P3)) (opair_eq_el _ _ _ _ P5)) as P8.
      apply (eq_cr (λ x, ⟨x, _⟩ ∈ _) (opair_eq_er _ _ _ _ P8)).
      apply (eq_cr (λ x, ⟨_, _⟩ ∈ nat_add_proto x) (opair_eq_el _ _ _ _ P8)).
      apply P6.
Qed.

Lemma nat_add_binop: binop ω nat_add.
Proof.
  apply fmap_i.
  + apply nat_add_fn.
  + apply sub_a.
    split.
    - apply (cp_sub_dom _ _ ω).
      apply sub_e1.
    - intros x P1.
      destruct (cp_e _ _ _ P1) as [a [b [P2 [P3 P4]]]].
      apply (dom_i _ _ ((nat_add_proto a)[b])).
      apply sub_i.
      * apply cp_i.
        ++apply (eq_cr (λ x, x ∈ _) P4).
          apply (cp_i _ _ _ _ P2 P3).
        ++apply (fval_codom _ _ _ _ (nat_add_proto_fmap _ P2) P3).
      * exists a. exists b. exists ((nat_add_proto a)[b]).
        split.
        ++apply (eq_cr (λ x, ⟨x, _⟩ = _) P4 (eq_r _)).
        ++apply (fval_i2 _ _ (nat_add_proto_fn _ P2)).
          apply (eq_cr (λ x, _ ∈ x) (fmap_dom _ _ _ (nat_add_proto_fmap _ P2))).
          apply P3.
  + apply (cp_sub_ran _ (ω ⨉ ω)).
    apply sub_e1.
Qed.

Lemma nat_add_close: ∀ m, ∀ n, m ∈ ω → n ∈ ω → m +ₙ n ∈ ω.
Proof.
  intros m n P1 P2.
  apply (binop_close _ _ _ _ (nat_add_binop) P1 P2).
Qed.

Lemma nat_add_proto_trans: ∀ m, ∀ n, m ∈ ω → n ∈ ω
  → (nat_add_proto m)[n] = m +ₙ n.
Proof.
  intros m n P1 P2.
  apply eq_s.
  apply (fval_i _ _ _ nat_add_fn).
  apply sub_i.
  +apply cp_i.
    -apply (cp_i _ _ _ _ P1 P2).
    -apply (fval_codom _ _ _ _ (nat_add_proto_fmap _ P1) P2).
  +exists m. exists n. exists ((nat_add_proto m)[n]).
    split.
    -apply eq_r.
    -apply (fval_i2 _ _ (nat_add_proto_fn _ P1)).
      apply (eq_cr (λ x, n ∈ x)
        (fmap_dom _ _ _ (nat_add_proto_fmap _ P1)) P2).
Qed.

Lemma nat_add_redr: ∀ m, ∀ n, m ∈ ω → n ∈ ω → m +ₙ S(n) = S(m +ₙ n).
Proof.
  intros m n P1 P2.
  apply (eq_cl (λ x, x = _)    (nat_add_proto_trans _ _ P1 (suc_is_nat _ P2))).
  apply (eq_cl (λ x, _ = S(x)) (nat_add_proto_trans _ _ P1 P2)).
  apply (nat_add_proto_e2 _ _ P1 P2).
Qed.

Lemma nat_add_zeror: ∀ m, m ∈ ω → m +ₙ 𝟢 = m.
Proof.
  intros m P1.
  apply (eq_cl (λ x, x = _)    (nat_add_proto_trans _ _ P1 zero_is_nat)).
  apply (nat_add_proto_e1 _ P1).
Qed.

Lemma nat_add_zerol: ∀ m, m ∈ ω → 𝟢 +ₙ m = m.
Proof.
  intros m P1.
  pose (λ k, 𝟢 +ₙ k = k) as P.
  assert (P 𝟢) as I1.
  { apply (nat_add_zeror _ empty_is_nat). }
  assert (induction_step P) as I2.
  { intros k Q1 Q2.
    apply (eq_cr (λ x, x = _) (nat_add_redr _ _ zero_is_nat Q1)).
    apply (eq_cr (λ x, S(x) = _) Q2).
    apply eq_r. }
  apply (induction_principle _ I1 I2 _ P1).
Qed.

Lemma nat_add_redl: ∀ m, ∀ n, m ∈ ω → n ∈ ω → S(m) +ₙ n = S(m +ₙ n).
Proof.
  intros m n P1 P2.
  pose (λ k, S(m) +ₙ k = S(m +ₙ k)) as P.
  assert (P 𝟢) as I1.
  { apply (eq_cr (λ x, x = _) (nat_add_zeror _ (suc_is_nat _ P1))).
    apply (eq_cr (λ x, _ = S(x)) (nat_add_zeror _ P1)).
    apply eq_r. }
  assert (induction_step P) as I2.
  { intros k Q1 Q2.
    apply (eq_cr (λ x, x = _) (nat_add_redr _ _ (suc_is_nat _ P1) Q1)).
    apply (eq_cr (λ x, S(x) = _) Q2).
    apply (eq_cr (λ x, _ = S(x)) (nat_add_redr _ _ P1 Q1)).
    apply eq_r. }
  apply (induction_principle _ I1 I2 _ P2).
Qed.

Lemma nat_add_commu: commu ω nat_add.
Proof.
  intros m n P1 P2.
  pose (λ k, m +ₙ k = k +ₙ m) as P.
  assert (P 𝟢) as I1.
  { apply (eq_cr (λ x, x = _) (nat_add_zeror _ P1)).
    apply (eq_cr (λ x, _ = x) (nat_add_zerol _ P1)).
    apply eq_r. }
  assert (induction_step P) as I2.
  { intros k P4 P5.
    apply (eq_cr (λ x, x = _) (nat_add_redr _ _ P1 P4)).
    apply (eq_cr (λ x, _ = x) (nat_add_redl _ _ P4 P1)).
    apply (eq_cl (λ x, _ = S(x)) P5).
    apply eq_r. }
  apply (induction_principle _ I1 I2 _ P2).
Qed.

Lemma nat_add_assoc: assoc ω nat_add.
Proof.
  intros m n p P1 P2 P3.
  pose (λ k, m +ₙ n +ₙ k = m +ₙ (n +ₙ k)) as P.
  assert (P 𝟢) as I1.
  { apply (eq_cr (λ x, _ = _ +ₙ x) (nat_add_zeror _ P2)).
    apply (nat_add_zeror _ (nat_add_close _ _ P1 P2)). }
  assert (induction_step P) as I2.
  { intros k P5 P6.
    red.
    apply (eq_cr (λ x, x = _) 
      (nat_add_redr (m +ₙ n) k (nat_add_close _ _ P1 P2) P5)).
    apply (eq_cr (λ x, S(x) = _) P6).
    apply (eq_cr (λ x, _ = _ +ₙ x) (nat_add_redr _ _ P2 P5)).
    apply (eq_cl (λ x, x = _) (nat_add_redr _ _ P1 (nat_add_close _ _ P2 P5))).
    apply eq_r. }
  apply (induction_principle _ I1 I2 _ P3).
Qed.

Lemma nat_add_ident: ident ω nat_add 𝟢.
Proof.
  split.
  + apply zero_is_nat.
  + intros x P1.
    split.
    - apply (nat_add_zeror _ P1).
    - apply (nat_add_zerol _ P1).
Qed.

Lemma nat_add_cmonoid: cmonoid ω nat_add 𝟢.
Proof.
  split. apply nat_add_binop.
  split. apply nat_add_assoc.
  split. apply nat_add_commu.
         apply nat_add_ident.
Qed.

Lemma nat_add_eq: ∀ a, ∀ b, ∀ c, ∀ d, a = b → c = d → a +ₙ c = b +ₙ d.
Proof.
  apply cmonoid_op_eq.
Qed.

Lemma nat_add_eq_2: ∀ m, ∀ n, ∀ l, m = n → m +ₙ l = n +ₙ l.
Proof.
  apply cmonoid_op_eq2.
Qed.

Lemma nat_add_132: ∀ m, ∀ n, ∀ l, m ∈ ω → n ∈ ω → l ∈ ω
  → m +ₙ n +ₙ l = m +ₙ l +ₙ n.
Proof.
  intros m n l.
  apply (cmonoid_132 _ _ _ _ _ _ nat_add_cmonoid).
Qed.

Lemma nat_add_213: ∀ m, ∀ n, ∀ l, m ∈ ω → n ∈ ω → l ∈ ω
  → m +ₙ n +ₙ l = n +ₙ m +ₙ l.
Proof.
  intros m n l P1 P2 P3.
  apply (cmonoid_213 _ _ _ _ _ _ nat_add_cmonoid P1 P2).
Qed.

Lemma nat_add_231: ∀ m, ∀ n, ∀ l, m ∈ ω → n ∈ ω → l ∈ ω
  → m +ₙ n +ₙ l = n +ₙ l +ₙ m.
Proof.
  intros m n l.
  apply (cmonoid_231 _ _ _ _ _ _ nat_add_cmonoid).
Qed.

Lemma nat_add_312: ∀ m, ∀ n, ∀ l, m ∈ ω → n ∈ ω → l ∈ ω
  → m +ₙ n +ₙ l = l +ₙ m +ₙ n.
Proof.
  intros m n l.
  apply (cmonoid_312 _ _ _ _ _ _ nat_add_cmonoid).
Qed.

Lemma nat_add_321: ∀ m, ∀ n, ∀ l, m ∈ ω → n ∈ ω → l ∈ ω
  → m +ₙ n +ₙ l = l +ₙ n +ₙ m.
Proof.
  intros m n l.
  apply (cmonoid_321 _ _ _ _ _ _ nat_add_cmonoid).
Qed.

Lemma nat_add_cancel: ∀ m, ∀ n, ∀ l, m ∈ ω → n ∈ ω → l ∈ ω
  → m +ₙ l = n +ₙ l → m = n.
Proof.
  intros m n l P1 P2 P3 P4.
  pose (λ k, m +ₙ k = n +ₙ k → m = n) as P.
  assert (P 𝟢) as I1.
  { intros Q1.
    apply (eq_t (eq_s (nat_add_zeror _ P1)) (eq_t Q1 (nat_add_zeror _ P2))). }
  assert (induction_step P) as I2.
  { intros k Q1 Q2 Q3.
    pose (nat_add_redr _ _ P1 Q1) as Q4.
    pose (nat_add_redr _ _ P2 Q1) as Q5.
    pose (eq_t (eq_s Q4) (eq_t Q3 Q5)) as Q6.
    apply Q2.
    apply (suc_unique _ _
      (nat_add_close _ _ P1 Q1)
      (nat_add_close _ _ P2 Q1) Q6). }
  apply (induction_principle _ I1 I2 _ P3 P4).
Qed.

Lemma nat_add_cancel2: ∀ m, ∀ n, ∀ p, ∀ q, p = q → m +ₙ p = n +ₙ q
  → m ∈ ω → n ∈ ω → p ∈ ω → q ∈ ω → m = n.
Proof.
  intros m n p q P1 P2 P3 P4 P5 P6.
  pose (eq_cl (λ x, _ +ₙ x = _) P1 P2) as P7.
  apply (nat_add_cancel _ _ _ P3 P4 P6 P7).
Qed.

Theorem one_one_two: 𝟣 +ₙ 𝟣 = 𝟤.
Proof.
  apply (eq_cr (λ x, x    = _) (nat_add_redr 𝟣 𝟢 one_is_nat zero_is_nat)).
  apply (eq_cr (λ x, S(x) = _) (nat_add_zeror 𝟣 one_is_nat) (eq_r _)).
Qed.
(*----------------------------------------------------------------------------*)

(* Multiplication *)
Lemma nat_mul_proto_fmap: ∀ m, m ∈ ω → (nat_mul_proto m) ∈ ω ↦ ω.
Proof.
  intros m P1.
  destruct (ex_outr (recursion_thm ω 𝟢 (nat_add_proto m)) 
    (zero_is_nat) (nat_add_proto_fmap _ P1)) as [P2 _].
  apply P2.
Qed.

Lemma nat_mul_proto_fn: ∀ m, m ∈ ω → fn (nat_mul_proto m).
Proof.
  intros m P1.
  apply (fmap_fn _ _ _ (nat_mul_proto_fmap _ P1)).
Qed.

Lemma nat_mul_proto_e1: ∀ m, m ∈ ω → (nat_mul_proto m)[𝟢] = 𝟢.
Proof.
  intros m P1.
  destruct (ex_outr (recursion_thm ω 𝟢 (nat_add_proto m)) 
    (zero_is_nat) (nat_add_proto_fmap _ P1)) as [_ [P2 _]].
  apply P2.
Qed.

Lemma nat_mul_proto_e2: ∀ m, ∀ n, m ∈ ω → n ∈ ω → 
    (nat_mul_proto m)[S(n)] = (nat_add_proto m)[(nat_mul_proto m)[n]].
Proof.
  intros m n P1 P2.
  destruct (ex_outr (recursion_thm ω 𝟢 (nat_add_proto m)) 
    (zero_is_nat) (nat_add_proto_fmap _ P1)) as [_ [_ P3]].
  apply (P3 _ P2).
Qed. 

Lemma nat_mul_fn: fn nat_mul.
Proof.
  split.
  + apply cp_sub_rel.
  + intros x y1 y2 P1 P2.
    destruct (sub_e _ _ _ P1) as [Q1 [a1 [b1 [c1 [P3 P4]]]]].
    destruct (sub_e _ _ _ P2) as [_  [a2 [b2 [c2 [P5 P6]]]]].
    destruct (cp_e2 _ _ _ _ Q1) as [Q2 _].
    destruct (cp_e2 _ _ _ _ (eq_cl (λ x, x ∈ _) (opair_eq_el _ _ _ _ P3) Q2))
      as [Q3 _].
    apply (eq_cr (λ x, x = _) (opair_eq_er _ _ _ _ P3)).
    apply (eq_cr (λ x, _ = x) (opair_eq_er _ _ _ _ P5)).
    destruct (nat_mul_proto_fn _ Q3) as [_ P7].
    apply (P7 b1).
    - apply P4.
    - pose (eq_t (eq_s (opair_eq_el _ _ _ _ P3)) (opair_eq_el _ _ _ _ P5)) as P8.
      apply (eq_cr (λ x, ⟨x, _⟩ ∈ _) (opair_eq_er _ _ _ _ P8)).
      apply (eq_cr (λ x, ⟨_, _⟩ ∈ nat_mul_proto x) (opair_eq_el _ _ _ _ P8)).
      apply P6.
Qed.

Lemma nat_mul_binop: binop ω nat_mul.
Proof.
  apply fmap_i.
  + apply nat_mul_fn.
  + apply sub_a.
    split.
    - apply (cp_sub_dom _ _ ω).
      apply sub_e1.
    - intros x P1.
      destruct (cp_e _ _ _ P1) as [a [b [P2 [P3 P4]]]].
      apply (dom_i _ _ ((nat_mul_proto a)[b])).
      apply sub_i.
      * apply cp_i.
        ++apply (eq_cr (λ x, x ∈ _) P4).
          apply (cp_i _ _ _ _ P2 P3).
        ++apply (fval_codom _ _ _ _ (nat_mul_proto_fmap _ P2) P3).
      * exists a. exists b. exists ((nat_mul_proto a)[b]).
        split.
        ++apply (eq_cr (λ x, ⟨x, _⟩ = _) P4 (eq_r _)).
        ++apply (fval_i2 _ _ (nat_mul_proto_fn _ P2)).
          apply (eq_cr (λ x, _ ∈ x) (fmap_dom _ _ _ (nat_mul_proto_fmap _ P2))).
          apply P3.
  + apply (cp_sub_ran _ (ω ⨉ ω)).
    apply sub_e1.
Qed.

Lemma nat_mul_close: ∀ m, ∀ n, m ∈ ω → n ∈ ω → m ×ₙ n ∈ ω.
Proof.
  intros m n P1 P2.
  apply (binop_close _ _ _ _ nat_mul_binop P1 P2).
Qed.

Lemma nat_mul_proto_trans: ∀ m, ∀ n, m ∈ ω → n ∈ ω
  → (nat_mul_proto m)[n] = m ×ₙ n.
Proof.
  intros m n P1 P2.
  apply eq_s.
  apply (fval_i _ _ _ nat_mul_fn).
  apply sub_i.
  +apply cp_i.
    -apply (cp_i _ _ _ _ P1 P2).
    -apply (fval_codom _ _ _ _ (nat_mul_proto_fmap _ P1) P2).
  +exists m. exists n. exists ((nat_mul_proto m)[n]).
    split.
    -apply eq_r.
    -apply (fval_i2 _ _ (nat_mul_proto_fn _ P1)).
      apply (eq_cr (λ x, n ∈ x)
        (fmap_dom _ _ _ (nat_mul_proto_fmap _ P1)) P2).
Qed.

Lemma nat_mul_redr: ∀ m, ∀ n, m ∈ ω → n ∈ ω → m ×ₙ S(n) = m +ₙ (m ×ₙ n).
Proof.
  intros m n P1 P2.
  apply (eq_cl (λ x, x = _) (nat_mul_proto_trans _ _ P1 (suc_is_nat _ P2))).
  apply (eq_cl (λ x, _ = x) 
    (nat_add_proto_trans _ _ P1 (nat_mul_close _ _ P1 P2))).
  apply (eq_cl (λ x, _ = nat_add_proto m [x]) (nat_mul_proto_trans _ _ P1 P2)).
  apply (nat_mul_proto_e2 _ _ P1 P2).
Qed.

Lemma nat_mul_zeror: ∀ m, m ∈ ω → m ×ₙ 𝟢 = 𝟢.
Proof.
  intros m P1.
  apply (eq_cl (λ x, x = _) (nat_mul_proto_trans _ _ P1 zero_is_nat)).
  apply (nat_mul_proto_e1 _ P1).
Qed.

Lemma nat_mul_zerol: ∀ m, m ∈ ω → 𝟢 ×ₙ m = 𝟢.
Proof.
  intros m P1.
  pose (λ k, 𝟢 ×ₙ k = 𝟢) as P.
  assert (P 𝟢) as I1.
  { apply (nat_mul_zeror _ zero_is_nat). }
  assert (induction_step P) as I2.
  { intros k Q1 Q2.
    apply (eq_cr (λ x, x = _) (nat_mul_redr _ _ zero_is_nat Q1)).
    apply (eq_cr (λ x, _ +ₙ x = _) Q2).
    apply (nat_add_zeror _ empty_is_nat). }
  apply (induction_principle _ I1 I2 _ P1).
Qed.

Lemma nat_mul_redl: ∀ m, ∀ n, m ∈ ω → n ∈ ω → S(m) ×ₙ n = n +ₙ (m ×ₙ n).
Proof.
  intros m n P1 P2.
  pose (λ k, S(m) ×ₙ k = k +ₙ (m ×ₙ k)) as P.
  assert (P 𝟢) as I1.
  { apply (eq_cr (λ x, x = _)      (nat_mul_zeror _ (suc_is_nat _ P1))).
    apply (eq_cr (λ x, _ = _ +ₙ x) (nat_mul_zeror _ P1)).
    apply (eq_cr (λ x, _ = x)      (nat_add_zeror _ empty_is_nat)).
    apply eq_r. }
  assert (induction_step P) as I2.
  { intros k P4 P5.
    apply (eq_cr (λ x, x = _)      (nat_mul_redr _ _ (suc_is_nat _ P1) P4)).
    apply (eq_cr (λ x, _ = _ +ₙ x) (nat_mul_redr _ _ P1 P4)).
    apply (eq_cr (λ x, _ +ₙ x = _) P5).
    apply (eq_cl (λ x, x = _)
      (nat_add_assoc _ _ _ (suc_is_nat _ P1) P4 (nat_mul_close _ _ P1 P4))).
    apply (eq_cl (λ x, _ = x)
      (nat_add_assoc _ _ _ (suc_is_nat _ P4) P1 (nat_mul_close _ _ P1 P4))).
    apply (eq_cr (λ x, _ = x +ₙ _) (nat_add_commu _ _ (suc_is_nat _ P4) P1)).
    apply (eq_cr (λ x, _ = x +ₙ _) (nat_add_redr _ _ P1 P4)).
    apply (eq_cr (λ x, x +ₙ _ = _) (nat_add_redl _ _ P1 P4)).
    apply eq_r. }
  apply (induction_principle _ I1 I2 _ P2).
Qed.

Lemma nat_mul_commu: commu ω nat_mul.
Proof.
  intros m n P1 P2.
  pose (λ k, m ×ₙ k = k ×ₙ m) as P.
  assert (P 𝟢) as I1.
  { apply (eq_cr (λ x, x = _) (nat_mul_zeror _ P1)).
    apply (eq_cr (λ x, _ = x) (nat_mul_zerol _ P1)).
    apply eq_r. }
  assert (induction_step P) as I2.
  { intros k P4 P5.
    apply (eq_cr (λ x, x = _) (nat_mul_redr _ _ P1 P4)).
    apply (eq_cr (λ x, _ = x) (nat_mul_redl _ _ P4 P1)).
    apply (eq_cr (λ x, _ +ₙ x = _) P5).
    apply eq_r. }
  apply (induction_principle _ I1 I2 _ P2).
Qed.

(* Will... weird order *)

Lemma nat_distrl: ∀ m, ∀ n, ∀ p, m ∈ ω → n ∈ ω → p ∈ ω
  → m ×ₙ (n +ₙ p) = m ×ₙ n +ₙ m ×ₙ p.
Proof.
  intros m n p P1 P2 P3.
  pose (λ k, m ×ₙ (n +ₙ k) = m ×ₙ n +ₙ m ×ₙ k) as P.
  assert (P 𝟢) as I1.
  { apply (eq_cr (λ x, _ ×ₙ x = _) (nat_add_zeror _ P2)).
    apply (eq_cr (λ x, _ = _ +ₙ x) (nat_mul_zeror _ P1)).
    apply (eq_cr (λ x, _ = x) (nat_add_zeror _ (nat_mul_close _ _ P1 P2))).
    apply eq_r. }
  assert (induction_step P) as I2.
  { intros k P5 P6.
    apply (eq_cr (λ x, _ ×ₙ x = _) (nat_add_redr _ _ P2 P5)).
    apply (eq_cr (λ x, x = _) (nat_mul_redr _ _ P1 (nat_add_close _ _ P2 P5))).
    apply (eq_cr (λ x, _ +ₙ x = _) P6).
    apply (eq_cr (λ x, _ = _ +ₙ x) (nat_mul_redr _ _ P1 P5)).
    apply (eq_cl (λ x, _ = x) (nat_add_assoc _ _ _ 
      (nat_mul_close _ _ P1 P2) P1 (nat_mul_close _ _ P1 P5))).
    apply (eq_cr (λ x, _ = x +ₙ _) (nat_add_commu _ _ 
      (nat_mul_close _ _ P1 P2) P1)).
    apply (eq_cl (λ x, x = _) (nat_add_assoc _ _ _ 
      P1 (nat_mul_close _ _ P1 P2) (nat_mul_close _ _ P1 P5))).
    apply eq_r. }
  apply (induction_principle _ I1 I2 _ P3).
Qed.

Lemma nat_distrr: ∀ m, ∀ n, ∀ p, m ∈ ω → n ∈ ω → p ∈ ω
  → (m +ₙ n) ×ₙ p = m ×ₙ p +ₙ n ×ₙ p.
Proof.
  intros m n p P1 P2 P3.
  apply (eq_cr (λ x, x = _) (nat_mul_commu _ _ (nat_add_close _ _ P1 P2) P3)).
  apply (eq_cr (λ x, _ = x +ₙ _) (nat_mul_commu _ _ P1 P3)).
  apply (eq_cr (λ x, _ = _ +ₙ x) (nat_mul_commu _ _ P2 P3)).
  apply (nat_distrl _ _ _ P3 P1 P2).
Qed.

Lemma nat_mul_assoc: assoc ω nat_mul.
Proof.
  intros m n p P1 P2 P3.
  pose (λ k, m ×ₙ n ×ₙ k = m ×ₙ (n ×ₙ k)) as P.
  assert (P 𝟢) as I1.
  { apply (eq_cr (λ x, _ = _ ×ₙ x) (nat_mul_zeror _ P2)).
    apply (eq_cr (λ x, _ = x)      (nat_mul_zeror _ P1)).
    apply (nat_mul_zeror _ (nat_mul_close _ _ P1 P2)). }
  assert (induction_step P) as I2.
  { intros k P5 P6.
    apply eq_s.
    apply (eq_cr (λ x, _ = x) (nat_mul_redr _ _ (nat_mul_close _ _ P1 P2) P5)).
    apply (eq_cr (λ x, _ = _ +ₙ x) P6).
    apply (eq_cr (λ x, _ ×ₙ x = _) (nat_mul_redr _ _ P2 P5)).
    apply (nat_distrl _ _ _ P1 P2 (nat_mul_close _ _ P2 P5)). }
  apply (induction_principle _ I1 I2 _ P3).
Qed.

Lemma nat_mul_oner: ∀ m, m ∈ ω → m ×ₙ 𝟣 = m.
Proof.
  intros m P1.
  apply (eq_cr (λ x, x = m)      (nat_mul_redr _ _ P1 zero_is_nat)).
  apply (eq_cr (λ x, m +ₙ x = m) (nat_mul_zeror _ P1)).
  apply (nat_add_zeror _ P1).
Qed.

Lemma nat_mul_onel: ∀ m, m ∈ ω → 𝟣 ×ₙ m = m.
Proof.
  intros m P1.
  apply (eq_cr (λ x, x = _) (nat_mul_commu _ _ one_is_nat P1)).
  apply (nat_mul_oner _ P1).
Qed.

Lemma nat_mul_ident: ident ω nat_mul 𝟣.
Proof.
  split.
  + apply one_is_nat.
  + intros m P1.
    split.
    - apply (nat_mul_oner _ P1).
    - apply (nat_mul_onel _ P1).
Qed.

Lemma nat_mul_cmonoid: cmonoid ω nat_mul 𝟣.
Proof.
  split. apply nat_mul_binop.
  split. apply nat_mul_assoc.
  split. apply nat_mul_commu.
         apply nat_mul_ident.
Qed.

Lemma nat_mul_eq: ∀ a, ∀ b, ∀ c, ∀ d, a = b → c = d → a ×ₙ c = b ×ₙ d.
Proof.
  apply cmonoid_op_eq.
Qed.

Lemma nat_mul_eq_2: ∀ m, ∀ n, ∀ l, m = n → m ×ₙ l = n ×ₙ l.
Proof.
  apply cmonoid_op_eq2.
Qed.

Lemma nat_mul_132: ∀ m, ∀ n, ∀ l, m ∈ ω → n ∈ ω → l ∈ ω
  → m ×ₙ n ×ₙ l = m ×ₙ l ×ₙ n.
Proof.
  intros m n l.
  apply (cmonoid_132 _ _ _ _ _ _ nat_mul_cmonoid).
Qed.

Lemma nat_mul_213: ∀ m, ∀ n, ∀ l, m ∈ ω → n ∈ ω → l ∈ ω
  → m ×ₙ n ×ₙ l = n ×ₙ m ×ₙ l.
Proof.
  intros m n l P1 P2 P3.
  apply (cmonoid_213 _ _ _ _ _ _ nat_mul_cmonoid P1 P2).
Qed.

Lemma nat_mul_231: ∀ m, ∀ n, ∀ l, m ∈ ω → n ∈ ω → l ∈ ω
  → m ×ₙ n ×ₙ l = n ×ₙ l ×ₙ m.
Proof.
  intros m n l.
  apply (cmonoid_231 _ _ _ _ _ _ nat_mul_cmonoid).
Qed.

Lemma nat_mul_312: ∀ m, ∀ n, ∀ l, m ∈ ω → n ∈ ω → l ∈ ω
  → m ×ₙ n ×ₙ l = l ×ₙ m ×ₙ n.
Proof.
  intros m n l.
  apply (cmonoid_312 _ _ _ _ _ _ nat_mul_cmonoid).
Qed.

Lemma nat_mul_321: ∀ m, ∀ n, ∀ l, m ∈ ω → n ∈ ω → l ∈ ω
  → m ×ₙ n ×ₙ l = l ×ₙ n ×ₙ m.
Proof.
  intros m n l.
  apply (cmonoid_321 _ _ _ _ _ _ nat_mul_cmonoid).
Qed.

Lemma nat_mul_eq_zero: ∀ m, ∀ n, m ∈ ω → n ∈ ω → m ×ₙ n = 𝟢 → m = 𝟢 ∨ n = 𝟢.
Proof.
  intros m n P1 P2.
  apply contraposition4.
  intros P3 P4.
  destruct (not_or_and P3) as [P5 P6].
  destruct (nat_is_suc _ P1 P5) as [mm [P7 P8]].
  destruct (nat_is_suc _ P2 P6) as [nn [P9 P10]].
  apply (empty_not_suc (nn +ₙ mm ×ₙ S( nn))).
  apply (eq_cl (λ x, _ = x)
    (nat_add_redl _ _ P9 (nat_mul_close _ _ P7 (suc_is_nat _ P9)))).
  apply (eq_cl (λ x, _ = x +ₙ _ ×ₙ x) P10).
  apply (eq_cl (λ x, _ = x) (nat_mul_redl _ _ P7 P2)).
  apply (eq_cl (λ x, _ = x ×ₙ _) P8).
  apply (eq_s P4).
Qed.

Theorem one_two_two: 𝟣 ×ₙ 𝟤 = 𝟤.
Proof.
  apply (eq_cr (λ x, x      = _) (nat_mul_redr 𝟣 𝟣 one_is_nat one_is_nat)).
  apply (eq_cr (λ x, _ +ₙ x = _) (nat_mul_oner _ one_is_nat)).
  apply one_one_two.
Qed.
(*----------------------------------------------------------------------------*)

(* Exponential *)
(*Lemma exp_proto_is_fn: ∀ m, m ∈ ω → fnm (exp_proto m) ω ω.*)
(*Proof.*)
  (*intros m P1.*)
  (*destruct (ex_outr (recursion_thm ω (𝟣) (nat_mul_proto m)) *)
    (*one_is_nat (nat_mul_proto_is_fn _ P1)) as [P2 _].*)
  (*apply P2.*)
(*Qed.*)

(*Lemma exp_proto_e1: ∀ m, m ∈ ω → (exp_proto m)[𝟢] = 𝟣.*)
(*Proof.*)
  (*intros m P1.*)
  (*destruct (ex_outr (recursion_thm ω (𝟣) (nat_mul_proto m)) *)
    (*one_is_nat (nat_mul_proto_is_fn _ P1)) as [_ [P2 _]].*)
  (*apply P2.*)
(*Qed.*)

(*Lemma exp_proto_e2: ∀ m, ∀ n, m ∈ ω → n ∈ ω → *)
    (*(exp_proto m)[S(n)] = (nat_mul_proto m)[(exp_proto m)[n]].*)
(*Proof.*)
  (*intros m n P1 P2.*)
  (*destruct (ex_outr (recursion_thm ω (𝟣) (nat_mul_proto m)) *)
    (*one_is_nat (nat_mul_proto_is_fn _ P1)) as [_ [_ P3]].*)
  (*apply (P3 _ P2).*)
(*Qed.*)

(*Lemma exp_zero: ∀ m, m ∈ ω → m ^ₙ 𝟢 = 𝟣.*)
(*Proof.*)
  (*intros m P1.*)
  (*apply (exp_proto_e1 _ P1).*)
(*Qed.*)

(*Lemma exp_red: ∀ m, ∀ n, m ∈ ω → n ∈ ω → m ^ₙ S(n) = m ×ₙ (m ^ₙ n).*)
(*Proof.*)
  (*intros m n P1 P2.*)
  (*apply (exp_proto_e2 _ _ P1 P2).*)
(*Qed.*)
(*----------------------------------------------------------------------------*)

(*Ltac *)
(*Ltac is_nat :=*)
  (*repeat match goal with*)
    (*| [       |- ?P = ?P         ] => apply eq_r*)
    (*| [       |- 𝟢 ∈ ω           ] => apply empty_is_nat*)
    (*| [       |- 𝟣 ∈ ω           ] => apply one_is_nat*)
    (*| [ H: ?P |- ?P              ] => apply H*)
    (*| [       |- ⟨_, _⟩ ∈ cp _ _ ] => apply cp_i*)
    (*| [       |- (S(_)) ∈ ω      ] => apply suc_is_nat*)
    (*| [       |- ?P +ₙ ?Q ∈ ω    ] => apply nat_add_close*)
    (*| [       |- ?P ×ₙ ?Q ∈ ω    ] => apply nat_mul_close*)
  (*end.*)

(*Flow: nat_add enough equation into the goal *)
      (*run nat_normal_form to normalize it *)
      (*exchange order of nat_mulple (I don't know how to do it automaticly now) *)
      (*run nat_rea to reduce result *)
      (*run is_nat to clean up *)
(*Ltac nat_unwrap_nat_mul_ M :=*)
  (*repeat match M with*)
    (*| ?R ×ₙ (?P +ₙ ?Q) => rewrite (distributive_l R P Q)*)
    (*| (?P +ₙ ?Q) ×ₙ ?R => rewrite (nat_mul_commutative (P +ₙ Q) R)*)
    (*| ?P ×ₙ (?Q ×ₙ ?R) => rewrite (nat_mul_commutative P (Q ×ₙ R))*)
    (*| ?P ×ₙ ?Q         => nat_unwrap_nat_mul_ P; nat_unwrap_nat_mul_ Q*)
    (*| ?P +ₙ ?Q         => nat_unwrap_nat_mul_ P; nat_unwrap_nat_mul_ Q*)
  (*end.*)

(*Ltac nat_unwrap_nat_mul :=*)
  (*repeat match goal with*)
    (*| [ |- ?P = ?Q ] => nat_unwrap_nat_mul_ P; nat_unwrap_nat_mul_ Q*)
  (*end.*)

(*Ltac nat_unwrap_nat_add_ M :=*)
  (*repeat match M with*)
    (*| ?P +ₙ (?Q +ₙ ?R) => rewrite (nat_add_associative P Q R)*)
    (*| ?P +ₙ ?Q         => nat_unwrap_nat_add_ P*)
  (*end.*)

(*Ltac nat_unwrap_nat_add :=*)
  (*repeat match goal with*)
    (*| [ |- ?P = ?Q ] => nat_unwrap_nat_add_ P; nat_unwrap_nat_add_ Q*)
  (*end.*)

(*Ltac nat_normal_form :=*)
  (*nat_unwrap_nat_mul;*)
  (*nat_unwrap_nat_add.*)

(*Ltac nat_red_ M P :=*)
  (*repeat match M with*)
    (*[>| P              => assumption<]*)
    (*[>| _ +ₙ P         => assumption [>do nothing<]<]*)
    (*| P +ₙ ?Q        => rewrite (nat_add_commutative P Q)*)
    (*| (?R +ₙ P) +ₙ ?Q => rewrite (nat_add_cyc R P Q)*)
    (*| ?Q +ₙ _        => nat_red_ Q P*)
  (*end.*)

(*Ltac nat_red :=*)
  (*repeat match goal with*)
    (*| [ |- ?P               = ?P      ] => reflexivity*)
    (*| [ |- _          +ₙ ?P = _ +ₙ ?P ] => apply nat_add_cancellation_inverse*)
    (*| [ |- ?P         +ₙ ?Q = _ +ₙ ?P ] => rewrite (nat_add_commutative P Q)*)
    (*| [ |- (?R +ₙ ?P) +ₙ ?Q = _ +ₙ ?P ] => rewrite (nat_add_cyc R P Q)*)
    (*| [ |- ?R         +ₙ _  = _ +ₙ ?P ] => repeat nat_red_ R P*)
  (*end.*)


(*Lemma test: forall a b c d, a ∈ ω -> b ∈ ω -> c ∈ ω -> d ∈ ω ->*)
  (*(a ×ₙ b) +ₙ a ×ₙ (c +ₙ d) ×ₙ (a +ₙ b) = a ×ₙ (c +ₙ d) ×ₙ (a +ₙ b) +ₙ (a ×ₙ b).*)
(*Proof.*)
  (*intros a b c d P1 P2 P3 P4.*)
  (*nat_normal_form.*)
  (*nat_red.*)
  (*all: is_nat.*)
(*Qed.*)
(*----------------------------------------------------------------------------*)
