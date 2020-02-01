Require Import axiom.logic.
Require Import axiom.axiom.
Require Import operation.basic.

(* Order Pairs *)
Definition opair (A: set) (B: set) := {{A}, {A, B}}.

Notation "⟨ A , B ⟩" := (opair A B) (at level 60).

Lemma in_opair_elim: forall A B x, x ∈ ⟨A, B⟩ -> 
  x = {A} \/ x = {A, B}.
Proof.
  intros A B x P1.
  apply (in_pair_equal ({A}) ({A, B}) x P1).
Qed.

(* 3A *)
Theorem opair_equal_intro: forall A B C D, (A = C) -> (B = D) ->
  ⟨A, B⟩ = ⟨C, D⟩.
Proof.
  intros A B C D P1 P2.
  rewrite P1.
  rewrite P2.
  reflexivity.
Qed.

Theorem opair_equal_elim: forall A B C D, ⟨A, B⟩ = ⟨C, D⟩ -> 
  (A = C) /\ (B = D).
Proof.
  intros A B C D P1.
  destruct (pair_pair_equal_1 ({A}) ({A, B}) ({C}) ({C, D}) P1) as [P2|P2].
  + symmetry in P1.
    destruct (pair_pair_equal_2 ({C}) ({C, D}) ({A}) ({A, B}) P1) as [P3|P3].
    - split.
      * apply (singleton_equal A C P2).
      * symmetry in P1.
        destruct (pair_pair_equal_2 ({A}) ({A, B}) ({C}) ({C, D}) P1) as [P4|P4].
        { symmetry in P3.
          rewrite <- (singleton_pair_equal_2 A C D P3).
          symmetry in P4.
          symmetry.
          apply (singleton_pair_equal_3 C A B P4). }
        { destruct (pair_pair_equal_2 A B C D P4) as [P5|P5].
          { rewrite P5.
            symmetry in P3.
            apply (singleton_pair_equal_3 A C D P3). }
          { apply P5. } }
    - split.
      * apply (singleton_equal A C P2).
      * destruct (pair_pair_equal_2 C D A B P3) as [P4|P4].
        { symmetry in P3.
          destruct (pair_pair_equal_2 A B C D P3) as [P5|P5].
          { rewrite P5.
            rewrite P4.
            symmetry.
            apply (singleton_equal A C P2). }
          { apply P5. } }
        { symmetry.
          apply P4. }
  + split.
    - apply (singleton_pair_equal_1 A C D P2).
    - destruct (pair_pair_equal_2 ({A}) ({A, B}) ({C}) ({C, D}) P1) as [P3|P3].
      * rewrite <- (singleton_pair_equal_2 A C D P2).
        symmetry.
        symmetry in P3.
        apply (singleton_pair_equal_3 C A B P3).
      * destruct (pair_pair_equal_2 A B C D P3) as [P4|P4].
        { rewrite P4.
          apply (singleton_pair_equal_3 A C D P2). }
        { apply P4. }
Qed.

Theorem opair_equal_elim_fst: forall A B C D, ⟨A, B⟩ = ⟨C, D⟩ -> 
  (A = C).
Proof.
  intros A B C D P1.
  destruct (opair_equal_elim _ _ _ _ P1) as [P2 _].
  apply P2.
Qed.

Theorem opair_equal_elim_snd: forall A B C D, ⟨A, B⟩ = ⟨C, D⟩ -> 
  (B = D).
Proof.
  intros A B C D P1.
  destruct (opair_equal_elim _ _ _ _ P1) as [_ P2].
  apply P2.
Qed.

Lemma opair_superset: forall A B C, A ∈ C -> B ∈ C -> 
  ⟨A, B⟩ ∈ 𝒫(𝒫(C)).
Proof.
  intros A B C P1 P2.
  apply (subset_in_power).
  intros x P3.
  apply (subset_in_power).
  intros y P4.
  destruct (in_pair_equal ({A}) ({A, B}) x P3) as [P5|P5].
  + rewrite P5 in P4.
    rewrite (in_singleton_equal A y P4) in P1.
    apply P1.
  + rewrite P5 in P4.
    destruct (in_pair_equal A B y P4) as [P6|P6].
    - rewrite P6.
      apply P1.
    - rewrite P6.
      apply P2.
Qed.
(*----------------------------------------------------------------------------*)

(* Cartesion Product *)
Definition in_cp (s: set) (A: set) (B: set) :=
  exists a b, a ∈ A /\ b ∈ B /\ s = ⟨a, b⟩.

Definition cp (A: set) (B: set) :=
  (subset_ctor 
    (fun s => in_cp s A B)
    (𝒫(𝒫(A ∪ B)))).

Lemma cp_intro: forall A B x y, x ∈ A -> y ∈ B -> 
  ⟨x, y⟩ ∈ cp A B.
Proof.
  intros A B x y P1 P2.
  destruct ((extract_set_property 
    (ax_subset 
      (fun S => in_cp S A B) 
      (𝒫(𝒫(A ∪ B))))) (⟨x, y⟩)) as [_ P3].
  apply P3.
  split.
  + apply opair_superset.
    - apply (in_in_union2_1 _ _ _ P1).
    - apply (in_in_union2_2 _ _ _ P2).
  + exists x.
    exists y.
    split.
    - apply P1.
    - split.
      * apply P2.
      * reflexivity.
Qed.

Lemma cp_elim: forall A B x, x ∈ cp A B -> in_cp x A B.
  intros A B x P1.
  destruct ((extract_set_property 
    (ax_subset 
      (fun S => in_cp S A B) 
      (𝒫(𝒫(A ∪ B))))) x) as [P2 _].
  destruct (P2 P1) as [_ P3].
  apply P3.
Qed.
(*----------------------------------------------------------------------------*)

(* Relation *)
Definition rel (R: set) :=
  forall r, r ∈ R -> exists a b, r = ⟨a, b⟩.
(*----------------------------------------------------------------------------*)

(* Domain *)
Definition in_dom (x: set) (R: set) :=
  exists y, ⟨x, y⟩ ∈ R.

Definition dom (A: set) :=
  subset_ctor (fun x => (in_dom x A)) (∪(∪(A))).

Notation "dom( A )" := (dom A) (at level 60, no associativity).

Lemma dom_superset: forall A x, in_dom x A -> x ∈ ∪(∪(A)).
Proof.
  intros A x P1.
  destruct P1 as [y P1].
  apply in_in_union.
  exists ({x, y}).
  split.
  + apply in_in_union.
    exists (⟨x, y⟩).
    split.
    - apply P1.
    - apply in_pair_2.
  + apply in_pair_1.
Qed.

Lemma in_dom_intro: forall R x y, ⟨x, y⟩ ∈ R -> in_dom x R.
Proof.
  intros R x y P1.
  exists y.
  apply P1.
Qed.

Lemma dom_intro: forall R x, in_dom x R -> x ∈ dom(R).
Proof.
  intros R x P1.
  destruct P1 as [y P1].
  destruct (extract_set_property 
    (ax_subset (fun x => (in_dom x R)) (∪(∪(R)))) 
    x) as [_ P2].
  apply P2.
  split.
  + apply dom_superset.
    exists y.
    apply P1.
  + exists y.
    apply P1.
Qed.

Lemma dom_intro_2: forall R x y, ⟨x, y⟩ ∈ R -> x ∈ dom(R).
Proof.
  intros R x y P1.
  apply dom_intro.
  apply (in_dom_intro R x y P1).
Qed.

Lemma dom_elim: forall R x, x ∈ dom(R) -> in_dom x R.
Proof.
  intros R x P1.
  destruct (extract_set_property 
    (ax_subset (fun x => (in_dom x R)) (∪(∪(R)))) 
    x) as [P2 _].
  apply P2.
  apply P1.
Qed.

Lemma subset_dom: forall F G, F ⊆ G -> dom(F) ⊆ dom(G).
Proof.
  intros F G P1 x P2.
  destruct (dom_elim _ _ P2) as [y P3].
  apply (dom_intro _ _ (in_dom_intro _ _ _ (P1 _ P3))).
Qed.

Lemma not_in_dom: forall F x, x ∉  dom(F) -> forall y, ⟨x, y⟩ ∉  F.
Proof. 
  intros F x.
  apply (contraposition2 (forall y, ⟨x, y⟩ ∉  F) (x ∈ dom(F))).
  intros P1.
  destruct (not_forall_exists_not _ _ P1) as [y P2].
  apply dom_intro.
  exists y.
  apply (NN_elim _ P2).
Qed.
(*----------------------------------------------------------------------------*)

(* Range *)
Definition in_ran (y: set) (R: set) :=
  exists x, ⟨x, y⟩ ∈ R.

Definition ran (A: set) := 
  subset_ctor (fun x => (in_ran x A)) (∪(∪(A))).

Notation "ran( A )" := (ran A) (at level 60, no associativity).

Lemma ran_superset: forall A y, in_ran y A -> y ∈ ∪(∪(A)).
Proof.
  intros A y P1.
  destruct P1 as [x P1].
  apply in_in_union.
  exists ({x, y}).
  split.
  + apply in_in_union.
    exists (⟨x, y⟩).
    split.
    - apply P1.
    - apply in_pair_2.
  + apply in_pair_2.
Qed.

Lemma in_ran_intro: forall R x y, ⟨x, y⟩ ∈ R -> in_ran y R.
Proof.
  intros R x y P1.
  exists x.
  apply P1.
Qed.

Lemma ran_intro: forall R y, in_ran y R -> y ∈ ran(R).
Proof.
  intros R y P1.
  destruct P1 as [x P1].
  destruct (extract_set_property 
    (ax_subset (fun x => (in_ran x R)) (∪(∪(R)))) 
    y) as [_ P2].
  apply P2.
  split.
  + apply ran_superset.
    exists x.
    apply P1.
  + exists x.
    apply P1.
Qed.

Lemma ran_intro_2: forall R x y, ⟨x, y⟩ ∈ R -> y ∈ ran(R).
Proof.
  intros R x y P1.
  apply ran_intro.
  apply (in_ran_intro R x y P1).
Qed.

Lemma ran_elim: forall R y, y ∈ ran(R) -> in_ran y R.
Proof.
  intros R y P1.
  destruct (extract_set_property 
    (ax_subset (fun x => (in_ran x R)) (∪(∪(R)))) 
    y) as [P2 _].
  apply P2.
  apply P1.
Qed.

Lemma subset_ran: forall F G, F ⊆ G -> ran(F) ⊆ ran(G).
Proof.
  intros F G P1 y P2.
  destruct (ran_elim _ _ P2) as [x P3].
  apply (ran_intro _ _ (in_ran_intro _ _ _ (P1 _ P3))).
Qed.
(*----------------------------------------------------------------------------*)

(* Filed *)
Definition filed (R:set) :=
  dom R ∪ran R.

Notation "fld( A )" := (filed A) (at level 60, no associativity).

Lemma fld_elim: forall x A, x ∈ fld(A) -> x ∈ dom(A) \/ x ∈ ran(A).
Proof.
  intros x A P1.
  destruct (in_union2_in _ _ _ P1) as [P2|P2].
  + left.
    apply P2.
  + right.
    apply P2.
Qed.

Lemma fld_intro_dom: forall x A, x ∈ dom(A) -> x ∈ fld(A).
Proof.
  intros x A P1.
  apply (in_in_union2_1 _ _ _ P1).
Qed.

Lemma fld_intro_ran: forall x A, x ∈ ran(A) -> x ∈ fld(A).
Proof.
  intros x A P1.
  apply (in_in_union2_2 _ _ _ P1).
Qed.

Definition rover (R: set) (A: set) :=
  (rel R) /\ (dom(R) ⊆ A) /\ (ran(R) ⊆ A).  
(*----------------------------------------------------------------------------*)
