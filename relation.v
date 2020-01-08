Require Import logic.
Require Import axiom.
Require Import basic.

(* order pair *)
(* Definition opair (A: set) (B: set) := {{A}, {A, B}}. *)
(* Notation "⟨ A , B ⟩" := (opair A B) (at level 60). *)

Lemma in_opair_elim: forall A B x, x ∈ ⟨A, B⟩ -> x = {A} \/ x = {A, B}.
Proof.
  intros A B x P1.
  apply (in_pair_equal ({A}) ({A, B}) x P1).
Qed.

(* 3A *)
Theorem opair_equal_intro: forall A B C D, (A = C) /\ (B = D) -> ⟨A, B⟩ = ⟨C, D⟩.
Proof.
  intros A B C D P1.
  destruct P1 as [P2 P3].
  rewrite P2.
  rewrite P3.
  reflexivity.
Qed.

Theorem opair_equal_elim: forall A B C D, ⟨A, B⟩ = ⟨C, D⟩ -> (A = C) /\ (B = D).
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
 
Theorem opair_equal_elim_1: forall A B C D, ⟨A, B⟩ = ⟨C, D⟩ -> (A = C).
Proof.
  intros A B C D P1.
  destruct (opair_equal_elim _ _ _ _ P1) as [P2 _].
  apply P2.
Qed.

Theorem opair_equal_elim_2: forall A B C D, ⟨A, B⟩ = ⟨C, D⟩ -> (B = D).
Proof.
  intros A B C D P1.
  destruct (opair_equal_elim _ _ _ _ P1) as [_ P2].
  apply P2.
Qed.

(* 3B *)
Lemma opair_superset: forall A B C, A ∈ C -> B ∈ C -> ⟨A, B⟩ ∈ 𝒫(𝒫(C)).
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

Definition in_cp s A B:=
  exists a b, a ∈ A /\ b ∈ B /\ s = ⟨a, b⟩.

(* Cartesion Product *)
Definition cp (A: set) (B: set) :=
  (subset_ctor 
    (fun s => in_cp s A B)
    (𝒫(𝒫(A ∪ B)))).

Lemma cp_intro: forall A B x y, x ∈ A -> y ∈ B -> ⟨x, y⟩ ∈ cp A B.
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
Proof.
  intros A B x P1.
  destruct ((extract_set_property 
    (ax_subset 
      (fun S => in_cp S A B) 
      (𝒫(𝒫(A ∪ B))))) x) as [P2 _].
  destruct (P2 P1) as [_ P3].
  apply P3.
Qed.

(* Definition relation (R: set) := *)
(*   forall r, r ∈ R -> exists a b, r = ⟨a, b⟩. *)

(* Definition in_domain (x: set) (R: set) := *)
(*   exists y, ⟨x, y⟩ ∈ R. *)
(* Definition domain (A: set) := *)
(*   subset_ctor (fun x => (in_domain x A)) (∪(∪(A))). *)
(* Notation "dom( A )" := (domain A) (at level 60, no associativity). *)

Definition in_range (y: set) (R: set) :=
  exists x, ⟨x, y⟩ ∈ R.
Definition range (A: set) := 
  subset_ctor (fun x => (in_range x A)) (∪(∪(A))).
Notation "ran( A )" := (range A) (at level 60, no associativity).

Definition relation_on (R: set) (A: set) := 
  forall r, r ∈ R -> exists a b, a ∈ A /\ b ∈ A /\ r = ⟨a, b⟩.

Lemma relation_on_elim: forall R A, relation_on R A -> relation R.
Proof.
  intros R A P1 r P2.
  destruct(P1 r P2) as [a [b [_ [_ P3]]]].
  exists a.
  exists b.
  apply P3.
Qed.
  
Definition filed (R:set) :=
  domain R ∪range R.
Notation "fld( A )" := (filed A) (at level 60, no associativity).

(* 3D *)
Lemma domain_superset: forall A x, in_domain x A -> x ∈ ∪(∪(A)).
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

Lemma range_superset: forall A y, in_range y A -> y ∈ ∪(∪(A)).
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

Lemma in_domain_intro: forall R x y, ⟨x, y⟩ ∈ R -> in_domain x R.
Proof.
  intros R x y P1.
  exists y.
  apply P1.
Qed.

Lemma domain_intro: forall R x, in_domain x R -> x ∈ dom(R).
Proof.
  intros R x P1.
  destruct P1 as [y P1].
  destruct (extract_set_property 
    (ax_subset (fun x => (in_domain x R)) (∪(∪(R)))) 
    x) as [_ P2].
  apply P2.
  split.
  + apply domain_superset.
    exists y.
    apply P1.
  + exists y.
    apply P1.
Qed.

Lemma domain_elim: forall R x, x ∈ dom(R) -> in_domain x R.
Proof.
  intros R x P1.
  destruct (extract_set_property 
    (ax_subset (fun x => (in_domain x R)) (∪(∪(R)))) 
    x) as [P2 _].
  apply P2.
  apply P1.
Qed.

Lemma subset_domain: forall F G, F ⊆ G -> domain(F) ⊆ domain(G).
Proof.
  intros F G P1 x P2.
  destruct (domain_elim _ _ P2) as [y P3].
  apply (domain_intro _ _ (in_domain_intro _ _ _ (P1 _ P3))).
Qed.

Lemma not_in_domain: forall F x, x ∉  dom(F) -> forall y, ⟨x, y⟩ ∉  F.
Proof. 
  intros F x.
  apply (contraposition2 (forall y, ⟨x, y⟩ ∉  F) (x ∈ dom(F))).
  intros P1.
  destruct (not_forall_exists_not _ _ P1) as [y P2].
  apply domain_intro.
  exists y.
  apply (NN_elim _ P2).
Qed.

Lemma in_range_intro: forall R x y, ⟨x, y⟩ ∈ R -> in_range y R.
Proof.
  intros R x y P1.
  exists x.
  apply P1.
Qed.

Lemma range_intro: forall R y, in_range y R -> y ∈ ran(R).
Proof.
  intros R y P1.
  destruct P1 as [x P1].
  destruct (extract_set_property 
    (ax_subset (fun x => (in_range x R)) (∪(∪(R)))) 
    y) as [_ P2].
  apply P2.
  split.
  + apply range_superset.
    exists x.
    apply P1.
  + exists x.
    apply P1.
Qed.

Lemma range_elim: forall R y, y ∈ ran(R) -> in_range y R.
Proof.
  intros R y P1.
  destruct (extract_set_property 
    (ax_subset (fun x => (in_range x R)) (∪(∪(R)))) 
    y) as [P2 _].
  apply P2.
  apply P1.
Qed.
  
Lemma subset_range: forall F G, F ⊆ G -> ran(F) ⊆ ran(G).
Proof.
  intros F G P1 y P2.
  destruct (range_elim _ _ P2) as [x P3].
  apply (range_intro _ _ (in_range_intro _ _ _ (P1 _ P3))).
Qed.

(* Skip n-ary *)

(* Definition function (F: set) := *)
(*  (relation F) /\ (forall a b1 b2, ⟨a, b1⟩ ∈ F /\ ⟨a, b2⟩ ∈ F -> b1 = b2). *)

Definition fun_maps (F: set) (A: set) (B: set) :=
  (function F) /\ (dom(F) = A) /\ (ran(F) ⊆ B).

Definition onto (F: set) (A: set) (B: set) :=
  (dom(F) = A) /\ (ran(F) = B).

Lemma single_value_is_function: forall x y, function ({⟨x, y⟩}).
Proof.
  intros x y.
  split.
  + intros s P1.
    exists x.
    exists y.
    symmetry.
    apply (in_singleton_equal _ _ P1).
  + intros a0 b1 b2 [P1 P2].
    destruct (opair_equal_elim _ _ _ _ (in_singleton_equal _ _ P1)) as [_ P3].
    rewrite <- P3.
    destruct (opair_equal_elim _ _ _ _ (in_singleton_equal _ _ P2)) as [_ P4].
    apply P4.
Qed.

Lemma single_value_domain: forall x y, dom({⟨x, y⟩}) = ({x}).
Proof. 
  intros x y.
  apply ax_exten.
  intros s.
  split.
  + intros P1.
    destruct (domain_elim _ _ P1) as [t P2].
    destruct (opair_equal_elim _ _ _ _ (in_singleton_equal _ _ P2)) as [P3 _].
    rewrite P3.
    apply in_singleton.
  + intros P1.
    apply domain_intro.
    exists y.
    rewrite (in_singleton_equal _ _ P1).
    apply in_singleton.
Qed.

Lemma single_value_range: forall x y, ran({⟨x, y⟩}) = ({y}).
Proof. 
  intros x y.
  apply ax_exten.
  intros s.
  split.
  + intros P1.
    destruct (range_elim _ _ P1) as [t P2].
    destruct (opair_equal_elim _ _ _ _ (in_singleton_equal _ _ P2)) as [_ P3].
    rewrite <- P3.
    apply in_singleton.
  + intros P1.
    apply range_intro.
    exists x.
    rewrite (in_singleton_equal _ _ P1).
    apply in_singleton.
Qed.

Lemma fun_val_thm: forall F x, exists y, function F -> x ∈ dom(F) -> 
  (⟨x, y⟩ ∈ F /\ (forall y2, ⟨x, y2⟩ ∈ F -> y = y2)).
Proof.
  intros F x.
  destruct (LEM (x ∈ dom(F))) as [P1|P1].
  + destruct (domain_elim _ _ P1) as [y P2].
    exists y.
    intros P3 P4.
    split.
    - apply P2.
    - intros y2 P5.
      destruct P3 as [_ P3].
      apply (P3 x y y2 (conj P2 P5)).
  + exists x.
    intros _ P2.
    contradiction.
Qed.

Definition fun_val (F:set) (x:set) :=
  extract_set (fun_val_thm F x).

Theorem fun_val_elim: forall F x y, y = fun_val F x -> function F -> x ∈ dom(F) ->
  (⟨x, y⟩ ∈ F /\ (forall y2, ⟨x, y2⟩ ∈ F -> y = y2)).
Proof.
  intros F x y P1.
  rewrite P1.
  apply (extract_set_property (fun_val_thm F x)).
Qed.

Theorem fun_val_intro: forall F x y, function F -> x ∈ dom(F) -> ⟨x, y⟩ ∈ F -> 
  y = fun_val F x.
Proof.
  intros F x y P1 P2 P3.
  destruct (extract_set_property (fun_val_thm F x) P1 P2) as [_ P4].
  rewrite <- (P4 y P3). 
  reflexivity.
Qed.

Lemma fun_val_basic: forall F x, function F -> x ∈ dom(F) -> ⟨x, fun_val F x⟩ ∈ F.
Proof.
  intros F x P1 P2.
  destruct (extract_set_property (fun_val_thm F x) P1 P2) as [P3 _].
  apply P3.
Qed.

Lemma fun_val_range: forall F x, function F -> x ∈ dom(F) -> 
  fun_val F x ∈ ran(F).
Proof.
  intros F x P1 P2.
  apply range_intro.
  exists x.
  apply (fun_val_basic F x P1 P2).
Qed.

Definition single_rooted (R: set) :=
  (forall a1 a2 b, ⟨a1, b⟩ ∈ R /\ ⟨a2, b⟩ ∈ R -> a1 = a2).

Definition one_to_one (F: set) :=
  (function F) /\ (single_rooted F). 

Definition in_inverse (x: set) (R: set) :=
  (exists a b, ⟨a, b⟩ ∈ R /\ x = ⟨b, a⟩).
Definition inverse (R: set) := 
  subset_ctor (fun x => (in_inverse x R)) (cp (ran(R)) (dom(R))).

Lemma inverse_superset: forall x R, in_inverse x R -> x ∈ cp (ran(R)) (dom(R)).
Proof.
  intros x R P1.
  destruct P1 as [a [b [P1 P2]]].
  rewrite P2.
  apply cp_intro.
  + apply range_intro.
    exists a.
    apply P1.
  + apply domain_intro.
    exists b.
    apply P1.
Qed.

Theorem inverse_intro: forall x y R, ⟨x, y⟩ ∈ R -> ⟨y, x⟩ ∈ inverse R.
Proof.
  intros x y R P1.
  destruct (extract_set_property 
    (ax_subset 
      (fun s => in_inverse s R) 
      (cp (ran(R)) (dom(R)))) (⟨y, x⟩)) as [_ P2].
  apply P2.
  assert (in_inverse (⟨y, x⟩) R) as P3.
  { exists x.
    exists y.
    split.
    + apply P1.
    + reflexivity. }
  split.
  + apply (inverse_superset _ _ P3).
  + apply P3.
Qed.

Lemma inverse_elim: forall x y R, ⟨x, y⟩ ∈ inverse R -> ⟨y, x⟩ ∈ R.
Proof.
  intros x y R P1.
  destruct (extract_set_property 
    (ax_subset 
      (fun s => in_inverse s R) 
      (cp (ran(R)) (dom(R)))) (⟨x, y⟩)) as [P2 _].
  destruct (P2 P1) as [_ [a [b [P3 P4]]]].
  destruct (opair_equal_elim _ _ _ _ P4) as [P5 P6].
  rewrite P5.
  rewrite P6.
  apply P3.
Qed.

Definition in_composition (x: set) (F: set) (G: set) :=
  (exists a b c, ⟨a, b⟩ ∈ F /\ ⟨b, c⟩ ∈ G /\ x = ⟨a, c⟩).
Definition composition (F: set) (G: set) := 
  subset_ctor (fun x => (in_composition x F G)) (cp (dom(F)) (ran(G))).
Lemma composition_superset: forall x F G, in_composition x F G -> 
  x ∈ cp (dom(F)) (ran(G)).
Proof.
  intros x F G P1.
  destruct P1 as [a [b [c [P1 [P2 P3]]]]].
  rewrite P3.
  apply cp_intro.
  + apply domain_intro.
    exists b.
    apply P1.
  + apply range_intro.
    exists b.
    apply P2.
Qed.

Theorem composition_is_relation: forall F G, relation(composition F G).
Proof.
  intros F G r P1.
  destruct (extract_set_property 
    (ax_subset 
      (fun s => in_composition s F G) 
      (cp (dom(F)) (ran(G)))) r) as [P2 _].
  destruct (P2 P1) as [P3 _].
  destruct (cp_elim _ _ _ P3) as [a [b [_ [_ P4]]]].
  exists a.
  exists b.
  apply P4.
Qed.

Theorem composition_intro: forall x z F G, (exists y, ⟨x, y⟩ ∈ F /\ ⟨y, z⟩ ∈ G) -> 
  ⟨x, z⟩ ∈ composition F G.
Proof.
  intros x z F G P1.
  destruct P1 as [y [P1 P2]].
  destruct (extract_set_property 
    (ax_subset 
      (fun s => in_composition s F G) 
      (cp (dom(F)) (ran(G)))) (⟨x, z⟩)) as [_ P3].
  apply P3.
  assert (in_composition (⟨x, z⟩) F G) as P4.
  { exists x.
    exists y.
    exists z.
    split.
    + apply P1.
    + split. 
      - apply P2. 
      - reflexivity. }
  split.
  + apply (composition_superset _ _ _ P4).
  + apply P4.
Qed.

Lemma composition_elim: forall x z F G, ⟨x, z⟩ ∈ composition F G -> 
  (exists y, ⟨x, y⟩ ∈ F /\ ⟨y, z⟩ ∈ G).
Proof.
  intros x z F G P1.
  destruct (extract_set_property 
    (ax_subset 
      (fun s => in_composition s F G) 
      (cp (dom(F)) (ran(G)))) (⟨x, z⟩)) as [P2 _].
  destruct (P2 P1) as [_ [a [b [c [P3 [P4 P5]]]]]].
  destruct (opair_equal_elim _ _ _ _ P5) as [P6 P7].
  exists b.
  split.
  + rewrite P6.
    apply P3.
  + rewrite P7.
    apply P4.
Qed.

Definition in_restriction (x: set) (F: set) (A: set) :=
  (exists a b, ⟨a, b⟩ ∈ F /\ x = ⟨a, b⟩ /\ a ∈ A).
Definition restriction (F: set) (A: set) := 
  subset_ctor (fun x => (in_restriction x F A)) F.

Theorem restriction_intro: forall x y F A, ⟨x, y⟩ ∈ F -> x ∈ A -> 
  ⟨x, y⟩ ∈ restriction F A.
Proof.
  intros x y F A P1 P2.
  destruct (extract_set_property 
    (ax_subset 
      (fun s => in_restriction s F A) F) 
    (⟨x, y⟩)) as [_ P3].
  apply P3.
  split.
  + apply P1.
  + exists x.
    exists y.
    split.
    - apply P1.
    - split.
      * reflexivity. 
      * apply P2.
Qed.

Lemma restriction_elim: forall x y F A, ⟨x, y⟩ ∈ restriction F A -> 
  ⟨x, y⟩ ∈ F /\ x ∈ A.
Proof.
  intros x y F A P1.
  destruct (extract_set_property 
    (ax_subset 
      (fun s => in_restriction s F A) F) 
    (⟨x, y⟩)) as [P2 _].
  destruct (P2 P1) as [P3 [a [b [_ [P4 P5]]]]].
  destruct (opair_equal_elim _ _ _ _ P4) as [P6 _].
  split.
  + apply P3.
  + rewrite P6.
    apply P5.
Qed.

Definition image (F: set) (A: set) := 
  ran(restriction F A).

Theorem image_intro: forall y F A, (exists x, ⟨x, y⟩ ∈ F /\ x ∈ A) -> y ∈ image F A.
Proof.
  intros y F A P1.
  destruct P1 as [x [P1 P2]].
  apply range_intro.
  exists x.
  apply restriction_intro.
  + apply P1.
  + apply P2.
Qed.

Lemma image_elim: forall y F A, y ∈ image F A -> (exists x, ⟨x, y⟩ ∈ F /\ x ∈ A).
Proof.
  intros y F A P1.
  destruct (range_elim _ _ P1) as [x P2].
  destruct (restriction_elim _ _ _ _ P2) as [P3 P4].
  exists x.
  split.
  + apply P3.
  + apply P4.
Qed.

(* 3F *)
Theorem inverse_domain: forall F, dom(inverse F) = ran(F).
Proof.
  intros F.
  apply ax_exten.
  intros x.
  split.
  + intros P1.
    destruct (domain_elim _ _ P1) as [y P2].
    apply range_intro.
    exists y.
    apply (inverse_elim _ _ _ P2).
  + intros P1.
    destruct (range_elim _ _ P1) as [y P2].
    apply domain_intro.
    exists y.
    apply (inverse_intro _ _ _ P2).
Qed.
    
Theorem inverse_range: forall F, ran(inverse F) = dom(F).
Proof.
  intros F.
  apply ax_exten.
  intros x.
  split.
  + intros P1.
    destruct (range_elim _ _ P1) as [y P2].
    apply domain_intro.
    exists y.
    apply (inverse_elim _ _ _ P2).
  + intros P1.
    destruct (domain_elim _ _ P1) as [y P2].
    apply range_intro.
    exists y.
    apply (inverse_intro _ _ _ P2).
Qed.

Theorem inverse_is_relation: forall R, relation (inverse R).
Proof.
  intros R x P1.
  destruct (extract_set_property 
    (ax_subset 
      (fun s => in_inverse s R) 
      (cp (ran(R)) (dom(R)))) x) as [P2 _].
  destruct (P2 P1) as [_ [a [b [P3 P4]]]].
  exists b.
  exists a.
  apply P4.
Qed.

Theorem inverse_inverse: forall F, relation F -> inverse (inverse F) = F.
Proof.
  intros F P1.
  apply ax_exten.
  intros x.
  split.
  + intros P2.
    destruct ((inverse_is_relation (inverse F)) x P2) as [a [b P3]].
    rewrite P3.
    apply inverse_elim.
    apply inverse_elim.
    rewrite <- P3.
    apply P2.
  + intros P2.
    destruct (P1 x P2) as [a [b P3]].
    rewrite P3.
    apply inverse_intro.
    apply inverse_intro.
    rewrite <- P3.
    apply P2.
Qed.

(* 3F *)
Lemma inverse_function: forall F, single_rooted F <-> function (inverse F).
Proof.
  intros F.
  split.
  + intros P1.
    split.
    - intros x P2.
      destruct (inverse_is_relation F x P2) as [a [b P3]].
      exists a.
      exists b.
      apply P3.
    - intros a b1 b2 P2.
      destruct P2 as [P2 P3].
      apply (P1 b1 b2 a).
      split.
      * apply (inverse_elim _ _ _ P2).
      * apply (inverse_elim _ _ _ P3).
  + intros P1.
    intros a1 a2 b P2.
    destruct P2 as [P2 P3].
    destruct P1 as [_ P1].
    apply (P1 b a1 a2).
    split.
    - apply (inverse_intro _ _ _ P2).
    - apply (inverse_intro _ _ _ P3).
Qed.

Lemma function_inverse: forall F, relation F -> (function F <-> single_rooted(inverse F)).
Proof.
  intros F P1.
  split.
  + intros P2 a1 a2 b P3.
    destruct P2 as [_ P2].
    destruct P3 as [P3 P4].
    apply (P2 b a1 a2).
    split.
    - apply (inverse_elim _ _ _ P3). 
    - apply (inverse_elim _ _ _ P4).
  + intros P2.
    split.
    - apply P1.
    - intros a b1 b2 P3.
      destruct P3 as [P3 P4].
      apply (P2 b1 b2 a).
      split.
      * apply (inverse_intro _ _ _ P3).
      * apply (inverse_intro _ _ _ P4).
Qed.

(* 3G *)
Lemma inverse_function_exist_1: forall F, one_to_one F -> 
  (forall x, x ∈ dom(F) -> (fun_val (inverse F) (fun_val F x)) = x).
Proof.
  intros F P1 x P2.
  symmetry.
  apply fun_val_intro.
  + destruct P1 as [_ P1].
    destruct (inverse_function F) as [P3 _].
    apply (P3 P1).
  + rewrite inverse_domain.
    apply range_intro.
    exists x.
    destruct P1 as [P1 _].
    apply (fun_val_basic _ _ P1 P2).
  + apply inverse_intro.
    destruct P1 as [P1 _].
    apply (fun_val_basic _ _ P1 P2).
Qed.

Lemma inverse_function_exist_2: forall F, one_to_one F -> 
  (forall x, x ∈ ran(F) -> (fun_val F (fun_val (inverse F) x)) = x).
Proof.
  intros F P1 x P2.
  symmetry.
  apply fun_val_intro.
  + destruct P1 as [P1 _].
    apply P1.
  + apply domain_intro.
    exists x.
    apply inverse_elim.
    destruct P1 as [_ P1].
    destruct (inverse_function F) as [P3 _].
    rewrite <- inverse_domain in P2.
    apply (fun_val_basic _ _ (P3 P1) P2).
  + apply inverse_elim.
    destruct P1 as [_ P1].
    destruct (inverse_function F) as [P3 _].
    rewrite <- inverse_domain in P2.
    apply (fun_val_basic _ _ (P3 P1) P2).
Qed.

(* 3H *)
Lemma composition_function: forall F G, function F -> function G ->
  function (composition F G).
Proof.
  intros F G P1 P2.
  split.
  + apply composition_is_relation.
  + intros a b1 b2 [P3 P4].
    destruct (composition_elim _ _ _ _ P3) as [y1 [P5 P6]].
    destruct (composition_elim _ _ _ _ P4) as [y2 [P7 P8]].
    destruct P1 as [_ P1].
    rewrite (P1 _ _ _ (conj P5 P7)) in P6.
    destruct P2 as [_ P2].
    apply (P2 _ _ _ (conj P6 P8)).
Qed.

(* Lemma composition domain *)
Lemma composition_domain: forall F G x, function F -> function G -> 
  x ∈ dom(composition F G) -> x ∈ dom(F) /\ (fun_val F x) ∈ dom(G).
Proof.
  intros F G x P1 P2 P3.
  destruct (domain_elim _ _ P3) as [z P4].
  destruct (composition_elim _ _ _ _ P4) as [y [P5 P6]].
  split.
  + apply domain_intro.
    exists y.
    apply P5.
  + apply domain_intro.
    exists z.
    assert (x ∈ dom(F)) as P7.
    { apply domain_intro.
      exists y.
      apply P5. }
    rewrite <- (fun_val_intro _ _ _ P1 P7 P5).
    apply P6.
Qed.

Lemma composition_basic: forall F G x, function F -> function G -> 
  x ∈ dom(composition F G) -> 
  (fun_val (composition F G) x) = (fun_val G (fun_val F x)).
Proof.
  intros F G x P1 P2 P3.
  symmetry.
  apply (fun_val_intro _ _ _ (composition_function _ _ P1 P2) P3).
  apply (composition_intro).
  exists (fun_val F x).
  destruct (composition_domain _ _ _ P1 P2 P3) as [P4 P5].
  split.
  + apply (fun_val_basic _ _ P1).
    apply P4.
  + apply (fun_val_basic _ _ P2).
    apply P5.
Qed.

(* 3I *)
Theorem composition_inverse: forall F G, inverse (composition F G) =
  composition (inverse G) (inverse F).
Proof.
  intros F G.
  apply ax_exten.
  intros r.
  split.
  + intros P1.
    destruct (inverse_is_relation _ r P1) as [x [z P2]].
    rewrite P2.
    rewrite P2 in P1.
    apply composition_intro.
    destruct (composition_elim _ _ _ _ (inverse_elim _ _ _ P1)) as [y [P3 P4]].
    exists y.
    split.
    - apply (inverse_intro _ _ _ P4).
    - apply (inverse_intro _ _ _ P3).
  + intros P1.
    destruct (composition_is_relation _ _ r P1) as [x [z P2]].
    rewrite P2.
    rewrite P2 in P1.
    apply inverse_intro.
    apply composition_intro.
    destruct (composition_elim _ _ _ _ P1) as [y [P3 P4]] .
    exists y.
    split.
    - apply (inverse_elim _ _ _ P4).
    - apply (inverse_elim _ _ _ P3).
Qed.

Definition id (A: set) :=
  (subset_ctor 
    (fun s => exists x, s = ⟨x, x⟩)
    (cp A A)).

Lemma id_intro: forall A x, x ∈ A -> ⟨x, x⟩ ∈ id A.
Proof.
  intros A x P1.
  destruct (extract_set_property (ax_subset 
    (fun s => exists x, s = ⟨x, x⟩)
    (cp A A)) (⟨x, x⟩)) as [_ P2].
  apply P2.
  split.
  + apply (cp_intro _ _ _ _ P1 P1).
  + exists x.
    reflexivity.
Qed.

Lemma id_elim: forall A s, s ∈ id A -> exists x, x ∈ A /\ s = ⟨x, x⟩.
Proof. 
  intros A s P1.
  destruct (extract_set_property (ax_subset 
    (fun s => exists x, s = ⟨x, x⟩)
    (cp A A)) s) as [P2 _].
  destruct (P2 P1) as [P3 [x P4]].
  destruct (cp_elim _ _ _ P3) as [a [b [P5 [_ P6]]]].
  exists x.
  split.
  + rewrite P4 in P6. 
    destruct (opair_equal_elim _ _ _ _ P6) as [P7 _].
    rewrite P7.
    apply P5.
  + apply P4.
Qed.
    
Lemma id_is_function: forall A, function (id A).
Proof.
  intros A.
  split.
  + intros r P1.
    destruct (id_elim _ _ P1) as [x [_ P2]].
    exists x.
    exists x.
    apply P2.
  + intros a b1 b2 [P1 P2].
    destruct (id_elim _ _ P1) as [x [_ P3]].
    destruct (id_elim _ _ P2) as [y [_ P4]].
    destruct (opair_equal_elim _ _ _ _ P3) as [P5 P6].
    rewrite P6.
    rewrite <- P5.
    destruct (opair_equal_elim _ _ _ _ P4) as [P7 P8].
    rewrite P7.
    rewrite <- P8.
    reflexivity.
Qed.

Lemma id_domain: forall A, A = dom(id A).
Proof.
  intros A.
  apply ax_exten.
  split.
  + intros P1. 
    apply domain_intro.
    exists x.
    apply (id_intro _ _ P1).
  + intros P1.
    destruct (domain_elim _ _ P1) as [y P2].
    destruct (id_elim _ _ P2) as [z [P3 P4]].
    destruct (opair_equal_elim _ _ _ _ P4) as [P5 _].
    rewrite P5.
    apply P3.
Qed.

Lemma id_range: forall A, A = ran(id A).
Proof.
  intros A.
  apply ax_exten.
  split.
  + intros P1.
    apply range_intro.
    exists x.
    apply (id_intro _ _ P1).
  + intros P1.
    destruct (range_elim _ _ P1) as [y P2].
    destruct (id_elim _ _ P2) as [z [P3 P4]].
    destruct (opair_equal_elim _ _ _ _ P4) as [_ P5].
    rewrite P5.
    apply P3.
Qed.

Lemma id_basic: forall A x, x ∈ A -> x = fun_val (id A) x.
Proof.
  intros A x P1.
  apply fun_val_intro.
  + apply (id_is_function A).
  + rewrite (id_domain A) in P1.
    apply P1.
  + apply (id_intro _ _ P1).
Qed.

Lemma id_inverse: forall A, id A = inverse (id A).
Proof.
  intros A.
  apply ax_exten.
  intros x.
  split.
  + intros P1.
    destruct (id_elim _ _ P1) as [y [_ P2]].
    rewrite P2.
    apply inverse_intro.
    rewrite <- P2.
    apply P1.
  + intro P1.
    destruct (inverse_is_relation (id A) x P1) as [a [b P2]].
    rewrite P2 in P1.
    destruct (id_elim _ _ (inverse_elim _ _ _ P1)) as [z [P3 P4]].
    rewrite P2.
    destruct (opair_equal_elim _ _ _ _ P4) as [P5 P6].
    rewrite P5.
    rewrite P6.
    apply (id_intro _ _ P3).
Qed.

Lemma id_onto: forall A, onto (id A) A A.
Proof.
  intros A.
  split.
  + symmetry. 
    apply id_domain.
  + symmetry.
    apply id_range.
Qed.

Lemma id_one_to_one: forall A, one_to_one(id A).
Proof.
  intros A.
  split.
  + apply id_is_function.
  + intros a1 a2 b [P1 P2].
    destruct (id_elim _ _ P1) as [x1 [_ P3]].
    destruct (id_elim _ _ P2) as [x2 [_ P4]].
    rewrite (opair_equal_elim_1 _ _ _ _ P3).
    rewrite <- (opair_equal_elim_2 _ _ _ _ P3).
    rewrite (opair_equal_elim_1 _ _ _ _ P4).
    apply (opair_equal_elim_2 _ _ _ _ P4).
Qed.

Definition const (A: set) (c: set) :=
  cp A ({c}).
Lemma const_intro: forall A c x, x ∈ A -> ⟨x, c⟩ ∈ const A c.
Proof.
  intros A c x P1.
  apply cp_intro.
  + apply P1.
  + apply in_singleton.
Qed.

Lemma const_elim: forall A c s, s ∈ const A c -> 
  exists x, x ∈ A /\ s = ⟨x, c⟩.
Proof.
  intros A c s P1.
  destruct (cp_elim _ _ _ P1) as [a [b [P2 [P3 P4]]]].
  exists a.
  split.
  + apply P2.
  + rewrite (in_singleton_equal _ _ P3).
    apply P4.
Qed.

Lemma const_is_function: forall A c, function (const A c).
Proof.
  intros A c.
  split.
  + intros x P1.
    destruct (const_elim _ _ _ P1) as [a [P2 P3]].
    exists a.
    exists c.
    apply P3.
  + intros a b1 b2 [P1 P2].
    destruct (const_elim _ _ _ P1) as [a1 [_ P3]].
    destruct (const_elim _ _ _ P2) as [a2 [_ P4]].
    destruct (opair_equal_elim _ _ _ _ P3) as [_ P5].
    rewrite P5.
    destruct (opair_equal_elim _ _ _ _ P4) as [_ P6].
    symmetry.
    apply P6.
Qed.

Lemma const_domain: forall A c, A = dom(const A c).
Proof.
  intros A c.
  apply ax_exten.
  intros x.
  split.
  + intros P1.
    apply domain_intro.
    exists c.
    apply (const_intro _ _ _ P1).
  + intros P1.
    destruct (domain_elim _ _ P1) as [a P2].
    destruct (const_elim _ _ _ P2) as [b [P3 P4]].
    destruct (opair_equal_elim _ _ _ _ P4) as [P5 _].
    rewrite P5.
    apply P3.
Qed.

Lemma const_range: forall A c, A <> ∅ -> {c} = ran(const A c).
  intros A c P1.
  apply ax_exten.
  intros x.
  split.
  + intros P2.
    apply range_intro.
    destruct (not_empty_exist_elmn _ P1) as [a P3].
    exists a.
    rewrite (in_singleton_equal _ _ P2).
    apply (const_intro _ _ _ P3).
  + intros P2.
    destruct (range_elim _ _ P2) as [a P3].
    destruct (const_elim _ _ _ P3) as [b [_ P4]].
    destruct (opair_equal_elim _ _ _ _ P4) as [_ P5].
    rewrite P5.
    apply in_singleton.
Qed.

Lemma const_basic: forall A c x, x ∈ A -> c = fun_val (const A c) x.
Proof. 
  intros A c x P1.
  apply fun_val_intro.
  + apply const_is_function.
  + rewrite <- (const_domain A c).
    apply P1.
  + apply (const_intro _ _ _ P1).
Qed.

Lemma union2_relation: forall F G, relation F -> relation G -> relation (F ∪ G).
Proof.
  intros F G P1 P2 r P3.
  destruct (in_union2_in _ _ _ P3) as [P4|P4].
  + apply (P1 r P4).
  + apply (P2 r P4).
Qed.

Lemma union_relation: forall F, (forall f, f ∈ F -> relation f) -> relation (∪(F)).
Proof.
  intros F P1 r P2.
  destruct (in_union_in _ _ P2) as [s [P3 P4]].
  apply (P1 s P3 r P4).
Qed.

Lemma piecewise_function: forall F G, function F -> function G ->
  (dom(F) ∩ dom(G)) = ∅ -> function (F ∪ G).
Proof.
  intros F G [P1 P3] [P2 P4] P5.
  split.
  + apply (union2_relation F G P1 P2).
  + intros a b1 b2 [P6 P7].
    destruct (in_union2_in F G (⟨a, b1⟩) P6) as [P8|P8].
    - destruct (in_union2_in F G (⟨a, b2⟩) P7) as [P9|P9].
      * apply (P3 a b1 b2 (conj P8 P9)).
      * absurd (a ∈ (dom(F) ∩ dom(G))).
        { rewrite P5. 
          apply (not_in_empty). }
        { apply (in_in_inter2).
          + apply domain_intro.
            exists b1.
            apply P8.
          + apply domain_intro.
            exists b2.
            apply P9. }
    - destruct (in_union2_in F G (⟨a, b2⟩) P7) as [P9|P9].
      * absurd (a ∈ (dom(F) ∩ dom(G))).
        { rewrite P5. 
          apply (not_in_empty). }
        { apply (in_in_inter2).
          + apply domain_intro.
            exists b2.
            apply P9.
          + apply domain_intro.
            exists b1.
            apply P8. }
      * apply (P4 a b1 b2 (conj P8 P9)).
Qed.

Lemma union2_domain: forall F G, dom(F ∪ G) = dom(F) ∪ dom(G).
Proof.
  intros F G.
  apply ax_exten.
  intros x.
  split.
  + intros P1.
    destruct (domain_elim _ _ P1) as [f P2].
    destruct (in_union2_in _ _ _ P2) as [P3|P3].
    - apply in_in_union2_1.
      apply domain_intro.
      exists f.
      apply P3.
    - apply in_in_union2_2.
      apply domain_intro.
      exists f.
      apply P3.
  + intros P1.
    apply domain_intro.
    destruct (in_union2_in _ _ _ P1) as [P2|P2].
    - destruct (domain_elim _ _ P2) as [f P3]. 
      exists f.
      apply (in_in_union2_1).
      apply P3.
    - destruct (domain_elim _ _ P2) as [f P3]. 
      exists f.
      apply (in_in_union2_2).
      apply P3.
Qed.

Lemma union2_range: forall F G, ran(F ∪ G) = ran(F) ∪ ran(G).
Proof.
  intros F G.
  apply ax_exten.
  intros x.
  split.
  + intros P1.
    destruct (range_elim _ _ P1) as [f P2].
    destruct (in_union2_in _ _ _ P2) as [P3|P3].
    - apply in_in_union2_1.
      apply range_intro.
      exists f.
      apply P3.
    - apply in_in_union2_2.
      apply range_intro.
      exists f.
      apply P3.
  + intros P1.
    apply range_intro.
    destruct (in_union2_in _ _ _ P1) as [P2|P2].
    - destruct (range_elim _ _ P2) as [f P3]. 
      exists f.
      apply (in_in_union2_1).
      apply P3.
    - destruct (range_elim _ _ P2) as [f P3]. 
      exists f.
      apply (in_in_union2_2).
      apply P3.
Qed.
    
Lemma union_fun_equal: forall f H x, f ∈ H -> function f -> function (∪(H)) -> 
  x ∈ dom(f) -> fun_val f x = fun_val (∪(H)) x.
Proof. 
  intros f H x P1 P2 P3 P4.
  destruct (domain_elim _ _ P4) as [y P5].
  rewrite <- (fun_val_intro _ _ _ P2 P4 P5).
  apply fun_val_intro.
  + apply P3.
  + apply domain_intro.
    exists y.
    apply in_in_union.
    exists f.
    split.
    - apply P1.
    - apply P5.
  + apply in_in_union.
    exists f.
    split.
    - apply P1.
    - apply P5.
Qed.

Lemma union2_fun_equal_1: forall F G x, function F -> function G -> function (F ∪ G) -> 
  x ∈ dom(F) -> fun_val F x = fun_val (F ∪ G) x.
Proof. 
  intros F G x P1 P2 P3 P4.
  destruct (domain_elim _ _ P4) as [y P5].
  rewrite <- (fun_val_intro _ _ _ P1 P4 P5).
  apply fun_val_intro.
  + apply P3.
  + apply domain_intro.
    exists y.
    apply in_in_union2_1.
    apply P5.
  + apply in_in_union2_1.
    apply P5.
Qed.

Lemma union2_fun_equal_2: forall F G x, function F -> function G -> function (F ∪ G) -> 
  x ∈ dom(G) -> fun_val G x = fun_val (F ∪ G) x.
Proof. 
  intros F G x P1 P2 P3 P4.
  rewrite union2_sym.
  rewrite union2_sym in P3.
  apply (union2_fun_equal_1 G F x P2 P1 P3 P4).
Qed.

(* 3J *)
Lemma left_inverse: forall F A B, A <> ∅ -> fun_maps F A B -> 
  ((exists G, fun_maps G B A /\ (id A = composition F G)) <-> one_to_one F).
Proof.
  intros F A B P1 [P2 [P3 P4]].
  split.
  + intros [G [[[_ P5] _] P6]].
    split.
    - apply P2.
    - intros a1 a2 n [P7 P8].
      apply (P5 n).
      split.
      * assert (a1 ∈ A) as P9.
        { rewrite <- P3.
          apply (domain_intro).
          exists n.
          apply P7. }
        pose (id_intro A a1 P9) as P10.
        rewrite P6 in P10.
        destruct (composition_elim _ _ _ _ P10) as [m [P11 P12]].
        destruct P2 as [_ P2].
        rewrite (P2 _ _ _ (conj P7 P11)).
        apply P12.
      * assert (a2 ∈ A) as P9.
        { rewrite <- P3.
          apply (domain_intro).
          exists n.
          apply P8. }
        pose (id_intro A a2 P9) as P10.
        rewrite P6 in P10.
        destruct (composition_elim _ _ _ _ P10) as [m [P11 P12]].
        destruct P2 as [_ P2].
        rewrite (P2 _ _ _ (conj P8 P11)).
        apply P12.
  + intros [P5 P6].
    destruct (not_empty_exist_elmn _ P1) as [a P7].
    destruct (LEM (ran(F) = B)) as [PB|PB].
    {
    exists (inverse F).
    split. split.
    - destruct (inverse_function F) as [P8 _].
      apply (P8 P6).
    - split.
      * rewrite (inverse_domain).
        apply PB.
      * rewrite (inverse_range).
        apply (eq_subset_1 _ _ P3).
    - apply ax_exten.
      intros x.
      split.
      * intros P8.
        destruct (id_elim _ _ P8) as [s [P9 P10]].
        rewrite P10.
        apply composition_intro.
        exists (fun_val F s).
        split.
        { rewrite <- P3 in P9. 
          apply (fun_val_basic _ _ P5 P9). }
        { apply inverse_intro.
          rewrite <- P3 in P9. 
          apply (fun_val_basic _ _ P5 P9). }
      * intros P8.
        destruct (composition_is_relation _ _ x P8) as [b1 [b2 P9]].
        rewrite P9 in P8.
        destruct (composition_elim _ _ _ _ P8) as [y [P10 P11]].
        rewrite P9.
        rewrite <- (P6 _ _ _ (conj P10 (inverse_elim _ _ _ P11))).
        apply id_intro.
        rewrite <- P3.
        apply domain_intro.
        exists y.
        apply P10.
    }
    {
    exists ((inverse F) ∪ (const (complement B (ran(F))) a)).
    split. split.
    - apply piecewise_function.
      * destruct (inverse_function F) as [P8 _].
        apply (P8 P6).
      * apply const_is_function.
      * rewrite (inverse_domain).
        rewrite <- (const_domain _ a).
        apply complement_inter2.
    - split.
      * rewrite union2_domain. 
        rewrite inverse_domain. 
        rewrite <- (const_domain _ a). 
        rewrite complement_union2.
        apply ax_exten.
        intros x.
        split.
        { intros P8.
          destruct (in_union2_in _ _ _ P8) as [P9|P9].
          + apply (P4 x P9).
          + apply P9. }
        { intros P8.
          apply in_in_union2_2.
          apply P8. }
      * rewrite union2_range. 
        intros x P8.
        destruct (in_union2_in _ _ _ P8) as [P9|P9].
        { rewrite (inverse_range F) in P9.
          rewrite P3 in P9.
          apply P9. }
        { rewrite <- (const_range _ a) in P9.
          + rewrite <- (in_singleton_equal _ _ P9).
            apply P7. 
          + intros P10.
            absurd (ran(F) = B).
            - apply PB. 
            - destruct (complement_proper_subset _ _ P4 PB) as [s P11]. 
              rewrite P10 in P11.
              absurd (s ∈ ∅).
              * apply not_in_empty.
              * apply P11. }
    - apply ax_exten.
      intros x.
      split.
      * intros P8.
        destruct (id_elim _ _ P8) as [s [P9 P10]].
        rewrite P10.
        apply composition_intro.
        exists (fun_val F s).
        split.
        { rewrite <- P3 in P9. 
          apply (fun_val_basic _ _ P2 P9). }
        { apply in_in_union2_1.
          apply inverse_intro.
          rewrite <- P3 in P9. 
          apply (fun_val_basic _ _ P2 P9). }
      * intros P8.
        destruct (composition_is_relation _ _ x P8) as [x1 [x2 P9]].
        rewrite P9 in P8.
        destruct (composition_elim _ _ _ _ P8) as [y [P10 P11]].
        destruct (in_union2_in _ _ _ P11) as [P12|P12].
        { rewrite P9.
          rewrite <- (P6 x1 x2 y (conj P10 (inverse_elim _ _ _ P12))).
          apply id_intro.
          rewrite <- P3.
          apply domain_intro.
          exists y.
          apply P10. }
        { absurd (y ∈ ran(F)).
          { apply (complement_elim B (ran(F)) y). 
            destruct (const_elim _ _ _ P12) as [s [P13 P14]].
            destruct (opair_equal_elim _ _ _ _ P14) as [P15 _].
            rewrite P15.
            apply P13. }
          { apply range_intro.
            exists x1.
            apply P10. } }
    }
Qed.

(*
Axiom ax_choice: forall S, (forall a, a ∈ S -> a <> ∅) ->
  (forall a b, a ∈ S -> b ∈ S -> a <> b -> a ∩ b = ∅) ->
  exists C, forall a, a ∈ S -> exists x, C ∩ a = {x}.
Theorem choice_fun_exists: forall A, exists F, 
  forall B, B <> ∅ -> B ⊆ A -> fun_val F B ∈ B
  /\ fun_maps F (complement (𝒫(A)) ({∅})) A.
Proof.
  intros A.
  pose (subset_ctor (fun S => exists a, a <> ∅  /\ a ⊆ A /\
    (ran(S) = a) /\ (forall s, s ∈ S -> exists y, s = ⟨a, y⟩)) 
    (𝒫(cp (𝒫(A)) A))) as B.
  assert (forall b, b ∈ B -> b <> ∅) as P1.
  { intros b P1.
    destruct (subset_elim _ _ _ P1) as [_ [a [P2 [_ [P3 _]]]]].
    destruct (not_empty_exist_elmn _ P2) as [x P4].
    rewrite <- P3 in P4.
    destruct (range_elim _ _ P4) as [y P5].
    apply exist_elmn_not_empty.
    exists (⟨y, x⟩).
    apply P5. }
  assert (forall b1 b2, b1 ∈ B -> b2 ∈ B -> b1 <> b2 -> b1 ∩ b2 = ∅) as P2.
  { intros b1 b2 P2 P3 P4.
    apply empty_unique.
    intros x P5.
    absurd (b1 = b2).
    + apply P4.
    + destruct (in_inter2_in _ _ _ P5) as [Q1 R1].
      destruct (subset_elim _ _ _ P2) as [_  [a1 [Q2 [Q3 [Q4 Q5]]]]].
      destruct (Q5 _ Q1) as [y1 Q6].
      destruct (subset_elim _ _ _ P3) as [_  [a2 [R2 [R3 [R4 R5]]]]].
      destruct (R5 _ R1) as [y2 R6].
      assert (a1 = a2) as P6.
      { rewrite Q6 in R6.
        destruct (opair_equal_elim _ _ _ _ R6) as [P6 _].
        apply P6. }
      apply ax_exten.
      intros s.
      split.
      - intros P7.
        destruct (Q5 _ P7) as [yy P8].
        rewrite P6 in P8.
        rewrite P8 in P7.
        pose (range_intro _ _ (in_range_intro _ _ _ P7)) as P9.
        rewrite Q4 in P9.
        rewrite P6 in P9.
        rewrite <- R4 in P9.
        destruct (range_elim _ _ P9) as [xx P10].
        destruct (R5 _ P10) as [yyy P11].
        rewrite (opair_equal_elim_1 _ _ _ _ P11) in P10.
        rewrite <- P8 in P10.
        apply P10.
      - intros P7.
        destruct (R5 _ P7) as [yy P8].
        rewrite <- P6 in P8.
        rewrite P8 in P7.
        pose (range_intro _ _ (in_range_intro _ _ _ P7)) as P9.
        rewrite R4 in P9.
        rewrite <- P6 in P9.
        rewrite <- Q4 in P9.
        destruct (range_elim _ _ P9) as [xx P10].
        destruct (Q5 _ P10) as [yyy P11].
        rewrite (opair_equal_elim_1 _ _ _ _ P11) in P10.
        rewrite <- P8 in P10.
        apply P10. }
  destruct (ax_choice _ P1 P2) as [C P3].
  pose (F := (∪(B)) ∩ C).
  exists F.
  split. 
  assert (fun_maps F (complement (𝒫( A)) ({∅})) A) as P4. {
  split. split.
  { intros x Q1.
    destruct (in_inter2_in _ _ _ Q1) as [Q2 _].
    destruct (in_union_in _ _ Q2) as [b [Q3 Q4]].
    destruct (subset_elim _ _ _ Q3) as [Q5 _].
    destruct (cp_elim _ _ _ (in_power_subset _ _ Q5 _ Q4)) as [aa [bb [_ [_ Q6]]]].
    exists aa.
    exists bb.
    apply Q6. }
  { intros a b1 b2 [Q1 Q2].
    admit. }
  split.
  { apply ax_exten.
    intros x.
    split.
    + intros Q1.
      destruct (domain_elim _ _ Q1) as [y Q2].
      destruct (in_inter2_in _ _ _ Q2) as [Q3 Q4].
      destruct (in_union_in _ _ Q3) as [b [Q5 Q6]].
      destruct (subset_elim _ _ _ Q5) as [Q7 _].
      apply complement_intro.
      split.
      - destruct (cp_elim _ _ _ (in_power_subset _ _ Q7 _ Q6)) as
          [xx [yy [Q8 [_ Q9]]]].
        rewrite (opair_equal_elim_1 _ _ _ _ Q9).
        apply Q8.
      - intros Q8. 
        destruct (subset_elim _ _ _ Q5) as [_ [a [Q10 [_[ _ Q11]]]]].
        absurd (a = ∅).
        * apply Q10.
        * destruct (Q11 _ Q6) as [yy Q12].
          rewrite <- (opair_equal_elim_1 _ _ _ _ Q12).
          symmetry.
          apply (in_singleton_equal _ _ Q8). }
  { intros x Q1.
    destruct (range_elim _ _ Q1) as [y Q2].
    destruct (in_inter2_in _ _ _ Q2) as [Q3 _].
    destruct (in_union_in _ _ Q3) as [b [Q4 Q5]].
    destruct (subset_elim _ _ _ Q4) as [_ [a [_ [Q6 [Q7 _]]]]].
    pose (range_intro _ _ (in_range_intro _ _ _ Q5)) as Q8.
    rewrite Q7 in Q8.
    apply (Q6 _ Q8). } }
  { destruct P4 as [P4 _].  
    pose(fun_val_intro). intros b Q1 Q2.

  pose (subset_ctor (fun s => exists x y, s = ⟨x, y⟩ /\ y ∈ x) (cp (𝒫(A)) A)) as B.
  pose (subset_ctor (fun s => exists x y, s = ⟨x, y⟩ /\ y ∈ x) (cp (𝒫(A)) A)) as B.
  pose (subset_ctor (fun s => exists x, 
    (forall e, e ∈ s -> exists y, e = ⟨x, y⟩) /\
    (forall e, e ∈ B -> (exists y, e = ⟨x, y⟩) -> e ∈ s))
    (𝒫(B))) as C.
  assert (forall a, a ∈ C -> a <> ∅) as P1.
  { intros a P1 P2.
    destruct (subset_elim _ _ _ P1) as [P3 [x P4]].
    destruct (in_power_ _ _ P3).
    apply P2. }
  assert (forall a b, a ∈ C -> b ∈ C -> a <> b -> a ∩ b = ∅) as P2.
  { intros a b P2 P3 P4.
    apply empty_unique.
    intros x P5.
    absurd (a = b).
    + apply P4.
    + destruct (in_inter2_in _ _ _ P5) as [P6 P7].
      destruct (subset_elim _ _ _ P2) as [P8  [_ [aa [P9  P10]]]].
      destruct (subset_elim _ _ _ P3) as [P11 [_ [bb [P12 P13]]]].
      destruct (P9  _ P6) as  [aaa P14].
      destruct (P12 _ P7) as [bbb P15].
      rewrite P15 in P14.
      destruct (opair_equal_elim _ _ _ _ P14) as [P16 P17].
      apply ax_exten.
      intros xx.
      split.
      - intros P18.
        apply P13.
        * apply (in_power_subset _ _ P8 _ P18).
        * rewrite P16.
          apply (P9 _ P18).
      - intros P18.
        apply P10.
        * apply (in_power_subset _ _ P11 _ P18).
        * rewrite <- P16.
          apply (P12 _ P18). }
  destruct (ax_choice _ P1 P2) as [D P3].
  pose (F := (∪(C)) ∩ D).
  exists F.
  split. split. split.
  { intros x P4.
    destruct (in_inter2_in _ _ _ P4) as [P5 _].
    destruct (in_union_in _ _ P5) as [c [P6 P7]].
    destruct (subset_elim _ _ _ P6) as [_ [_ [aa [P8 _]]]].
    destruct (P8 _ P7) as [bb P9].
    exists aa.
    exists bb.
    apply P9. }
  { intros a b1 b2 [P4 P5].
    destruct (in_inter2_in _ _ _ P4) as [Q1 Q2].
    destruct (in_union_in _ _ Q1) as [c1 [Q3 Q4]].
    pose (P3 _ Q3).
    admit. }
  split.
  { apply ax_exten.
    intros x.
    split.
    + intros Q1.
      destruct (domain_elim _ _ Q1) as [a Q2].
      destruct (in_inter2_in _ _ _ Q2) as [Q3 _].
      destruct (in_union_in _ _ Q3) as [c [Q4 Q5]].
      destruct (subset_elim _ _ _ Q4) as [Q6 [Q7 _]].
      apply complement_intro.
      split.
      - pose (in_power_subset _ _ Q6 _ Q5) as Q8.
        destruct (subset_elim _ _ _ Q8) as [Q9 _].
        destruct (cp_elim _ _ _ Q9) as [y [z [Q10 [_ Q11]]]].
        destruct (opair_equal_elim _ _ _ _ Q11) as [Q12 _].
        rewrite Q12.
        apply Q10.
      - intros Q8.
       
*)

Lemma right_inverse: forall F A B, A <> ∅ -> fun_maps F A B -> 
  ((exists H, fun_maps H B A /\ (id B = composition H F)) <-> onto F A B).
Proof.
  intros F A B P1 [P2 [P3 P4]].
  split.
  + intros [H [[[_ P5] _] P6]].
    - split.
      * apply P3. 
      * apply subset_asym.
      split. 
      { apply P4. }
      { intros x P7.
        pose (id_intro _ _ P7) as P8.
        rewrite P6 in P8.
        destruct (composition_elim _ _ _ _ P8) as [y [_ P9]].
        apply (range_intro _ _ (in_range_intro _ _ _ P9)). }
  + intros [P7 P8].
    destruct (ax_choice _ (inverse_is_relation F)) as [H [P9 [P10 P11]]].
    exists H.
    split. split.
    - apply P9.
    - split.
      * rewrite P11.
        rewrite (inverse_domain F).
        apply P8.
      * rewrite <- P3.
        rewrite <- inverse_range.
        apply (subset_range _ _ P10).
    - apply ax_exten.
      intros x.
      split.
      * intros P12.
        destruct (id_elim _ _ P12) as [y [P13 P14]].
        rewrite P14.
        apply composition_intro.
        exists (fun_val H y).
        split.
        { apply (fun_val_basic _ _ P9).
          rewrite P11.
          rewrite inverse_domain.
          rewrite P8.
          apply P13. }
        { apply inverse_elim.
          apply P10.
          apply (fun_val_basic _ _ P9).
          rewrite P11.
          rewrite inverse_domain.
          rewrite P8.
          apply P13. }
      * intros P12.
        destruct (composition_is_relation H F x P12) as [a [b P13]].
        rewrite P13 in P12.
        destruct (composition_elim _ _ _ _ P12) as [c [P14 P15]].
        destruct P2 as [_ P2].
        rewrite (P2 c a b (conj (inverse_elim _ _ _ (P10 _ P14)) P15)) in P13.
        rewrite P13.
        apply id_intro.
        apply P4.
        apply range_intro.
        exists c.
        apply P15.
Qed.
      
(* 3K *)
Lemma image_union2: forall F A B, image F (A ∪ B) = (image F A) ∪ (image F B).
Proof.
  intros F A B.
  apply ax_exten.
  intros y.
  split.
  + intros P1.
    destruct (image_elim _ _ _ P1) as [x [P2 P3]].
    destruct (in_union2_in _ _ _ P3) as [P4|P4].
    - apply in_in_union2_1.
      apply image_intro.
      exists x.
      apply (conj P2 P4).
    - apply in_in_union2_2.
      apply image_intro.
      exists x.
      apply (conj P2 P4).
  + intros P2.
    apply image_intro.
    destruct (in_union2_in _ _ _ P2) as [P3|P3].
    - destruct (image_elim _ _ _ P3) as [x [P4 P5]].
      exists x.
      split.
      * apply P4.
      * apply in_in_union2_1.
        apply P5.
    - destruct (image_elim _ _ _ P3) as [x [P4 P5]].
      exists x.
      split.
      * apply P4.
      * apply in_in_union2_2.
        apply P5.
Qed.

Lemma image_inter2: forall F A B, image F (A ∩ B) ⊆ (image F A) ∩ (image F B).
Proof.
  intros F A B y P1.
  destruct (image_elim _ _ _ P1) as [x [P2 P3]].
  destruct (in_inter2_in _ _ _ P3) as [P4 P5].
  apply in_in_inter2.
  + apply image_intro.
    exists x.
    apply (conj P2 P4).
  + apply image_intro.
    exists x.
    apply (conj P2 P5).
Qed.

Lemma image_complement: forall F A B, complement (image F A) (image F B) ⊆ image F (complement A B).
Proof.
  intros F A B y P1.
  destruct (complement_elim _ _ _ P1) as [P2 P3].
  apply image_intro.
  destruct (image_elim _ _ _ P2) as [x [P4 P5]].
  exists x.
  split.
  + apply P4.
  + apply complement_intro.
    split.
    - apply P5.
    - intros P6.
      absurd (y ∈ image F B).
      * apply P3.
      * apply image_intro.
        exists x.
        apply (conj P4 P6).
Qed.
   
Definition fun_space (A: set) (B: set) :=
  (subset_ctor (fun s => fun_maps s A B) (𝒫(cp A B))).

Lemma fun_space_superset: forall F A B, fun_maps F A B -> F ∈ 𝒫(cp A B).
Proof.
  intros F A B [[P1 _] [P2 P3]].
  apply subset_in_power.
  intros x P4.
  destruct (P1 x P4) as [a [b P5]].
  rewrite P5 in P4.
  rewrite P5.
  apply cp_intro.
  + rewrite <- P2.
    apply (domain_intro _ _ (in_domain_intro _ _ _ P4)).
  + apply P3.
    apply (range_intro _ _ (in_range_intro _ _ _ P4)).
Qed.

Lemma fun_space_intro: forall F A B, fun_maps F A B -> F ∈ fun_space A B.
Proof.
  intros F A B P1.
  destruct ((extract_set_property 
    (ax_subset (fun s => fun_maps s A B) (𝒫(cp A B)))) F) as [_ P2].
  apply P2.
  split.
  + apply (fun_space_superset _ _ _ P1).
  + apply P1.
Qed.

Lemma fun_space_elim: forall F A B, F ∈ fun_space A B -> fun_maps F A B.
Proof.
  intros F A B P1.
  destruct ((extract_set_property 
    (ax_subset (fun s => fun_maps s A B) (𝒫(cp A B)))) F) as [P2 _].
  apply P2.
  apply P1.
Qed.

(* TODO classify different difition *)
(* TODO intro and elim fun *)
