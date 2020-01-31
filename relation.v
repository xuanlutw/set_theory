Require Import logic.
Require Import axiom.
Require Import basic.

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

(* Relation *)
Definition rel (R: set) :=
  forall r, r ∈ R -> exists a b, r = ⟨a, b⟩.

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

(* Filed *)
Definition filed (R:set) :=
  dom R ∪ran R.

Notation "fld( A )" := (filed A) (at level 60, no associativity).

(* Function *)
Definition single_value (R: set) :=
  forall a b1 b2, ⟨a, b1⟩ ∈ R -> ⟨a, b2⟩ ∈ R -> b1 = b2.

Definition single_rooted (R: set) :=
  forall a1 a2 b, ⟨a1, b⟩ ∈ R -> ⟨a2, b⟩ ∈ R -> a1 = a2.

Definition function (F: set) :=
  rel F /\ single_value F.

Definition fover (F: set) (A: set) (B: set) :=
  (function F) /\ (dom(F) = A) /\ (ran(F) ⊆ B).

Definition fonto (F: set) (A: set) (B: set) :=
  (function F) /\ (dom(F) = A) /\ (ran(F) = B).

Definition injection (F: set) :=
  function F /\ single_rooted F.

Theorem fonto_fover: forall F A B, fonto F A B -> fover F A B.
Proof. 
  intros F A B [P1 [P2 P3]].
  split.
  + apply P1.
  + split. 
    - apply P2.
    - rewrite P3.
      apply subset_refl.
Qed.

Lemma fonto_intro: forall F, function F -> fonto F (dom(F)) (ran(F)).
Proof.
  intros F P1.
  split.
  + apply P1.
  + split.
    - reflexivity.
    - reflexivity.
Qed.

(* Function Value *)
Theorem fval_exist: forall F x, exists y, function F -> x ∈ dom(F) -> 
  (⟨x, y⟩ ∈ F /\ (forall z, ⟨x, z⟩ ∈ F -> y = z)).
Proof.
  intros F x.
  destruct (LEM (x ∈ dom(F))) as [P1|P1].
  + destruct (dom_elim _ _ P1) as [y P2].
    exists y.
    intros P3 P4.
    split.
    - apply P2.
    - intros z P5.
      destruct P3 as [_ P3].
      apply (P3 x y z P2 P5).
  + exists x.
    intros _ P2.
    contradiction.
Qed.

Definition fval (F:set) (x:set) :=
  extract_set (fval_exist F x).

Notation "F [ x ]" := (fval F x) (at level 60).

Lemma fval_elim: forall F x y, y = F[x] -> function F -> x ∈ dom(F) ->
  (⟨x, y⟩ ∈ F /\ (forall y2, ⟨x, y2⟩ ∈ F -> y = y2)).
Proof.
  intros F x y P1.
  rewrite P1.
  apply (extract_set_property (fval_exist F x)).
Qed.

Lemma fval_elim_1: forall F x y, y = F[x] -> function F -> x ∈ dom(F) ->
  (⟨x, y⟩ ∈ F).
Proof.
  intros F x y P1 P2 P3.
  destruct (fval_elim F x y P1 P2 P3) as [P4 _].
  apply P4.
Qed.

Lemma fval_elim_2: forall F x y, y = F[x] -> function F -> x ∈ dom(F) ->
  (forall y2, ⟨x, y2⟩ ∈ F -> y = y2).
Proof.
  intros F x y P1 P2 P3.
  destruct (fval_elim F x y P1 P2 P3) as [_ P4].
  apply P4.
Qed.

Theorem fval_intro: forall F x y, function F -> x ∈ dom(F) -> ⟨x, y⟩ ∈ F -> 
  y = F[x].
Proof.
  intros F x y P1 P2 P3.
  destruct (extract_set_property (fval_exist F x) P1 P2) as [_ P4].
  rewrite <- (P4 y P3). 
  reflexivity.
Qed.

Lemma fval_intro_2: forall F x, function F -> x ∈ dom(F) -> ⟨x, F[x]⟩ ∈ F.
Proof.
  intros F x P1 P2.
  destruct (extract_set_property (fval_exist F x) P1 P2) as [P3 _].
  apply P3.
Qed.

Lemma fval_intro_fover: forall F A B x, fover F A B -> x ∈ A -> ⟨x, F[x]⟩ ∈ F.
Proof. 
  intros F A B x [P1 [P2 _]] P3.
  rewrite <- P2 in P3.
  apply (fval_intro_2 _ _ P1 P3).
Qed.

Lemma fval_intro_fonto: forall F A B x, fonto F A B -> x ∈ A -> ⟨x, F[x]⟩ ∈ F.
Proof.
  intros F A B x P1 P2.
  apply (fval_intro_fover F A B x (fonto_fover F A B P1) P2).
Qed.

Lemma fval_ran: forall F x, function F -> x ∈ dom(F) -> F[x] ∈ ran(F).
Proof.
  intros F x P1 P2.
  apply ran_intro.
  exists x.
  apply (fval_intro_2 F x P1 P2).
Qed.

Lemma fval_ran_fover: forall F A B x, fover F A B -> x ∈ A -> F[x] ∈ B.
Proof.
  intros F A B x [P1 [P2 P3]] P4.
  rewrite <- P2 in P4.
  apply (P3 _ (fval_ran _ _ P1 P4)).
Qed.

Lemma fval_ran_fonto: forall F A B x, fonto F A B -> x ∈ A -> F[x] ∈ B.
Proof.
  intros F A B x P1 P2.
  apply (fval_ran_fover F A B x (fonto_fover F A B P1) P2).
Qed.

(* Restriction *)
Definition in_restr (x: set) (F: set) (A: set) :=
  (exists a b, ⟨a, b⟩ ∈ F /\ x = ⟨a, b⟩ /\ a ∈ A).

Definition restr (F: set) (A: set) := 
  subset_ctor (fun x => (in_restr x F A)) F.

Notation "F ↾ A" := (restr F A) (at level 60, no associativity).

Theorem restr_intro: forall x y F A, ⟨x, y⟩ ∈ F -> x ∈ A -> 
  ⟨x, y⟩ ∈ F↾A.
Proof.
  intros x y F A P1 P2.
  destruct (extract_set_property 
    (ax_subset 
      (fun s => in_restr s F A) F) 
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

Lemma restr_elim: forall x y F A, ⟨x, y⟩ ∈ restr F A -> 
  ⟨x, y⟩ ∈ F /\ x ∈ A.
Proof.
  intros x y F A P1.
  destruct (extract_set_property 
    (ax_subset 
      (fun s => in_restr s F A) F) 
    (⟨x, y⟩)) as [P2 _].
  destruct (P2 P1) as [P3 [a [b [_ [P4 P5]]]]].
  split.
  + apply P3.
  + rewrite (opair_equal_elim_fst _ _ _ _ P4).
    apply P5.
Qed.

(* Image *)
Definition image (F: set) (A: set) := 
  ran(restr F A).

Notation "F [| A |]" := (image F A) (at level 60, no associativity).

Theorem image_intro: forall y F A, (exists x, ⟨x, y⟩ ∈ F /\ x ∈ A) -> y ∈ F[|A|].
Proof.
  intros y F A P1.
  destruct P1 as [x [P1 P2]].
  apply ran_intro.
  exists x.
  apply (restr_intro _ _ _ _ P1 P2).
Qed.

Lemma image_elim: forall y F A, y ∈ F[|A|] -> (exists x, ⟨x, y⟩ ∈ F /\ x ∈ A).
Proof.
  intros y F A P1.
  destruct (ran_elim _ _ P1) as [x P2].
  destruct (restr_elim _ _ _ _ P2) as [P3 P4].
  exists x.
  split.
  + apply P3.
  + apply P4.
Qed.

(* 3K *)
Lemma image_union2: forall F A B, F[|A ∪ B|] = F[|A|] ∪ F[|B|].
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

Lemma image_inter2: forall F A B, F[|A ∩ B|] ⊆ F[|A|] ∩ F[|B|].
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

Lemma image_complement: forall F A B, (F[|A|]) \ (F[|B|]) ⊆ F[|(A \ B)|].
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
      absurd (y ∈ F[|B|]).
      * apply P3.
      * apply image_intro.
        exists x.
        apply (conj P4 P6).
Qed.

(* Inverse *)
Definition in_inv (x: set) (R: set) :=
  (exists a b, ⟨a, b⟩ ∈ R /\ x = ⟨b, a⟩).

Definition inv (R: set) := 
  subset_ctor (fun x => (in_inv x R)) (cp (ran(R)) (dom(R))).

Theorem inv_superset: forall x R, in_inv x R -> x ∈ cp (ran(R)) (dom(R)).
Proof.
  intros x R P1.
  destruct P1 as [a [b [P1 P2]]].
  rewrite P2.
  apply cp_intro.
  + apply ran_intro.
    exists a.
    apply P1.
  + apply dom_intro.
    exists b.
    apply P1.
Qed.

Lemma inv_intro: forall x y R, ⟨x, y⟩ ∈ R -> ⟨y, x⟩ ∈ inv R.
Proof.
  intros x y R P1.
  destruct (extract_set_property 
    (ax_subset 
      (fun s => in_inv s R) 
      (cp (ran(R)) (dom(R)))) (⟨y, x⟩)) as [_ P2].
  apply P2.
  assert (in_inv (⟨y, x⟩) R) as P3.
  { exists x.
    exists y.
    split.
    + apply P1.
    + reflexivity. }
  split.
  + apply (inv_superset _ _ P3).
  + apply P3.
Qed.

Lemma inv_elim: forall x y R, ⟨x, y⟩ ∈ inv R -> ⟨y, x⟩ ∈ R.
Proof.
  intros x y R P1.
  destruct (extract_set_property 
    (ax_subset 
      (fun s => in_inv s R) 
      (cp (ran(R)) (dom(R)))) (⟨x, y⟩)) as [P2 _].
  destruct (P2 P1) as [_ [a [b [P3 P4]]]].
  rewrite (opair_equal_elim_fst _ _ _ _ P4).
  rewrite (opair_equal_elim_snd _ _ _ _ P4).
  apply P3.
Qed.

(* 3F *)
Theorem inv_dom: forall F, dom(inv F) = ran(F).
Proof.
  intros F.
  apply ax_exten.
  intros x.
  split.
  + intros P1.
    destruct (dom_elim _ _ P1) as [y P2].
    apply ran_intro.
    exists y.
    apply (inv_elim _ _ _ P2).
  + intros P1.
    destruct (ran_elim _ _ P1) as [y P2].
    apply dom_intro.
    exists y.
    apply (inv_intro _ _ _ P2).
Qed.
    
Theorem inv_ran: forall F, ran(inv F) = dom(F).
Proof.
  intros F.
  apply ax_exten.
  intros x.
  split.
  + intros P1.
    destruct (ran_elim _ _ P1) as [y P2].
    apply dom_intro.
    exists y.
    apply (inv_elim _ _ _ P2).
  + intros P1.
    destruct (dom_elim _ _ P1) as [y P2].
    apply ran_intro.
    exists y.
    apply (inv_intro _ _ _ P2).
Qed.

Theorem inv_is_rel: forall R, rel (inv R).
Proof.
  intros R x P1.
  destruct (extract_set_property 
    (ax_subset 
      (fun s => in_inv s R) 
      (cp (ran(R)) (dom(R)))) x) as [P2 _].
  destruct (P2 P1) as [_ [a [b [P3 P4]]]].
  exists b.
  exists a.
  apply P4.
Qed.

Theorem inv_inv: forall F, rel F -> inv (inv F) = F.
Proof.
  intros F P1.
  apply ax_exten.
  intros x.
  split.
  + intros P2.
    destruct ((inv_is_rel (inv F)) x P2) as [a [b P3]].
    rewrite P3.
    apply inv_elim.
    apply inv_elim.
    rewrite <- P3.
    apply P2.
  + intros P2.
    destruct (P1 x P2) as [a [b P3]].
    rewrite P3.
    apply inv_intro.
    apply inv_intro.
    rewrite <- P3.
    apply P2.
Qed.

(* 3F *)
Lemma inv_function: forall F, single_rooted F <-> function (inv F).
Proof.
  intros F.
  split.
  + intros P1.
    split.
    - intros x P2.
      destruct (inv_is_rel F x P2) as [a [b P3]].
      exists a.
      exists b.
      apply P3.
    - intros a b1 b2 P2 P3.
      apply (P1 b1 b2 a).
      * apply (inv_elim _ _ _ P2).
      * apply (inv_elim _ _ _ P3).
  + intros [_ P1] a1 a2 b P2 P3.
    apply (P1 b a1 a2).
    - apply (inv_intro _ _ _ P2).
    - apply (inv_intro _ _ _ P3).
Qed.

Lemma function_inv: forall F, rel F -> (function F <-> single_rooted(inv F)).
Proof.
  intros F P1.
  split.
  + intros [_ P2] a1 a2 b P3 P4.
    apply (P2 b a1 a2).
    - apply (inv_elim _ _ _ P3). 
    - apply (inv_elim _ _ _ P4).
  + intros P2.
    split.
    - apply P1.
    - intros a b1 b2 P3 P4.
      apply (P2 b1 b2 a).
      * apply (inv_intro _ _ _ P3).
      * apply (inv_intro _ _ _ P4).
Qed.

(* 3G *)
Lemma inv_function_exist_1: forall F, injection F -> 
  (forall x, x ∈ dom(F) -> (inv F)[F[x]] = x).
Proof.
  intros F [P1 P2] x P3.
  symmetry.
  apply fval_intro.
  + destruct (inv_function F) as [P4 _].
    apply (P4 P2).
  + rewrite inv_dom.
    apply ran_intro.
    exists x.
    apply (fval_intro_2 _ _ P1 P3).
  + apply inv_intro.
    apply (fval_intro_2 _ _ P1 P3).
Qed.

Lemma inv_function_exist_2: forall F, injection F -> 
  (forall x, x ∈ ran(F) -> F[(inv F)[x]] = x).
Proof.
  intros F [P1 P2] x P3.
  symmetry.
  apply fval_intro.
    apply P1.
  + apply dom_intro.
    exists x.
    apply inv_elim.
    destruct (inv_function F) as [P4 _].
    rewrite <- inv_dom in P3.
    apply (fval_intro_2 _ _ (P4 P2) P3).
  + apply inv_elim.
    destruct (inv_function F) as [P4 _].
    rewrite <- inv_dom in P3.
    apply (fval_intro_2 _ _ (P4 P2) P3).
Qed.

(* Composition *)
(* Only consider composition of two functions *)
Definition in_comp (x: set) (F: set) (G: set) :=
  (exists a b c, ⟨a, b⟩ ∈ F /\ ⟨b, c⟩ ∈ G /\ x = ⟨a, c⟩).

Definition comp (F: set) (G: set) := 
  subset_ctor (fun x => (in_comp x F G)) (cp (dom(F)) (ran(G))).

Notation "A ∘ B" := (comp B A) (at level 60, no associativity).

Theorem comp_superset: forall x F G, in_comp x F G -> 
  x ∈ cp (dom(F)) (ran(G)).
Proof.
  intros x F G P1.
  destruct P1 as [a [b [c [P1 [P2 P3]]]]].
  rewrite P3.
  apply cp_intro.
  + apply dom_intro.
    exists b.
    apply P1.
  + apply ran_intro.
    exists b.
    apply P2.
Qed.

Theorem comp_intro: forall x z F G, (exists y, ⟨x, y⟩ ∈ F /\ ⟨y, z⟩ ∈ G) -> 
  ⟨x, z⟩ ∈ G ∘ F.
Proof.
  intros x z F G P1.
  destruct P1 as [y [P1 P2]].
  destruct (extract_set_property 
    (ax_subset 
      (fun s => in_comp s F G) 
      (cp (dom(F)) (ran(G)))) (⟨x, z⟩)) as [_ P3].
  apply P3.
  assert (in_comp (⟨x, z⟩) F G) as P4.
  { exists x.
    exists y.
    exists z.
    split.
    + apply P1.
    + split. 
      - apply P2. 
      - reflexivity. }
  split.
  + apply (comp_superset _ _ _ P4).
  + apply P4.
Qed.

Lemma comp_elim: forall x z F G, ⟨x, z⟩ ∈ G ∘ F-> 
  (exists y, ⟨x, y⟩ ∈ F /\ ⟨y, z⟩ ∈ G).
Proof.
  intros x z F G P1.
  destruct (extract_set_property 
    (ax_subset 
      (fun s => in_comp s F G) 
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

Theorem comp_is_rel: forall F G, rel(G ∘ F).
Proof.
  intros F G r P1.
  destruct (extract_set_property 
    (ax_subset 
      (fun s => in_comp s F G) 
      (cp (dom(F)) (ran(G)))) r) as [P2 _].
  destruct (P2 P1) as [P3 _].
  destruct (cp_elim _ _ _ P3) as [a [b [_ [_ P4]]]].
  exists a.
  exists b.
  apply P4.
Qed.

Lemma comp_elim_2: forall s F G, s ∈ G ∘ F-> 
  (exists x y z, s = ⟨x, z⟩ /\ ⟨x, y⟩ ∈ F /\ ⟨y, z⟩ ∈ G).
Proof. 
  intros s F G P1.
  destruct (comp_is_rel _ _ _ P1) as [x [z P2]].
  rewrite P2 in P1.
  destruct (comp_elim _ _ _ _ P1) as [y P3].
  exists x.
  exists y.
  exists z.
  split.
  + apply P2. 
  + apply P3.
Qed.
  
(* 3H *)
Lemma comp_single_value: forall F G, single_value F -> single_value G ->
  single_value (G ∘ F).
Proof. 
  intros F G P1 P2 a b1 b2 P3 P4.
  destruct (comp_elim _ _ _ _ P3) as [e1 [P5 P6]].
  destruct (comp_elim _ _ _ _ P4) as [e2 [P7 P8]].
  rewrite (P1 _ _ _ P5 P7) in P6.
  apply (P2 _ _ _ P6 P8).
Qed.

Lemma comp_single_rooted: forall F G, single_rooted F -> single_rooted G ->
  single_rooted (G ∘ F).
Proof. 
  intros F G P1 P2 a1 a2 b P3 P4.
  destruct (comp_elim _ _ _ _ P3) as [e1 [P5 P6]].
  destruct (comp_elim _ _ _ _ P4) as [e2 [P7 P8]].
  rewrite (P2 _ _ _ P6 P8) in P5.
  apply (P1 _ _ _ P5 P7).
Qed.

Lemma comp_function: forall F G, function F -> function G ->
  function (G ∘ F).
Proof.
  intros F G [_ P1] [_ P2].
  split.
  + apply comp_is_rel.
  + apply (comp_single_value _ _ P1 P2).
Qed.

Lemma comp_injection: forall F G, injection F -> 
  injection G -> injection (G ∘ F).
Proof.
  intros F G P1 P2.
  split.
  + destruct P1 as [P1 _].
    destruct P2 as [P2 _].
    apply (comp_function _ _ P1 P2).
  + destruct P1 as [_ P1].
    destruct P2 as [_ P2].
    apply (comp_single_rooted _ _ P1 P2).
Qed.

Lemma comp_dom: forall F G, dom(G ∘ F) ⊆ dom(F). 
Proof.
  intros F G x P1.
  destruct (dom_elim _ _ P1) as [z P2].
  destruct (comp_elim _ _ _ _ P2) as [y [P3 _]].
  apply (dom_intro_2 _ _ y P3).
Qed.

Lemma comp_dom_elim: forall F G x, function F -> function G -> 
  x ∈ dom(G ∘ F) -> F[x] ∈ dom(G).
Proof.
  intros F G x P1 P2 P3.
  destruct (dom_elim _ _ P3) as [z P4].
  destruct (comp_elim _ _ _ _ P4) as [y [P5 P6]].
  apply dom_intro.
  exists z.
  assert (x ∈ dom(F)) as P7.
  { apply dom_intro.
    exists y.
    apply P5. }
  rewrite <- (fval_intro _ _ _ P1 P7 P5).
  apply P6.
Qed.

Lemma comp_ran: forall F G, ran(G ∘ F) ⊆ ran(G).
Proof.
  intros F G z P1.
  destruct (ran_elim _ _ P1) as [x P2].
  destruct (comp_elim _ _ _ _ P2) as [y [_ P3]].
  apply (ran_intro_2 _ y _ P3).
Qed.

Lemma comp_ran_2: forall F G, ran(G ∘ F) = G[|ran(F)|].
Proof.
  intros F G.
  apply subset_asym.
  split.
  + intros z P1.
    destruct (ran_elim _ _ P1) as [x P2].
    destruct (comp_elim _ _ _ _ P2) as [y [P3 P4]].
    apply image_intro.
    exists y.
    split.
    - apply P4.
    - apply (ran_intro_2 _ _ _ P3).
  + intros z P1.
    destruct (image_elim _ _ _ P1) as [y [P2 P3]].
    destruct (ran_elim _ _ P3) as [x P4].
    apply (ran_intro_2 _ x _).
    apply (comp_intro).
    exists y.
    apply (conj P4 P2).
Qed.

Lemma comp_elim_fval: forall F G x, function F -> function G -> x ∈ dom(G ∘ F) -> 
  G[F[x]] = (G ∘ F)[x].
Proof.
  intros F G x P1 P2 P3.
  apply (fval_intro _ _ _ (comp_function _ _ P1 P2) P3).
  apply (comp_intro).
  exists (F[x]).
  split.
  + apply (fval_intro_2 _ _ P1).
    apply (comp_dom _ _ _ P3).
  + apply (fval_intro_2 _ _ P2).
    apply (comp_dom_elim _ _ _ P1 P2 P3).
Qed.

Lemma comp_fonto: forall F G A B C, fonto F A B -> fonto G B C ->
  fonto (G ∘ F) A C.
Proof. 
  intros F G A B C Q1 Q2. 
  split. split. 
  + apply comp_is_rel.
  + destruct Q1 as [[_ P1] _]. 
    destruct Q2 as [[_ P2] _].
    apply (comp_single_value _ _ P1 P2).
  + split.
    - apply subset_asym. 
      split.
      * destruct Q1 as [_ [P1 _]].
        rewrite <- P1.
        apply comp_dom.
      * intros x P1.
        apply (dom_intro_2 _ _ (G[F[x]])).
        apply comp_intro.
        exists (F[x]).
        split.
        { apply (fval_intro_fonto F A B _ Q1 P1). }
        { apply (fval_intro_fonto G B C _ Q2).
          apply (fval_ran_fonto F A B _ Q1 P1). }
    - apply subset_asym.
      split.
      * destruct Q2 as [_ [_ P1]].
        rewrite <- P1.
        apply comp_ran.
      * intros z P1.
        destruct Q2 as [_ [P2 P3]].
        rewrite <- P3 in P1.
        destruct (ran_elim _ _ P1) as [y P4].
        pose (dom_intro_2 _ _ _ P4) as P5.
        destruct Q1 as [_ [P6 P7]].
        rewrite P2 in P5.
        rewrite <- P7 in P5.
        destruct (ran_elim _ _ P5) as [x P8].
        apply ran_intro.
        exists x.
        apply comp_intro.
        exists y.
        apply (conj P8 P4).
Qed.

(* 3I *)
Theorem comp_inv: forall F G, inv (G ∘ F) = (inv F) ∘ (inv G).
Proof.
  intros F G.
  apply ax_exten.
  intros r.
  split.
  + intros P1.
    destruct (inv_is_rel _ r P1) as [x [z P2]].
    rewrite P2.
    rewrite P2 in P1.
    apply comp_intro.
    destruct (comp_elim _ _ _ _ (inv_elim _ _ _ P1)) as [y [P3 P4]].
    exists y.
    split.
    - apply (inv_intro _ _ _ P4).
    - apply (inv_intro _ _ _ P3).
  + intros P1.
    destruct (comp_is_rel _ _ r P1) as [x [z P2]].
    rewrite P2.
    rewrite P2 in P1.
    apply inv_intro.
    apply comp_intro.
    destruct (comp_elim _ _ _ _ P1) as [y [P3 P4]] .
    exists y.
    split.
    - apply (inv_elim _ _ _ P4).
    - apply (inv_elim _ _ _ P3).
Qed.

(* Function Space *)
Definition fspace (A: set) (B: set) :=
  (subset_ctor (fun s => fover s A B) (𝒫(cp A B))).

Lemma fspace_superset: forall F A B, fover F A B -> F ∈ 𝒫(cp A B).
Proof.
  intros F A B [[P1 _] [P2 P3]].
  apply subset_in_power.
  intros x P4.
  destruct (P1 x P4) as [a [b P5]].
  rewrite P5 in P4.
  rewrite P5.
  apply cp_intro.
  + rewrite <- P2.
    apply (dom_intro _ _ (in_dom_intro _ _ _ P4)).
  + apply P3.
    apply (ran_intro _ _ (in_ran_intro _ _ _ P4)).
Qed.

Lemma fspace_intro: forall F A B, fover F A B -> (F ∈ (fspace A B)).
Proof.
  intros F A B P1.
  destruct ((extract_set_property 
    (ax_subset (fun s => fover s A B) (𝒫(cp A B)))) F) as [_ P2].
  apply P2.
  split.
  + apply (fspace_superset _ _ _ P1).
  + apply P1.
Qed.

Lemma fspace_elim: forall F A B, F ∈ fspace A B -> fover F A B.
Proof.
  intros F A B P1.
  destruct ((extract_set_property 
    (ax_subset (fun s => fover s A B) (𝒫(cp A B)))) F) as [P2 _].
  apply P2.
  apply P1.
Qed.

(* Empty Function *)
Lemma empty_is_rel: rel ∅.
Proof.
  intros x P1.
  absurd (x ∈ ∅).
  + apply not_in_empty.
  + apply P1.
Qed.

Lemma empty_is_single_value: single_value ∅.
Proof.
  intros a b1 b2 P1 P2.
  absurd (⟨a, b1⟩ ∈ ∅).
  + apply not_in_empty.
  + apply P1.
Qed.

Lemma empty_is_single_rooted: single_rooted ∅.
Proof.
  intros a1 a2 b P1 P2.
  absurd (⟨a1, b⟩ ∈ ∅).
  + apply not_in_empty.
  + apply P1.
Qed.

Lemma empty_is_function: function ∅.
Proof.
  split.
  + apply empty_is_rel.
  + apply empty_is_single_value.
Qed.

Lemma empty_is_injection: injection ∅.
Proof.
  split.
  + apply empty_is_function.
  + apply empty_is_single_rooted.
Qed.

Lemma empty_dom: dom(∅) = ∅.
Proof.
  apply subset_asym.
  split.
  + intros x P1.
    destruct (dom_elim _ _ P1) as [y P2].
    absurd (⟨x, y⟩ ∈ ∅).
    - apply not_in_empty.
    - apply P2.
  + intros x P1.
    absurd (x ∈ ∅).
    - apply not_in_empty.
    - apply P1.
Qed.

Lemma empty_ran: ran(∅) = ∅.
Proof.
  apply subset_asym.
  split.
  + intros y P1.
    destruct (ran_elim _ _ P1) as [x P2].
    absurd (⟨x, y⟩ ∈ ∅).
    - apply not_in_empty.
    - apply P2.
  + intros y P1.
    absurd (y ∈ ∅).
    - apply not_in_empty.
    - apply P1.
Qed.

Lemma fspace_empty_dom: forall B, fspace ∅ B = {∅}.
Proof.
  intros B.
  apply subset_asym.
  split.
  + intros x P1.
    assert (x = ∅) as P2.
    { apply empty_unique.
      intros s P2.
      destruct (fspace_elim _ _ _ P1) as [[P3 _] [P4 _]].
      destruct (P3 _ P2) as [p [q P5]].
      rewrite P5 in P2.
      absurd (dom(x) = ∅).
      + apply exist_elmn_not_empty.
        exists p.
        apply (dom_intro_2 _ _ _ P2).
      + apply P4. }
    rewrite P2.
    apply in_singleton.
  + intros x P1.
    apply fspace_intro.
    rewrite <- (in_singleton_equal _ _ P1).
    split.
    - apply empty_is_function.
    - split.
      * apply empty_dom.
      * rewrite empty_ran.
        apply empty_subset.
Qed.

Lemma fspace_empty_ran: forall A, A <> ∅ -> fspace A ∅ = ∅.
Proof.
  intros A P1.
  apply subset_asym.
  split.
  + intros x P2.
    destruct (fspace_elim _ _ _ P2) as [_ [P3 P4]].
    destruct (not_empty_exist_elmn _ P1) as [a P5].
    rewrite <- P3 in P5.
    destruct (dom_elim _ _ P5) as [b P7].
    absurd (b ∈ ∅).
    - apply not_in_empty.
    - apply (P4 _ (ran_intro_2 _ _ _ P7)).
  + intros x P2.
    absurd (x ∈ ∅).
    - apply not_in_empty.
    - apply P2.
Qed.

Lemma empty_dom_empty_ran: forall F, function F -> dom(F) = ∅ -> ran(F) = ∅.
Proof. 
  intros F P1 P2.
  pose (fonto_intro _ P1) as P3.
  rewrite P2 in P3.
  pose (fspace_intro _ _ _ (fonto_fover _ _ _ P3)) as P4.
  rewrite fspace_empty_dom in P4.
  rewrite <- (in_singleton_equal _ _ P4).
  apply empty_ran.
Qed.

(* Single Pair Function *)
Lemma single_pair_is_function: forall x y, function ({⟨x, y⟩}).
Proof.
  intros x y.
  split.
  + intros s P1.
    exists x.
    exists y.
    symmetry.
    apply (in_singleton_equal _ _ P1).
  + intros a0 b1 b2 P1 P2.
    destruct (opair_equal_elim _ _ _ _ (in_singleton_equal _ _ P1)) as [_ P3].
    rewrite <- P3.
    destruct (opair_equal_elim _ _ _ _ (in_singleton_equal _ _ P2)) as [_ P4].
    apply P4.
Qed.

Lemma single_pair_dom: forall x y, dom({⟨x, y⟩}) = ({x}).
Proof. 
  intros x y.
  apply ax_exten.
  intros s.
  split.
  + intros P1.
    destruct (dom_elim _ _ P1) as [t P2].
    rewrite (opair_equal_elim_fst _ _ _ _ (in_singleton_equal _ _ P2)).
    apply in_singleton.
  + intros P1.
    apply dom_intro.
    exists y.
    rewrite (in_singleton_equal _ _ P1).
    apply in_singleton.
Qed.

Lemma single_pair_ran: forall x y, ran({⟨x, y⟩}) = ({y}).
Proof. 
  intros x y.
  apply ax_exten.
  intros s.
  split.
  + intros P1.
    destruct (ran_elim _ _ P1) as [t P2].
    rewrite <- (opair_equal_elim_snd _ _ _ _ (in_singleton_equal _ _ P2)).
    apply in_singleton.
  + intros P1.
    apply ran_intro.
    exists x.
    rewrite (in_singleton_equal _ _ P1).
    apply in_singleton.
Qed.

(* Identify Function *)
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

Lemma id_is_rel: forall A, rel (id A).
Proof.
  intros A x P1.
  destruct (id_elim _ _ P1) as [s [_ P2]].
  exists s.
  exists s.
  apply P2.
Qed.

Lemma id_is_single_value: forall A, single_value (id A).
Proof.
  intros A a b1 b2 P1 P2.
  destruct (id_elim _ _ P1) as [s1 [_ P3]].
  destruct (id_elim _ _ P2) as [s2 [_ P4]].
  rewrite (opair_equal_elim_snd _ _ _ _ P3).
  rewrite <- (opair_equal_elim_fst _ _ _ _ P3).
  rewrite (opair_equal_elim_snd _ _ _ _ P4).
  apply (opair_equal_elim_fst _ _ _ _ P4).
Qed.

Lemma id_is_single_rooted: forall A, single_rooted (id A).
Proof.
  intros A a1 a2 b P1 P2.
  destruct (id_elim _ _ P1) as [s1 [_ P3]].
  destruct (id_elim _ _ P2) as [s2 [_ P4]].
  rewrite (opair_equal_elim_fst _ _ _ _ P3).
  rewrite <- (opair_equal_elim_snd _ _ _ _ P3).
  rewrite (opair_equal_elim_fst _ _ _ _ P4).
  apply (opair_equal_elim_snd _ _ _ _ P4).
Qed.

Lemma id_is_function: forall A, function (id A).
Proof.
  intros A.
  split.
  + apply id_is_rel.
  + apply id_is_single_value.
Qed.

Lemma id_is_injection: forall A, injection (id A).
Proof.
  intros A.
  split.
  + apply id_is_function.
  + apply id_is_single_rooted.
Qed.

Lemma id_dom: forall A, A = dom(id A).
Proof.
  intros A.
  apply ax_exten.
  intros x.
  split.
  + intros P1. 
    apply (dom_intro_2 _ _ _ (id_intro A x P1)).
  + intros P1.
    destruct (dom_elim _ _ P1) as [y P2].
    destruct (id_elim _ _ P2) as [s [P3 P4]].
    rewrite (opair_equal_elim_fst _ _ _ _ P4).
    apply P3.
Qed.

Lemma id_ran: forall A, A = ran(id A).
Proof.
  intros A.
  apply ax_exten.
  intros y.
  split.
  + intros P1.
    apply (ran_intro_2 _ _ _ (id_intro A y P1)).
  + intros P1.
    destruct (ran_elim _ _ P1) as [x P2].
    destruct (id_elim _ _ P2) as [s [P3 P4]].
    rewrite (opair_equal_elim_snd _ _ _ _ P4).
    apply P3.
Qed.

Lemma id_fval: forall A x, x ∈ A -> (id A)[x] = x.
Proof.
  intros A x P1.
  symmetry.
  apply fval_intro.
  + apply (id_is_function A).
  + rewrite (id_dom A) in P1.
    apply P1.
  + apply (id_intro _ _ P1).
Qed.

Lemma id_fonto: forall A, fonto (id A) A A.
Proof.
  intros A.
  split.
  + apply id_is_function.
  + split.
    - symmetry. 
      apply id_dom.
    - symmetry.
      apply id_ran.
Qed.

Lemma id_inv: forall A, id A = inv (id A).
Proof.
  intros A.
  apply ax_exten.
  intros x.
  split.
  + intros P1.
    destruct (id_elim _ _ P1) as [y [_ P2]].
    rewrite P2.
    apply inv_intro.
    rewrite <- P2.
    apply P1.
  + intro P1.
    destruct (inv_is_rel (id A) x P1) as [a [b P2]].
    rewrite P2 in P1.
    destruct (id_elim _ _ (inv_elim _ _ _ P1)) as [z [P3 P4]].
    rewrite P2.
    destruct (opair_equal_elim _ _ _ _ P4) as [P5 P6].
    rewrite P5.
    rewrite P6.
    apply (id_intro _ _ P3).
Qed.

(* Constant Function *)
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

Lemma const_is_rel: forall A c, rel (const A c).
Proof.
  intros A c x P1.
  destruct (const_elim _ _ _ P1) as [a [_ P2]].
  exists a.
  exists c.
  apply P2.
Qed.

Lemma const_is_single_value: forall A c, single_value (const A c).
Proof. 
  intros A c a b1 b2 P1 P2.
  destruct (const_elim _ _ _ P1) as [a1 [_ P3]].
  rewrite (opair_equal_elim_snd _ _ _ _ P3).
  destruct (const_elim _ _ _ P2) as [a2 [_ P4]].
  symmetry.
  apply (opair_equal_elim_snd _ _ _ _ P4).
Qed.

Lemma const_is_function: forall A c, function (const A c).
Proof.
  intros A c.
  split.
  + apply const_is_rel. 
  + apply const_is_single_value. 
Qed.

Lemma const_dom: forall A c, A = dom(const A c).
Proof.
  intros A c.
  apply ax_exten.
  intros x.
  split.
  + intros P1.
    apply dom_intro.
    exists c.
    apply (const_intro _ _ _ P1).
  + intros P1.
    destruct (dom_elim _ _ P1) as [a P2].
    destruct (const_elim _ _ _ P2) as [b [P3 P4]].
    rewrite (opair_equal_elim_fst _ _ _ _ P4).
    apply P3.
Qed.

Lemma const_ran: forall A c, A <> ∅ -> {c} = ran(const A c).
  intros A c P1.
  apply ax_exten.
  intros x.
  split.
  + intros P2.
    apply ran_intro.
    destruct (not_empty_exist_elmn _ P1) as [a P3].
    exists a.
    rewrite (in_singleton_equal _ _ P2).
    apply (const_intro _ _ _ P3).
  + intros P2.
    destruct (ran_elim _ _ P2) as [a P3].
    destruct (const_elim _ _ _ P3) as [b [_ P4]].
    destruct (opair_equal_elim _ _ _ _ P4) as [_ P5].
    rewrite P5.
    apply in_singleton.
Qed.

Lemma const_fval: forall A c x, x ∈ A -> c = (const A c)[x].
Proof. 
  intros A c x P1.
  apply fval_intro.
  + apply const_is_function.
  + rewrite <- (const_dom A c).
    apply P1.
  + apply (const_intro _ _ _ P1).
Qed.

(* Combination of Functions *)
Lemma union2_rel: forall F G, rel F -> rel G -> rel (F ∪ G).
Proof.
  intros F G P1 P2 r P3.
  destruct (in_union2_in _ _ _ P3) as [P4|P4].
  + apply (P1 r P4).
  + apply (P2 r P4).
Qed.

Lemma union_rel: forall F, (forall f, f ∈ F -> rel f) -> rel (∪(F)).
Proof.
  intros F P1 r P2.
  destruct (in_union_in _ _ P2) as [s [P3 P4]].
  apply (P1 s P3 r P4).
Qed.

Lemma union2_dom: forall F G, dom(F ∪ G) = dom(F) ∪ dom(G).
Proof.
  intros F G.
  apply ax_exten.
  intros x.
  split.
  + intros P1.
    destruct (dom_elim _ _ P1) as [f P2].
    destruct (in_union2_in _ _ _ P2) as [P3|P3].
    - apply in_in_union2_1.
      apply dom_intro.
      exists f.
      apply P3.
    - apply in_in_union2_2.
      apply dom_intro.
      exists f.
      apply P3.
  + intros P1.
    apply dom_intro.
    destruct (in_union2_in _ _ _ P1) as [P2|P2].
    - destruct (dom_elim _ _ P2) as [f P3]. 
      exists f.
      apply (in_in_union2_1).
      apply P3.
    - destruct (dom_elim _ _ P2) as [f P3]. 
      exists f.
      apply (in_in_union2_2).
      apply P3.
Qed.

Lemma union2_ran: forall F G, ran(F ∪ G) = ran(F) ∪ ran(G).
Proof.
  intros F G.
  apply ax_exten.
  intros x.
  split.
  + intros P1.
    destruct (ran_elim _ _ P1) as [f P2].
    destruct (in_union2_in _ _ _ P2) as [P3|P3].
    - apply in_in_union2_1.
      apply ran_intro.
      exists f.
      apply P3.
    - apply in_in_union2_2.
      apply ran_intro.
      exists f.
      apply P3.
  + intros P1.
    apply ran_intro.
    destruct (in_union2_in _ _ _ P1) as [P2|P2].
    - destruct (ran_elim _ _ P2) as [f P3]. 
      exists f.
      apply (in_in_union2_1).
      apply P3.
    - destruct (ran_elim _ _ P2) as [f P3]. 
      exists f.
      apply (in_in_union2_2).
      apply P3.
Qed.

Lemma disjoint_dom_rel: forall F G, rel F -> rel G ->
  dom(F) ∩ dom(G) = ∅ -> F ∩ G = ∅.
Proof. 
  intros F G P1 P2 P3.
  apply (empty_unique).
  intros s P4.
  destruct (in_inter2_in _ _ _ P4) as [P5 P6].
  destruct (P1 _ P5) as [a1 [b1 P7]].
  absurd (a1 ∈ dom(F) ∩ dom(G)).
  + rewrite P3.
    apply not_in_empty.
  + rewrite P7 in P5. 
    apply in_in_inter2.
    - apply (dom_intro_2 _ _ _ P5).
    - rewrite P7 in P6. 
      apply (dom_intro_2 _ _ _ P6). 
Qed.

(* union2_function *)
Lemma piecewise_function: forall F G, function F -> function G ->
  (dom(F) ∩ dom(G)) = ∅ -> function (F ∪ G).
Proof.
  intros F G [P1 P3] [P2 P4] P5.
  split.
  + apply (union2_rel F G P1 P2).
  + intros a b1 b2 P6 P7.
    destruct (disjoint_selection _ _ _(disjoint_dom_rel _ _ P1 P2 P5) P6) as
      [[P8 P9]|[P8 P9]].
    - destruct (disjoint_selection _ _ _(disjoint_dom_rel _ _ P1 P2 P5) P7) as
        [[P10 P11]|[P10 P11]].
      * apply (P3 _ _ _ P8 P10).
      * absurd (a ∈ dom(F) ∩ dom(G)).
        { rewrite P5.
          apply not_in_empty. }
        { apply (in_in_inter2 _ _ _ (dom_intro_2 _ _ _ P8) (dom_intro_2 _ _ _ P10)). }
    - destruct (disjoint_selection _ _ _(disjoint_dom_rel _ _ P1 P2 P5) P7) as
        [[P10 P11]|[P10 P11]].
      * absurd (a ∈ dom(F) ∩ dom(G)).
        { rewrite P5.
          apply not_in_empty. }
        { apply (in_in_inter2 _ _ _ (dom_intro_2 _ _ _ P10) (dom_intro_2 _ _ _ P8)). }
      * apply (P4 _ _ _ P8 P10).
Qed.

Lemma union_fval: forall f H x, f ∈ H -> function f -> function (∪(H)) -> 
  x ∈ dom(f) -> f[x] = (∪(H))[x].
Proof.
  intros f H x P1 P2 P3 P4.
  destruct (dom_elim _ _ P4) as [y P5].
  rewrite <- (fval_intro _ _ _ P2 P4 P5).
  apply fval_intro.
  + apply P3.
  + apply dom_intro.
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

Lemma union2_fval_1: forall F G x, function F -> function (F ∪ G) -> 
  x ∈ dom(F) -> F[x] = (F ∪ G)[x].
Proof. 
  intros F G x P1 P2 P3.
  destruct (dom_elim _ _ P3) as [y P4].
  rewrite <- (fval_intro _ _ _ P1 P3 P4).
  apply fval_intro.
  + apply P2.
  + apply dom_intro.
    exists y.
    apply in_in_union2_1.
    apply P4.
  + apply in_in_union2_1.
    apply P4.
Qed.
 
Lemma union2_fval_2: forall F G x, function G -> function (F ∪ G) -> 
  x ∈ dom(G) -> G[x] = (F ∪ G)[x].
Proof. 
  intros F G x P1 P2 P3.
  rewrite union2_sym.
  rewrite union2_sym in P2.
  apply (union2_fval_1 G F x P1 P2 P3).
Qed.
