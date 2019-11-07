(* Some logic result, including law of excluded middle.*)
Axiom LEM: forall P: Prop, P \/ ~P.

Lemma NN_elim: forall P: Prop, ~~P -> P.
Proof.
  intros P H1.
  pose (H2 := LEM P).
  destruct H2.
  + assumption.
  + contradiction.
Qed.

Lemma NN_intro: forall P: Prop, P -> ~~P.
Proof.
  intros P H1 H2.
  contradiction.
Qed.

Lemma contraposition: forall P Q: Prop, (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H1 H2 H3.
  apply (H2 (H1 H3)).
Qed.

Lemma contraposition2: forall P Q: Prop, (~P -> Q) -> (~Q -> P).
Proof.
  intros P Q H1 H2.
  apply NN_elim.
  apply (contraposition (~P) Q H1 H2).
(*  apply contraposition.*)
(*  assert ((~P -> Q) -> ~Q -> ~~P) as H1.*)
(*  apply contraposition.*)
(*  assert (~~P -> P) as H2.*)
(*  apply NN_elim.*)
(*  intros Q1 Q2.*)
(*  apply H2.*)
(*  apply H1.*)
(*  assumption.*)
(*  assumption.*)
Qed.

Lemma contraposition3: forall P Q: Prop, (P -> ~Q) -> (Q -> ~P).
Proof.
  intros P Q H1 H2.
  apply ((contraposition P (~Q) H1) (NN_intro Q H2)).
Qed.

Lemma contraposition4: forall P Q: Prop, (~P -> ~Q) -> (Q -> P).
Proof.
  intros P Q H1 H2.
  apply NN_elim.
  apply (contraposition3 (~P) Q H1 H2).
Qed.

Lemma not_and_or: forall P Q: Prop, ~(P /\ Q) -> ~P \/ ~Q.
Proof.
  intros P Q H1.
  destruct (LEM P) as [H2|H2].
  + destruct (LEM Q) as [H3|H3].
    - absurd (P /\ Q).
      * apply H1.
      * split. apply H2. apply H3.
    - right.
      apply H3.
  + left.
    apply H2.
Qed.

Lemma not_or_and: forall P Q: Prop, ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  intros P Q H1.
  split.
  + destruct (LEM P) as [H2|H2].
    - absurd (P \/ Q).
      * apply H1.
      * left. apply H2.
    - apply H2.
  + destruct (LEM Q) as [H2|H2].
    - absurd (P \/ Q).
      * apply H1.
      * right. apply H2.
    - apply H2.
Qed.

Lemma and_not_or: forall P Q: Prop, ~P /\ ~Q -> ~(P \/ Q).
Proof.
  intros P Q H1 H2.
  destruct H1.
  destruct H2.
  contradiction.
  contradiction.
Qed.

Lemma or_not_and: forall P Q: Prop, ~P \/ ~Q -> ~(P /\ Q).
Proof.
  intros P Q H1 H2.
  destruct H2.
  destruct H1.
  contradiction.
  contradiction.
Qed.

Lemma not_exists_forall_not: forall T: Prop, forall P: T -> Prop, 
  ~(exists A: T, P A) -> (forall A: T, ~(P A)).
Proof.
  intros T P H1 A H2.
  absurd (exists A, P A).
  + apply H1.
  + exists A.
    apply H2.
Qed.

Lemma not_forall_exists_not: forall T: Prop, forall P: T -> Prop, 
  ~(forall A: T, P A) -> (exists A: T, ~(P A)).
Proof.
  intros T P.
  apply contraposition2.
  intros H1 A.
  pose (H2 := not_exists_forall_not T (fun x => ~P x) H1 A).
  apply (NN_elim (P A)).
  apply H2.
Qed.

Lemma and_sym: forall P1 P2: Prop, P1 /\ P2 -> P2 /\ P1.
Proof.
  intros P1 P2 H1.
  destruct H1 as [H2 H3].
  split.
  + apply H3.
  + apply H2.
Qed.

Lemma or_sym: forall P1 P2: Prop, P1 \/ P2 -> P2 \/ P1.
Proof.
  intros P1 P2 H1.
  destruct H1 as [H2|H2].
  + right. apply H2.
  + left. apply H2.
Qed.
