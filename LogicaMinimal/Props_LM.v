(** Tarea 2 Lógica Minimal
    Autor: Luis Felipe Benítez Lluis
      Script de proposiciones a demostrar de la 
      sección de lógica minimal  *)


Proposition LM_a: forall A: Prop, ~~~A <-> ~A.
Proof.
intros.
split.
+ intros.
  intro.
  apply H.
  intro.
  apply H1.
  assumption.
+ intros.
  unfold not.
  intros.
  apply H0 in H.
  assumption.
Qed.

Proposition LM_b: forall A B: Prop, 
  ~~(A /\ B) -> ~~A /\ ~~B.
Proof.
intros.
split.
+ intro.
  apply H.
  intro.
  apply H0.
  destruct H1.
  assumption.
+ intro.
  apply H.
  intro.
  apply H0.
  destruct H1.
  assumption.
Qed.

Proposition LM_c: forall T, forall A : T->Prop,
  ~~(forall x : T, A x)-> (forall x : T, ~~ A x).
Proof.
  intros.
  intro.
  apply H.
  intro.
  apply H0.
  apply H1.
Qed.
  
Lemma PNNP: forall P : Prop, 
  P-> ~~P.
Proof.
  intros. intro. apply H0. apply H.
Qed.

  