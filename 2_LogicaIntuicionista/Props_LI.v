(**
  Autor: Luis Felipe Benítez Lluis
  script de proposiciones a demostrar de la 
  sección de lógica intuicionista  *)
  
Lemma Para_a: forall A B : Prop,
  ~~A -> ~B ->~(A->B).
Proof.
  intros.
  intro.
  apply H.
  intro.
  apply H1 in H2.
  contradiction.
Qed.

Lemma Para_b_1: forall A B : Prop,
  ~(A->B)->~~A.
Proof.
  intros.
  intro.
  apply H.
  intros.
  contradiction.
Qed.

Lemma Para_b_2: forall A B : Prop,
  ~(A->B)->~B.
Proof.
  intros.
  intro.
  apply H.
  intro.
  assumption.
Qed.

Proposition LI_a: forall A B: Prop,
  ~~(A->B)-> ~~A->~~B.
Proof.
  intros.
  intro.
  apply H.
  intro.
  apply H0.
  intro.
  apply H2 in H3.
  contradiction.
Qed.


Proposition LI_b: forall A B: Prop,
  (~~A->~~B)->~~(A->B). 
Proof.
  intros.
  intro.
  apply Para_b_2 in H0 as H1.
  apply Para_b_1 in H0 as H2.
  apply H in H2.
  contradiction.
Qed.

Proposition LI: forall A B: Prop,
  (~~A->~~B)<->~~(A->B).
Proof. 
  split.
  apply LI_b.
  apply LI_a.
Qed.

 