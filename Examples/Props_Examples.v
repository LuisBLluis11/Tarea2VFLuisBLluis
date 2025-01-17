(**
  Autor: Luis Felipe Benítez Lluis
  script de proposiciones a demostrar de la 
  sección ejemplos *)
  
Require Import Classical.
From Tarea2VF Require Export Props_LC .

(** Lemas *)
(* LM*)
Check PNNP_classic.

(* LC *)
Check and_not_imply.

(* LC *)
Check Contrapos_classic .

(*LC y tal vez LI e incluso LM*)
Check Univ_distr_and_classic.

(*LC y tal vez LI e incluso LM*)
Lemma Univ_distr_and_classic_1: 
  forall T, forall a:T,forall P: T -> Prop, forall Q: Prop  , (forall x :T,
  ( P x /\ Q )) <-> ((forall x:T, P x)/\ Q).
Proof.
  intros.
  split. 
  + intros.
    split.
    - intros.
      specialize H with x.
      destruct H.
      assumption.
    - specialize H with a.
      destruct H.
      assumption.
  + intros.
    destruct H.
    specialize H with x. 
    split.
    assumption.
    assumption.
Qed.
  
(** Ejercicios *)

(* LC por el tercero_ex*)
Proposition Ej1: forall A B C D: Prop,
  (A-> B)->
  (~(A\/C)-> D)->
  ((A\/B)-> C)->
  (~D->C).
Proof.
  intros.
  tercero_ex (C).
  assumption.
  apply Contrapos_classic in H1.
  2: {assumption. }
  apply not_or_and in H1.
  destruct H1.
  assert (~(A \/C)).
  + apply  and_not_or .
    split. assumption. assumption.
  + apply H0 in H5.
    contradiction_classic.
Qed.
  

(*LC por el NNPP *)
Proposition Ej2: forall A B C D: Prop, 
  (A \/ B)->
  ((~D->C)->(~B->~A)->(C-> ~B)->D).
Proof.
  intros.
  apply imply_to_or in H0.
  destruct H,H0.
  + apply NNPP in H0.
    assumption.
  + apply H2 in H0.
    apply H1 in H0.
    contradiction.
  + apply NNPP in H0.
    assumption.
  + apply H2 in H0.
    contradiction.
Qed.


(*LI y no LM porque usé contradict*)
Proposition Ej3: forall (T: Type)(a:T)(P B R:T -> Prop),
  (forall x :T, (P x -> ~B x))->
  (R a -> (forall x :T, (R x -> B x))-> ~P a).
Proof.
  intros.
  specialize H1 with (x := a).
  apply H1 in H0.
  specialize H with (x:= a).
  contradict H0. 
  apply H.
  assumption.
Qed.


(* LC por el imply_to_or*)
Proposition Ej4: forall (X: Type)(P B R S T:X -> Prop),
  (forall x:X,(P x \/ B x) -> ~ R x)->
  (forall x:X, (S x -> R x))->
  (forall x:X, (P x -> ~S x \/ T x)).
Proof.
  intros.
  left.
  specialize H with x.
  specialize H0 with x.
  assert ((P x \/ B x )).
  { left; assumption. }
  apply H in H2.
  apply imply_to_or in H0.
  destruct H0.
  assumption.
  contradiction.
Qed.


(* LC  e incluso LM *)
Proposition Ej5: forall (X: Type)(a:X)(P B:X -> Prop),
  (forall x:X, (P x /\ (exists y: X, B y)))-> (exists x: X, (P x /\ B x)).
Proof.
  intros.
  apply Univ_distr_and_classic in H.
  destruct H.
  assert (exists y : X, B y ).
  { apply H0. apply a. }
  destruct H0.
  { apply a. }
  exists x.
  split.
  + specialize H with x.
    assumption.
  + assumption.
Qed.


(* Desde LI, quizás incluso LM *)
Proposition Ej6: forall (X: Type)(P:X -> Prop)(R: X->X-> Prop),
  (forall x: X, exists y:X, (P x -> R x y))->
  (forall x:X, (P x-> (exists y: X, R x y ))).
Proof.
  intros. 
  specialize H with x.
  destruct H. 
  exists x0.
  apply H.
  assumption.
Qed.


(* desde Li quizás incluso LM dependiendo del specialize*)
Proposition Ej7: forall (X: Type)(P B:X -> Prop),
  (forall x:X, P x -> ~ B x)-> 
  ~(exists x:X, (P x /\ B x)).
Proof.
  intros.
  intro.
  destruct H0.
  destruct H0.
  specialize H with x.
  apply H in H0.
  apply H0.
  assumption.
Qed.


(* desde Li y muy seguramente desde LM*)
Proposition Ej8: forall (X: Type)(P :X->X -> Prop),
  (exists x:X, forall y:X ,P x y ) ->
  (forall y:X, exists x:X, P x y).
Proof.
  intros.
  destruct H.
  exists x.
  apply H.
Qed.

