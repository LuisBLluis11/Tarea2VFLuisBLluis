(**
  Autor: Luis Felipe Benítez Lluis
  script de proposiciones a demostrar de la 
  sección de lógica clásica  *)
Require Import Classical.


Definition cotenability (A B:Prop) := ~ (A -> ~ B).

Notation "A ° B" := (cotenability A B) (at level 60).

(* Ltac tercero_ex (P:Prop) :=
match goal with
| [ |- _ ] => assert (P \/ ~P);
                apply classic
end. *)




(* Mias *)

Ltac tercero_ex T :=
  assert (TE := classic (T));
  destruct TE.
(* Add LoadPath "C_LogicaClasica" .  *)
(* Require Import Defs_LC . *)

Ltac contradiction_classic :=
match goal with
| [ H1: ?A , H2: ~ ?A|- _ ] => contradict H1; assumption
(*| [  |- ~ ?P] => tercero_ex (?P);  2 : {assumption . }*)
end. 


(* Lemas *)
Lemma PNNP_classic: forall P: Prop,
  P-> ~~P.
Proof.
  intros.
  tercero_ex (~P).
  contradiction_classic.
  assumption.
Qed.




Ltac destruct_cot H :=
match goal with
| [ H : _ |- _ ] => unfold cotenability in H;
                    apply imply_to_and in H;
                    destruct H
end.


Proposition and_not_imply : forall A B : Prop, A /\~ B -> ~ (A -> B).
Proof.
intros A B H.
destruct H.
tercero_ex (~ (A -> B)).
- assumption.
- apply NNPP in H1.
  apply H1 in H.
  contradiction_classic.
Qed.

Ltac split_cot :=
match goal with
| [ |- ?A ° ?B ] => unfold cotenability;
                    apply and_not_imply;
                    split
end.




Theorem Contrapos_classic :forall P Q: Prop, (P -> Q) <-> (~Q -> ~P).
Proof.
  split.
  + intros.
    tercero_ex (P).
    2:{ assumption. }
    apply H in H1.
    contradiction_classic.
  + intros. 
    tercero_ex Q.
    assumption.
    apply H in H1.
    contradiction_classic.
Qed.

Check imply_to_or.
Check imply_to_and.








Lemma cotComm_ida : forall A B : Prop, A ° B -> B ° A.
Proof.
   intros.
   destruct_cot H. 
   apply NNPP in H0.
   split_cot.
   * assumption.
   * apply PNNP_classic.
     assumption.
Qed.
Proposition cotComm : forall A B : Prop, A ° B <-> B ° A.
Proof. 
  split.
  * apply cotComm_ida.
  * apply cotComm_ida.
Qed.


Proposition cotAsoc: forall A B C : Prop,
  (A ° B) ° C <-> A ° (B ° C).
Proof.
  split.
  + intros.
    destruct_cot H. 
    apply NNPP in H0.
    apply imply_to_and in H.
    destruct H.
    apply NNPP in H1.
    split_cot.
    * assumption.
    * apply PNNP_classic.
      tercero_ex ((B -> ~ C)).
      2: {assumption. }
      apply H2 in H1.
      contradiction_classic.
  + intros.
    destruct_cot H.
    apply NNPP in H0.
    apply  imply_to_and in H0.
    destruct H0.
    apply NNPP in H1.
    split_cot. 
    * tercero_ex (A -> ~ B).
      2: {assumption. }
      apply H2 in H.
      contradiction_classic.
    * apply PNNP_classic.
      assumption.
Qed.




Proposition cotDist: forall A B C : Prop,
  (A ° B) \/ (A ° C) <-> A ° (B \/ C).
Proof.
  intros.
  split.
  + intros.
    destruct H.
    * destruct_cot H.
      apply NNPP in H0.
      split_cot.
      - assumption.
      - apply PNNP_classic.
        left.
        assumption.
    * destruct_cot H.
      apply NNPP in H0.
      split_cot.
      - assumption.
      - apply PNNP_classic.
        right.
        assumption.
  + intros. 
    destruct_cot H.
    apply NNPP in H0.
    destruct H0.
    * left. split_cot. assumption.
      apply PNNP_classic. assumption.
    * right. split_cot. assumption.
      apply PNNP_classic. assumption.
Qed.

Proposition cotFusion: forall A B C : Prop,
  (A-> B -> C)<->((A ° B)->C).
Proof.
  intros.
  split.
  + intros. destruct_cot H0.
    apply NNPP in H1.
    apply H in H0. assumption. assumption.
  + intros. 
    apply H.
    split_cot.
    assumption.
    apply PNNP_classic.
    assumption.
Qed.

Proposition cotDefImpl: forall A B : Prop,
  (A -> B)<-> ~(A ° (~ B)).
Proof.
  intros.
  split.
  + intros.
    tercero_ex (A ° (~ B)).
    * destruct_cot H0.
      apply NNPP in H1.
      apply H in H0.
      contradiction_classic.
    * assumption.
  + intros.
    tercero_ex (B).
    assumption.
    contradict H.
    split_cot.
    assumption.
    apply PNNP_classic.
    assumption.
Qed.

  
(** Argumentos lógicos como proposiciones.*)  

Proposition A: forall T,forall a:T, forall A B C: T -> Prop,

  ((exists x:T, (A x /\ B x )) -> 
        (forall x :T, (B x -> C x)))

  ->                
  
  (B a /\ ~C a) 
  
  -> 
  
    ~(forall x: T, A x).
Proof.
  intros.
  destruct H0.
  apply ex_not_not_all.
  tercero_ex (A a).
  + assert ( forall x0 : T, B x0 -> C x0).
    apply H; exists a; split; assumption;  assumption.
    specialize H3 with (x0:= a).
    apply H3 in H0.
    contradiction_classic.
  + exists a. assumption.
Qed.



Proposition B: forall T,forall m:T, forall C W: T -> Prop, forall B G: T-> T-> Prop, 

  (exists x:T, (~ B x m /\ 
                           (forall y:T, (C y -> ~ G x y ))))
  
  ->
  
  (forall z :T,(~(forall y,(W y -> G z y) )-> 
                                               B z m) ) 
  
  ->
  
    (forall x, (C x -> ~W x)).
Proof.
  intros.
  destruct H.
  destruct H.
  specialize H0 with (z:= x0).
  apply Contrapos_classic in H0.
  2: { assumption. }
  apply NNPP in H0.
  specialize H2 with (y := x).
  specialize H0 with (y := x).
  apply H2 in H1.
  apply Contrapos_classic in H0.
  2: { assumption. }
  assumption. 
Qed.

  
Lemma Univ_distr_and_classic: 
  forall T ,forall P Q: T -> Prop  , (forall x :T,
  ( P x /\ Q x)) <-> ((forall x:T, P x)/\ (forall x :T, Q x)).
Proof.
  intros.
  split.
  + split.
    intros.
    specialize H with x.
    destruct H.
    assumption .
    intros.
    specialize H with x.
    destruct H.
    assumption .
  + intros.
    destruct H.
    split.
    - specialize H with x.
      assumption.
    - specialize H0 with x.
      assumption.
Qed.
  

Proposition C: forall T, forall P H C L R: T-> Prop, forall A B: T -> T -> Prop, 

  ((~(forall x:T,(~P x \/ ~H x)))
            ->
              (forall x:T,(C x /\
                                  (forall y: T ,(L y -> A x y)))))
  ->
  
  ((exists x:T,(H x /\(forall y:T,(L y -> A x y))))
            ->
              (forall x: T,(R x /\ 
                                  (forall y :T, B x y) )))
    
  ->
    (~forall x y:T, B x y)-> 
    (forall x :T,(~P x\/~ H x)).
Proof.
  do 11 intro.
  tercero_ex ((forall x : T, ~ P x \/ ~ H x)).
  assumption.
  assert(forall x : T, C x /\ (forall y : T, L y -> A0 x y)).
  {apply H0.  assumption. }
  apply not_all_ex_not in H3.
  destruct H3.
  apply not_or_and in H3.
  destruct H3.
  apply NNPP in H3.
  apply NNPP in H5.
  specialize H4 with (x:= x).
  destruct H4.
  assert(forall x : T, R x /\ (forall y : T, B0 x y)).
  {  apply H1. exists x. split. assumption. assumption. }
  apply Univ_distr_and_classic in H7.
  destruct H7.
  contradiction_classic.
Qed.

(*   
  Modus ponens
  modus tolens
  contrapositiva
  specialize sin perder hipotesis
  tercero excluido *)
  
  
  
  
          




