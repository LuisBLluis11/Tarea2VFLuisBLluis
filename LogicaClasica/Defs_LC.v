(**
  Autor: Luis Felipe Benítez Lluis
  script de definiciones de la 
  sección de lógica clásica  *)
  
 Require Import Classical. 

Definition cotenability (A B:Prop) := ~ (A -> ~ B).

Notation "A ° B" := (cotenability A B) (at level 60).
Ltac tercero_ex T :=
  assert (TE := classic (T));
  destruct TE.


Ltac contradiction_classic :=
match goal with
| [ H1: ?A , H2: ~ ?A|- _ ] => contradict H1; assumption
(*| [  |- ~ ?P] => tercero_ex (?P);  2 : {assumption . }*)
end. 

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


(*No supe como evitar poner le teorema and_not_imply
  en esta sección*)
 Ltac split_cot :=
match goal with
| [ |- ?A ° ?B ] => unfold cotenability;
                    apply and_not_imply;
(*                    pose proof and_not_imply;*)
                    split
end. 