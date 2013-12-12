Require Import InductiveFiniteSets.
Require Export JMeq.


Set Implicit Arguments.

Section Subs.
 
 (* eq_subs : alternative version of eq_rect, where the equality objects are implict *)
 Definition eq_subs := 
    fun (A : Type) (P : A -> Type) (a b : A)
         (H : a = b) (Pa : P a) => eq_rect a P Pa b H.
  

(* dp_rwt - dependent rewrite : elimination rule for "John Major" equality,  *)
(* which allows us to substitute JM-equal, dependently typed terms, poviding *)
(* there is homogeneous equality between the types on which they depend      *)
Definition  dp_rwt : forall (A : Type) (B : A -> Type) (a a1 : A) 
                       (P: forall a: A, forall x: B a,  Type  ) (b : B a) 
		       (b1: B a1), a = a1 -> JMeq b b1   -> P  a b ->  P a1 b1 . 
 Proof. 
  intros A B a a1 P b b1 H; destruct H.
  intro jm; elim  jm; trivial.
 Qed.

(*  *)
Definition  dp_rwt1 : forall (A X: Set) (B : X -> Set) (F G : A -> X) (a a1 : A)
               (P: forall (a: A) (f : A -> X) , B (f a) -> Type ) (b : B (F a)) 
               (b1 : B (G a1)), a = a1 ->  F = G -> JMeq b  b1  -> P a F b -> 
            P a1 G b1 . 
Proof. 
  intros A X B F G a a1 P b b1 H; destruct H.
  intro H1; destruct H1.
  intro jm; elim  jm; trivial.
Qed.

(* usful substitutions about finite types *)
 Lemma fs_eq : forall n : nat, forall  x y : Fin n,  x = y  -> fs x = fs y .
 Proof.
  intros n x y H;
  apply (eq_subs (fun z => fs z = fs y) (sym_equal H));
  trivial.
 Defined .

Lemma fin_fs (n m : nat) (H : n = m) (i : Fin m) (J : Fin n) : JMeq i J -> JMeq (fs i) (fs J).
Proof.
  intros n m H i J H0 . 
  apply (dp_rwt Fin (fun (x : nat) (fx : Fin x) => JMeq (fs fx) (fs J) ) H (sym_JMeq H0)); 
  trivial. 
Defined.
 
End Subs.


Section SigT.

 Lemma sig_prj1 :  forall (A : Type) (P : A -> Type) 
   (x y : sigT P),   projT1 x = projT1 y /\ JMeq (projT2 x) (projT2 y) -> x = y.
  Proof.
   destruct x; destruct y; simpl; auto.
   intro h; destruct h. 
   cut (forall (A : Type) (B : A -> Type) (a a1 : A)
         (P : forall a0 : A, B a0 -> Type) (b : B a) 
         (b1 : B a1), a = a1 -> JMeq b b1 -> P a b -> P a1 b1).
   intro H1.
   exact (H1 _ P _ _ 
          (fun a0 => fun (i : P a0) => existT P a0 i = existT P x0 p0 )
          _ _ (sym_equal H)  (sym_JMeq H0) 
         (refl_equal ( existT P x0 p0))  ). clear.
   intros A B a a1 P b b1 H; destruct H.
   intro H; case (JMeq_eq H); trivial.
 Qed.

 Definition sig_prj :  forall (A : Type) (P : A -> Type) 
   (x y : sigT P), x = y ->  projT1 x = projT1 y /\ JMeq (projT2 x) (projT2 y).
   destruct x; destruct y.
   intro h; dependent rewrite h; auto.
 Defined.

End SigT.
