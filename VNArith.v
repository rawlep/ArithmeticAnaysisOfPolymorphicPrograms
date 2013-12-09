(* Some useful definitions and lemmas *)
Require Import Arith Omega.
Require Export Vectors.


 Set Implicit Arguments.


 Section Addition_subtraction_multiplication.

  (* addition, subtraction and composition *)
    (* addition, subtraction and composition *)
   Fixpoint vAdd (n : nat) (i : Vec nat n) : Vec nat n -> Vec nat n :=
     match i in Vec _ e return (Vec nat e -> Vec nat e) with
    | vnil => fun _ => vnil _
    | vcons _ x xs => fun j => match vCons j with 
                               | isvcons y ys => vcons (x + y) (vAdd xs ys)
                               end
    end.

    Fixpoint vSub (n : nat) (i : Vec nat n) : Vec nat n -> Vec nat n :=
     match i in Vec _ e return (Vec nat e -> Vec nat e) with
    | vnil => fun _ => vnil _
    | vcons _ x xs => fun j => match vCons j with 
                               | isvcons y ys => vcons (x - y) (vSub xs ys)
                               end
    end. 

  (* Fixpoint vmul (n : nat) (i : Vec Z n) : Vec Z n -> Vec Z n :=
     match i in Vec _ e return (Vec Z e -> Vec Z e) with
    | vnil => fun _ => vnil _
    | vcons _ x xs => fun j => match vCons j with 
                               | isvcons y ys => vcons (x * y) (vmul xs ys)
                               end
    end. *)

    (* compute the evaluation matrix *)
   Fixpoint Vtimes (n : nat) (l : Vec nat n)  : Vec nat n -> Vec nat n :=
    match l as l in (Vec _ e) return Vec nat e -> Vec nat e with
    | vnil => fun _ => vnil _
    | vcons _ x ls =>
              fun j => match vCons j with
                       | isvcons y ys => vcons (x * y) (Vtimes ls ys)
                       end
    end.
  

  (* sum the elements of a vector *)
  Fixpoint vsum (n : nat) (i : Vec nat n)  :=  
   match i with
   | vnil  => 0
   | vcons _ n ns => n + vsum ns
   end.

  Lemma vsum_vplus n m (i : Vec nat n) (j : Vec nat m) :  vsum (vPlus i j)  = vsum i + vsum j.
  Proof.
      induction i; simpl; trivial.
      intros j; rewrite (IHi j); auto with arith.
  Qed.

  Lemma vsum_plus n m (v : Vec nat (n + m)): 
       vsum v = match vplusView _ _ v with
                | vplus a b => vsum a + vsum b
                end.
  Proof.
    intros n m v; vSimp; apply vsum_vplus. 
  Qed.

   Fixpoint ZSumz (n : nat) (l : Vec nat n)   :=
     match l as l in (Vec _ e)  with
       | vnil => 0
       | vcons _ x ls =>  (ZSumz ls) + x
     end. 

 Lemma ZSz_Vtms (n : nat ) (v i0 i : Vec nat n) :
   ZSumz (Vtimes (vAdd v i0) i) = ZSumz (Vtimes v i) + ZSumz (Vtimes i0 i).
 Proof.
    induction v; intros; vSimp; simpl; trivial. rewrite (IHv i0 i); ring.
  Qed.

 
(* Lemma ZSz_sub (n : nat ) (v i0 i : Vec nat n) :
   ZSumz (Vtimes (vSub v i0) i) = ZSumz (Vtimes v i) - ZSumz (Vtimes i0 i).
  Proof.
   induction v; intros; vSimp; simpl; trivial. rewrite (IHv i0 i).   
   replace ((x - a0) * a) with (x * a - a0 * a); auto with arith. omega. 
  Qed. *)

  Lemma vtimesPlus (n m : nat) (i i1  : Vec nat n) (j j1 : Vec nat m) :
     Vtimes (vPlus i j) (vPlus i1 j1) = vPlus (Vtimes i i1) (Vtimes j j1).
  Proof.
   induction i;  intros; vSimp; simpl; trivial. rewrite (IHi i0 j j1); trivial.
  Qed.

 Lemma zSumzPlus (n m: nat) (i : Vec nat n) (j : Vec nat m) : ZSumz (vPlus i j) = ZSumz i + ZSumz j.
 Proof.
   induction i; simpl; trivial. intro j; rewrite (IHi j);  ring.
 Qed.


  Lemma ZSumz_vmap_Vtimes (n : nat) (v : Vec nat n) (a  : nat) :
     forall x,  ZSumz (Vtimes (vmap (fun x1  => a * x1) v) x) =  a * (ZSumz (Vtimes v x) ). 
  Proof.
    induction v; intros; vSimp; simpl; trivial; try auto with arith.
    rewrite (IHv a i); ring.
  Qed. 

 (* misc *)
 Ltac vsimpl :=  unfold vhead in *; unfold vtail in *;  simpl in *.

 Lemma vtimes0 n i j : i = vec n 0 -> Vtimes i j = vec n 0.
  Proof.
    induction n; intros; vSimp; simpl; auto. destruct (VeqInj2 H); vsimpl.
    rewrite (IHn i i0 H1); subst; trivial.
 Qed. 

 Lemma vtimes_comm (n : nat) (i j : Vec nat n):  Vtimes i j = Vtimes j i.
 Proof.
  induction i; intros; vSimp; simpl; auto.
   rewrite (IHi i0). replace (a * x) with (x * a); trivial; try ring.
 Qed.

 Lemma Zsumz_0 : forall n , ZSumz (vec n 0) = 0.
  Proof. 
    induction n; simpl; trivial. rewrite IHn; trivial.
  Qed.
 
 Lemma vecPlus0  n m i j :
   i = vec n 0 -> j = vec m 0 -> vPlus i j = vec (n + m) 0.
  Proof. 
    induction i; intros; simpl; trivial. destruct (VeqInj2 H); vsimpl.
    rewrite H1. rewrite (IHi j H2 H0); trivial.
 Qed.

  Lemma vPluz_0 : forall n m, 
    match vplusView _ _ (vec (n + m) 0)  with
     | vplus x y => x = vec n 0 /\ y = vec m 0
    end.
   induction n; intros; simpl;  auto.
    generalize ( IHn m); intro. destruct (vplusView _ _ (vec (n + m) 0)).
   destruct H. rewrite H; auto.
  Qed.

  Lemma vPluz_1 (A : Set) (n m : nat) (i : Vec  A n) (j : Vec A m) :
    match vplusView _ _ (vPlus i j)  with
     | vplus x y => x = i /\ y = j
    end.
   induction i; intros; simpl; auto.
    generalize ( IHi j).  destruct (vplusView _ _ (vPlus i j)).
    intro H; destruct H; subst; auto.
  Qed.

  Lemma vecPlus00  n m i j :  vPlus i j = vec (n + m) 0 ->  i = vec n 0 /\ j = vec m 0 .
  Proof.
    induction n; intros; vSimp; simpl; auto.
    destruct (VeqInj2 H); vsimpl. destruct (IHn m i j H1). rewrite H0.
    rewrite H2; auto.
  Qed.

  Lemma vadd_id  n i : vAdd i (vec n 0) = i.
    induction i;  simpl; trivial. rewrite plus_0_r; rewrite IHi ; trivial.
  Qed.

  Lemma vtimesPlus1 (n m : nat) ( v : Vec nat n) (v0 : Vec nat m) (i0 : Vec nat n) (j0 : Vec nat m) : 
    ZSumz (Vtimes (vPlus v v0) (vPlus i0 j0))  = ZSumz (Vtimes v i0) + ZSumz (Vtimes v0 j0) .
  Proof. 
    induction v; intros; vSimp; simpl; trivial.  rewrite (IHv v0 i j0); ring.
  Qed.

  
  Lemma vtimes_vcons_vsnoc n (xs : Vec nat n) (ys : Vec nat (S n)) x :
      ZSumz (Vtimes (vSnoc x xs) ys) = ZSumz (Vtimes xs (vfirst ys)) + x * (vlast ys).
  Proof.
    induction xs; intros; vSimp; vsimpl; simpl; trivial; try vecRwt. 
    unfold vfirst;  vsimpl.
    rewrite (IHxs (vcons a0 i) x0 );  unfold vfirst; unfold vlast; vsimpl; ring.
  Qed.

 
   Lemma Vtimes_vSnoc n (v v1 : Vec nat (S n)) : 
     ZSumz (Vtimes v (vSnoc (vlast v1) (vfirst v1))) =
     ZSumz (Vtimes (vfirst v) (vfirst v1)) +  vlast v * vlast v1.
   Proof. 
     intros n v; destruct (vCons v) as [vh vt]. 
     generalize vh; clear; induction vt.
     intros vh v1; destruct (vCons v1); unfold vlast; unfold vfirst; vsimpl; vSimp; trivial.
     intros vh v1; destruct (vCons v1) as [b bs].
     destruct (vCons bs) as [y ys];  generalize (IHvt x (vcons y ys)); clear; 
     unfold vlast; unfold vfirst; vsimpl. 
     destruct ( vCons (vSnoc (vlast_aux y ys) (vfirst_aux y ys))); simpl.
     intro H;  rewrite H; ring.
   Qed.

  (* this belong in the vectors file *-)
   Lemma vVsnoc n (X : Set) (v : Vec X (S n)) : v = vSnoc (vlast v) (vfirst v).
   Proof.
     intros; vSimp. generalize a; unfold vlast; unfold vfirst; vsimpl; clear.
    induction i ; simpl; trivial. intros; rewrite (IHi x); trivial.
  Qed.*)
  
 End Addition_subtraction_multiplication.

 (* exporting tactics *)
 
