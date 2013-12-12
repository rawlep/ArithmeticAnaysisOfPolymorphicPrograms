Require Import Eqdep_dec Peano_dec Substitution JMeq. 
Require Import Image Arith.
Require Export InductiveFiniteSets Arith. 

(**  * Definitions and proofs about co products of Finite types, etc  *)

Set Implicit Arguments.

Section FinSum_defs.

Implicit Arguments fz [n ].
 

 Fixpoint fin_inl (n m : nat ) (i : Fin n) {struct i} : Fin (n + m) :=
          match i  in Fin n return Fin (n + m) with
          | fz _  => fz 
          | fs x k => fs (fin_inl  m  k)
          end.

 Fixpoint  fin_inr (n m : nat) (i:Fin m) {struct n}: Fin (n + m) :=
     match n return Fin (n + m) with
        | O => i
        | S n' => fs (fin_inr n' i)
       end.

 
  (** View for CoProducts of finite types  *)
  Inductive FinSum (n m : nat)  : Fin (n + m) -> Type :=
         | is_inl : forall i: Fin n ,  FinSum n m (fin_inl m  i)
         | is_inr : forall j: Fin m, FinSum  n m  (fin_inr  n j).

  Fixpoint finsplit (n m : nat) {struct n}  
                : forall  (i : Fin (n + m)), FinSum n m i :=
     match n as e return (forall  (i : Fin (e + m)), FinSum e m i) with
     | O => fun i => is_inr _ i
     | S n' => fun i =>  let f := finSN i in
                   match f in (FinSN f0) return (FinSum (S n') m f0) with
                   | isfz => is_inl m  (fz (n := n'))
                   | isfs j =>  let f0 := (finsplit n' m j) in
          match f0 in (FinSum _ _ f1) return (FinSum (S n') m (fs f1)) with
                     | is_inl x => is_inl m (fs x)
                     | is_inr y => is_inr (S n') y
                     end
                  end
     end. 

(** * Results and Proofs *)
 Lemma finsplit_inl : forall (n m: nat) (i : Fin n),    
             finsplit n m (fin_inl m i) = is_inl m   i.
 Proof.
   intros n m; induction i; simpl; trivial. 
   rewrite IHi; reflexivity.
 Qed.

 Lemma finsplit_inr : forall (n m: nat) (i : Fin m),    
        finsplit n m (fin_inr  n i) = is_inr  n  i.
 Proof.
   induction n; simpl; trivial. 
   intros m i; rewrite (IHn m i); reflexivity.
 Qed.

 Lemma fin_inl_inject : forall (n m : nat) (i j : Fin n), 
       fin_inl  m i = fin_inl  m j -> i = j.
 Proof.
   induction i; destruct j using FinSn_rect; auto. 
   intro H ; discriminate H. 
   intro H; rewrite (IHi j (fsInject  H)) ; trivial.
   intro H; discriminate H.
 Qed.

Lemma fin_inr_inject : forall (n m : nat) (i j : Fin m),  
   fin_inr n  i = fin_inr n  j -> i = j.
Proof.
   induction n; simpl; auto.
   apply (fun m i j H =>  (IHn m i j (fsInject H))).
Qed.

 Definition fincase (n m : nat)(X : Type )  (l : Fin n -> X) ( r : Fin m -> X) 
     (i : Fin ( n + m)):= 
   let f := finsplit n m i in
   match f with
   | is_inl i => l i
   | is_inr j => r j
   end.

 Lemma f_fincase (n m : nat) (X Y : Type) (f : X -> Y)  
                (l : Fin n -> X) ( r : Fin m -> X) (i : Fin ( n + m)) :
       f (fincase l r i) = fincase (fun x  => f (l x)) (fun x => f (r x)) i .
 Proof.
  unfold fincase; intros n m X Y f l r i.
  destruct (finsplit n m i); trivial.
 Qed.


Definition FinCase (n m : nat) (i : Fin (n + m)) : Fin n + Fin m :=
   match finsplit n m i with
   | is_inl a => inl (Fin m) a
   | is_inr a => inr (Fin n) a
   end.

Definition CaseFin (n m : nat) (i : Fin n + Fin m ) : Fin (n + m) :=
  match i with
  | inl a => fin_inl  m a
  | inr b => fin_inr n  b
  end.
 
Lemma FinCaseFin : forall (n m : nat)(i : Fin n + Fin m), 
    FinCase n m (CaseFin i) = i.  
Proof.
  unfold FinCase; unfold CaseFin. 
  intros n m i; destruct i; auto.
  rewrite (finsplit_inl m f); reflexivity.
  rewrite (finsplit_inr n f); reflexivity.
Qed.

Lemma CaseFinCase : 
   forall (n m : nat)(i : Fin (n + m)), CaseFin (FinCase n m i) = i.
Proof.
  unfold CaseFin; unfold FinCase.
  intros n m i; destruct (finsplit n m i); trivial.
Qed.

Lemma FinCase_inl (n m  : nat) (i : Fin n) : 
   (FinCase n m (fin_inl  m i) )= (inl (Fin m) i).
Proof.
  intros n m i;  unfold FinCase.
  rewrite  finsplit_inl; trivial.
Qed.

Lemma FinCase_inr (n m  : nat) (i : Fin m) : 
    (FinCase n m  (fin_inr  n i) )= (inr (Fin n) i).
Proof.
  intros n m i;
  unfold FinCase.
  rewrite  finsplit_inr; trivial.
Qed. 

Lemma fincase1 (A: Type) (n m : nat)
    (f : Fin (S n) -> A) (g : Fin m -> A)  (a : Fin (n + m)) :  
               fincase f g (fs a) = fincase (fun i => f (fs i)) g a.
Proof.
  unfold fincase; intros A n m f0 g0 a ; simpl. 
  destruct (finsplit n m a); trivial .
Qed. 

Lemma finCase_eq  (n m : nat) 
     (f : Fin n -> nat) (g : Fin m -> nat)  (a : Fin (n + m)) :  
               match  FinCase n m  a with
               inl z => f z
               | inr z => g z
               end = fincase f g a.
 Proof.
  unfold fincase; unfold FinCase.
  intros n m f0 g0 i.
  destruct (finsplit n m i); trivial.
 Qed.

 Lemma fincaseS (n m : nat) (f : Fin (S n) -> nat)
     (g : Fin m -> nat)  (a : Fin (n + m)) :  
               match  FinCase n m  a with
               inl z => f (fs z)
               | inr z => g z
               end = 
              match FinCase (S n) m (fs a) with
              | inl z => f z
              | inr z => g z
             end. 
Proof.
  intros n m f0 g0 a.
  generalize (finCase_eq (fun x => f0 (fs x)) g0 a).
  intro H; simpl in H.
  rewrite H. 
  rewrite (finCase_eq f0 g0 (fs a)). 
  apply (sym_equal (fincase1 f0 g0 a)).
Qed.


End FinSum_defs.


Section reversing_inductive_finite_sets.
 (** * Top and Embed *)

 Implicit Arguments fz [ n].
 Fixpoint emb (n : nat) (i:Fin n) {struct i }: Fin (S n) :=
   match i in Fin n  return Fin (S n) with
   |  fz _  =>  fz 
   |  fs _ j => fs (emb j)
   end. 
     
 Fixpoint tp (n:nat) : Fin (S n) :=
    match n return Fin (S n) with
    | O => fz 
    | S x' => fs (tp x' )
   end.

(** View on tp and emb *)
Inductive FinEmtp (n : nat) : Fin (S  n) -> Type :=
   | isTp :  FinEmtp (tp n)
   | isEmb : forall  (i : Fin n), FinEmtp (emb i).

 Fixpoint finEmtp (n : nat) : forall i : Fin (S n) ,  FinEmtp i :=
   match n as e return (forall i : Fin (S e), FinEmtp i) with
   | O => fun i => let f := finSN i in  
          match f in (FinSN f0) return FinEmtp f0 with
          | isfz => isTp 0
          | isfs j => match (fin_0_empty j) with end
          end
   | S n' => fun f => let f' := finSN f in
           match f' in (FinSN f0) return FinEmtp f0 with
           | isfz => isEmb (fz (n := n'))
           | isfs i => let k := finEmtp i in
              match k in (FinEmtp  f1) return (FinEmtp  (fs f1)) with
              | isTp => isTp (S n') 
              | isEmb i => isEmb (fs  i)
              end
           end
   end.

 Definition FinEmTp_rect
     : forall (n : nat) (P : Fin (S n) -> Type),
       (forall y : Fin n, P (emb y)) -> P (tp n) -> forall x : Fin (S n), P x :=
   fun n P H0 H1 x => match (finEmtp x) in (FinEmtp  e) return (P e) with
                    | isTp => H1
                    | isEmb i => (H0 i)
                    end.

  (** forgetful function using the emb _ tp view *)
  Fixpoint foo1 n : Fin n -> nat :=
    match n as e return Fin e -> nat with
    | O => fun i => 
             match (fin_0_empty i) return nat with end 
    | S m => fun i => match (finEmtp i) with
                      | isTp => m
                      | isEmb j => foo1 j
                      end
    end.

 
  (* tp not fz *)
  Lemma tp_not_fz : forall n, tp (S n) <> fz (n := S n).
  simpl. unfold not;  intros n H; inversion H.
 Qed.

 Lemma tp_emb (n : nat) (i : Fin n): tp n = emb i -> False.
 Proof.
   induction i; simpl.
   intros h; discriminate h.
    apply (fun H => IHi (fsInject H)).
 Qed.

Lemma fs_emb (n : nat) (i : Fin n) : fs i = emb i -> False.
Proof.
  induction i.
  intro h; discriminate h.
  simpl. apply (fun H => IHi (fsInject H)).
Qed.

(* emb is injective *)
 Lemma  embInject ( n :nat) (i j: Fin n) :   emb i = emb j -> i = j .
 Proof.
   induction i; destruct j using FinSn_rect; simpl.
   intro h; discriminate h. trivial.
   intro h; rewrite (IHi j (fsInject h)); trivial. 
   intro h; discriminate h.
Qed.

 (** Reversing the nat-indexed family, Fin  *)
 Fixpoint rv (n:nat) (i:Fin n) {struct i} : Fin n :=
    match  i in Fin n  return Fin n with   
    |  fz p => tp p 
    |  fs _ k => emb  (rv k)
   end.   

 Lemma emb_S :  forall n: nat, forall i: Fin n, rv  (emb i) = fs (rv i).
 Proof.
   induction  i; simpl; auto.
   rewrite IHi;  simpl;  trivial.
 Qed.             
        
 (** reversing Fin is involutive *)
 Theorem idem_rvFin: forall n: nat, forall i:Fin n,  rv (rv i) = i.
 Proof.
   induction i; simpl;  auto.
   induction n; simpl; auto.
   rewrite IHn ; trivial.   
   rewrite (emb_S (rv i));  rewrite IHi; reflexivity.
 Qed.

 Lemma fsFz (n : nat) (i : Fin n) : rv fz = rv (fs i) -> False .
 Proof.
   intros  n i; simpl; generalize (rv i) . 
   induction f; simpl; try  (intro h; discriminate h). 
   exact (fun H => IHf f (fsInject H)).
 Qed.
 
  (** rev in injective *)
 Lemma rvInject (n : nat) (i j : Fin n) : rv i = rv j -> i = j.
 Proof.
    induction n. 
    abstract inversion i.
    intros i j; destruct j using FinSn_rect . 
    destruct i using FinSn_rect.
    intro H; elim (IHn i j (embInject (rv i) (rv  j) H)); trivial.
    intro H; case (fsFz j H).
    destruct i using FinSn_rect; auto.  
    intro H; case (fsFz i (sym_equal H)).
Qed. 
 
 Lemma rvdist (n: nat) (i j: Fin n): rv  i = j -> i = rv j.
 Proof.
  intros n i j H; 
  apply (eq_subs (fun x : Fin n => x = rv (n := n) j) 
       (idem_rvFin i) (f_equal (rv (n := n)) H)).
 Qed.

 Lemma rvdistJM (n m : nat) (H : n = m) (i : Fin n) (j : Fin m) : 
        JMeq (rv i) j -> JMeq i (rv j).
 Proof. 
  intros n m H ; case H.
  intros i j h; rewrite  (rvdist i (JMeq_eq h) ); trivial.
 Qed. 

Lemma idmrv_subst: forall (n : nat) (i : Fin n) 
  (P : Fin n -> Fin n -> Type), P (rv (rv i))  (rv i) -> P i (rv i).
 Proof.
   intros n i P; 
   rewrite (idem_rvFin i); 
   trivial.
 Qed.
  
Definition rv_elim (n: nat) (i : Fin n) 
  (P : Fin n -> Fin n -> Type ) (H : forall j, P (rv j) j) : P i (rv i) :=
   idmrv_subst i P (H (rv i)).

 Section Foo.
    (** *** Redunctions *)
  
   Lemma foo_emb : forall n (i : Fin n), foo (emb i) = foo i.
     induction i; simpl; auto.
   Qed.

    Lemma foo_rvtp:  forall n : nat, foo (rv (tp n)) = 0.
      induction n; simpl ; auto.
      rewrite <- IHn.
      apply foo_emb.
    Qed.
 
    Lemma foo_tp : forall n, foo (tp n) = n.
      induction n; simpl; auto.
    Qed.

    Lemma fooRv n (i : Fin n) : foo (rv i) = n - (foo i) - 1.
    Proof.
      induction i; simpl. rewrite <- (minus_n_O ).
      apply foo_tp. rewrite foo_emb. trivial.
    Qed.

    Lemma foo_inl n m (i : Fin n) : foo (fin_inl m i) = foo i.
    Proof.
       induction i; simpl; auto.
    Qed.

     Lemma foo_inr n m (i : Fin m) : foo (fin_inr n i) =  n + (foo i).
    Proof.
      induction n; simpl; auto.
    Qed.

   Lemma foo_nm n m (i : Fin (n + m)) : foo i = 
       match finsplit  n m  i with
       | is_inl a => foo a
       | is_inr a => n + foo a
       end.
    Proof.
      intros n m i; destruct (finsplit n m i);  
      [rewrite (foo_inl m i); trivial |  rewrite (foo_inr n j); trivial]. 
   Qed.

    
      
 End Foo.


Section Alternative_Reverse.
 (** * Alternative Definition of rev *) 

 Definition S1 (n:nat) : S n = n + 1.
 Proof.
  induction n; auto.
  exact (eq_subs (fun x : nat => S x = S n + 1) (sym_equal IHn) 
    (refl_equal (S n + 1)) ).
 Defined.

 Axiom eq_unique : forall (A : Set) (a : A) (H : a = a), H = refl_equal a.
 Axiom extensionality : forall (A B: Type)  (f g: A ->  B ), 
      (forall a , f a = g a )-> f =g. 

 Definition Rv (n : nat) : Fin n ->   Fin n.  
  induction n.
  intro i; try inversion i.
  exact (fun i : Fin (S n) => 
       fincase (fun (x:  Fin n) => fs (IHn x)) (fun _ : Fin 1 => fz ) 
         (eq_subs Fin (S1 n) i) ).
 Defined.

Lemma Rv_fs (n : nat) (i : Fin (S n)) :
   Rv i = fincase (fun a : Fin n => fs (Rv a)) (fun _ : Fin 1 => fz ) 
    (eq_subs Fin (S1 n)  i).
 Proof.
    intros n i; destruct i using FinSn_rect; auto.
 Qed.
 
 Lemma F_fincase (n : nat) (i : Fin (n + 1) )(F : forall m : nat, Fin m -> 
     Fin (S m)) :
     fincase (fun x : Fin n => F (S n) (fs (Rv x))) 
       (fun _ : Fin 1 => F (S n)  fz ) i =
   F (S n) (fincase (fun x : Fin n => fs (Rv x)) (fun _ : Fin 1 => fz ) i).
 Proof.
  intros n i F; unfold fincase.
  destruct (finsplit n 1 i); trivial.
 Qed.

 Lemma fs_eq_subs (n m : nat) (H : n = m) (i : Fin n) :  
      fs (eq_subs Fin H i) = eq_subs Fin (f_equal S H) (fs i).
  Proof. 
   intros n m H; case H; trivial.
  Qed.

 Lemma match_rem1 (n m : nat) (H : n = m) (H1 : S n = S m)  (i : Fin n) :
   match H1 in ( _ = y ) return (Fin y) with 
   | refl_equal => fs i
   end = 
   match H in ( _ = y ) return (Fin (S y)) with 
   | refl_equal => fs i
   end .
 Proof.
  intros n m H; case H.
  intro H1; rewrite (eq_unique H1); trivial.
 Qed. 

(*Require Import Peano_dec. *)

 Lemma emb_Rv : forall  (n : nat) (i : Fin n), Rv (fs i) = emb (Rv i).
 Proof.
  induction n.
  intro i; try inversion i. 
  intro i; destruct i using FinSn_rect.
  replace (emb (Rv (fs i))) with 
    (fincase (fun x : Fin n => fs (emb (Rv x))) (fun _ : Fin 1 => fz )
                            (eq_subs Fin (S1 n) (fs i))).
  rewrite  (extensionality  (fun x : Fin n => fs (emb (Rv x)))
           (fun x : Fin n => fs (Rv (fs x))) 
           (fun a : Fin n => fs_eq (sym_eq (IHn a))) ).
  rewrite (Rv_fs (fs (fs i))). 
  replace (eq_subs Fin (S1 (S n)) (fs (fs i))) with
       (fs (eq_subs Fin (S1 n) (fs i))).
  unfold fincase.
  destruct (finsplit n 1 (eq_subs Fin (S1 n) (fs i))).
  generalize  (finsplit_inl  1 (fs i0)).
  intro H; simpl fin_inl in H; rewrite H; trivial.
  destruct j using FinSn_rect.
  inversion j. 
  Implicit Arguments fz [ ].
  simpl; rewrite (finsplit_inr n (fz 0) ); trivial.
  rewrite (fs_eq_subs (S1 n) ).
   rewrite (proof_irrelevance (S (S n) = S n + 1)
     (S1 (S n)) (f_equal S (S1 n)) ); trivial.
  simpl Rv at 2; rewrite <- (F_fincase n (eq_subs Fin (S1 n) (fs i)) emb);  trivial.
  simpl .
  rewrite <- (F_fincase n (eq_subs Fin (S1 n) (fz n)) emb);  trivial.
  rewrite   (extensionality
 (fun x : Fin n  => emb (fs  (Rv x))) (fun x : Fin n => fs (Rv (fs x)))
 (fun x : Fin n => fs_eq (sym_equal (IHn x)))
  ).
 replace  (eq_subs Fin
        (eq_subs (fun x : nat => S x = S (n + 1)) (sym_equal (S1 n))
           (refl_equal (S (n + 1)))) (fs (fz n))) with (fs  (eq_subs Fin (S1 n) (fz n))).
 rewrite (fincase1 (fun x : Fin (S n) => fs (fincase (fun x0 : Fin n => fs (Rv x0))
                    (fun _ : Fin 1 => fz n) (eq_subs Fin (S1 n) x))) 
     (fun _ : Fin 1 => fz (S n))
          (eq_subs Fin (S1 n) (fz n))); trivial.
 replace (eq_subs (fun x : nat => S x = S (n + 1)) (sym_equal (S1 n))
        (refl_equal (S (n + 1)))) with (S1 (S n)); auto.
 rewrite (proof_irrelevance (S (S n) = S n + 1)
     (S1 (S n)) (f_equal S (S1 n)) ); trivial. 
 rewrite  (fs_eq_subs (S1 n) (fz n)); trivial.
Qed. 

 
 Lemma fz_eq_subs (n m : nat) (H : S n =  S m) :
   fz m = match H in ( _ = y) return (Fin  y)  with
         | refl_equal => fz n
          end.
 Proof.
   intros n m H ; injection  H. 
   intro H1; destruct  H1. 
   apply  (eq_subs (fun x : S n = S n => fz n =
                          match x in (_ = y) return (Fin y) with
                          | refl_equal => fz n
                          end ) (sym_equal (eq_unique H))); trivial. 
 Qed. 

 Lemma rv_Rv : forall (n : nat) (i : Fin n), rv i = Rv i.
 Proof.
  induction n.
  intro i; try inversion i.
  intro i; destruct i using FinSn_rect.
  rewrite (emb_Rv i); rewrite <- (IHn i); trivial.
  destruct n. 
  simpl; trivial.
  simpl Rv.
  replace  (eq_subs Fin
        (eq_subs (fun x : nat => S x = S (n + 1)) (sym_equal (S1 n))
           (refl_equal (S (n + 1)))) (fz (S n))) with
              (eq_subs Fin (S1 (S n)) (fz (S n))); auto .
  apply (eq_subs (fun x : Fin (S n + 1) => fs (tp n) =
     fincase
     (fun x : Fin (S n) =>
      fs (fincase (fun x0 : Fin n => fs (Rv x0)) (fun _ : Fin 1 => fz n)
          (eq_subs Fin (S1 n) x))) (fun _ : Fin 1 => fz (S n)) x ) 
                 (fz_eq_subs (S1  (S n)))).
  unfold fincase; simpl.
  apply  (eq_subs (fun x : Fin (S n) => fs (tp n) = fs x) (Rv_fs (fz n)) ). 
  rewrite <- (IHn (fz n)); trivial.
 Qed. 
  
 End  Alternative_Reverse.

End reversing_inductive_finite_sets.
(* Implicit Arguments fz [ ]. *)

 Section Rotate.
(** * Rotate *)

 (* rotates the first position to the last , and remainig ones
    one level up *)
 Definition rot n (i :  Fin n)  :  Fin n :=
   match i in Fin e return Fin e with
   | fz x => tp x
   | fs _ j => emb j 
   end. 

 Fixpoint rotn n : forall m, Fin m -> Fin m :=
    match n with 
    | O => fun _ i => i
    (* | S O => rot *)  
    | S n' => fun m i => (rotn n' (rot i))
    end.

 Definition rotn1 n m (i : Fin m)  := match le_lt_dec m n with
                                      | left _ => rotn (n - m) i
                                      | right _ => i
                                      end.
 Definition rotn2 n (i : Fin n) := rotn1 n i.


Lemma rotn_Sn : forall n m (i : Fin m), rot (rotn n i) = rotn (S n) i.
 Proof. 
  induction n; simpl; auto. 
  intros. rewrite (IHn m (rot i)); simpl; trivial.
 Qed.

 Lemma rotn_rotn : forall n m x (i : Fin x), rotn n (rotn m i) = rotn (n+m) i.
 Proof.
   induction n; simpl; auto.
   intros. rewrite <- (IHn m x (rot i)); trivial.
   rewrite (rotn_Sn m i); simpl; trivial.
 Qed.

 Lemma rotn_minus : forall n (i : Fin n), rotn (n - n) i = i.
 Proof.
    intros ; rewrite  minus_diag; simpl; trivial.
 Qed.

 Lemma rotn_minus1 : forall n (i : Fin n), rotn (S n - n) i = rot i.
 Proof. 
   intros n i; rewrite <- (minus_Sn_m _ _ (le_n n)); simpl.
   rewrite rotn_minus; trivial.
 Qed.

 Lemma rotn_nm : forall (n m : nat) (i : Fin m), rotn (n + m - n) i = rotn m i.
 Proof.
  induction n; simpl. intros.
  rewrite <- (minus_n_O m); trivial.
  intros. apply (IHn m i).
 Qed.


(*Lemma rotn_rot_swap : forall n m (i : Fin m), rot (rotn n i) = rotn n (rot i).
 Proof.
   induction n; simpl; trivial.
 Qed. *)

 Lemma rot_inject : forall n (i j: Fin n), rot i = rot j -> i = j.
   destruct i; destruct j using FinSn_rect; simpl; auto.
   intro. destruct (tp_emb _ H). 
   intro H; rewrite (embInject _ _ H ); trivial.
   intros H; destruct (tp_emb _ (sym_eq H)).
 Qed.

 Lemma rotn_inject : forall n m (i j : Fin m), rotn n i = rotn n j -> i = j.
 Proof.
   induction n; simpl; auto.
  intros. apply (rot_inject i j (IHn m (rot i) (rot j) H)).
 Qed.

 Lemma foo_rot (n : nat) (i : Fin n):
     foo (rot i) = match i in Fin e return nat with
             | fz m => foo (tp m)
             | fs _ j => foo (emb j)
             end. 
     destruct i; simpl; trivial.
  Qed.

 
 Definition un_rot (n : nat) :  Fin n -> Fin n := 
   match n as e return Fin e -> Fin e with
   | O => fun i => i
   | S m => fun i => match finEmtp i with
                     | isEmb i => fs i
                     | isTp  => fz m
                     end
   end.

 Lemma un_rot_inject : forall n (i j : Fin n), un_rot i = un_rot j -> i = j.
 Proof.
   destruct n; try intros; simpl. inversion i.
   destruct (finEmtp i);  destruct (finEmtp j); trivial.
   simpl in H. destruct (finEmtp (tp n));
   destruct (finEmtp (emb i)); trivial. inversion H.
   inversion H. rewrite (fsInject H); trivial. 
   simpl in *. 
   destruct (finEmtp (emb i)). destruct (finEmtp (tp n)); trivial.
   destruct (finEmtp (tp n)). inversion H.  rewrite (fsInject H); trivial.
   simpl in H. destruct (finEmtp (emb i)). destruct (finEmtp (emb i0)); trivial.
   inversion H. destruct ( finEmtp (emb i0)). inversion H.
   rewrite (fsInject H); trivial.
 Qed.


 (* rot in inverse  to un_rot *)
 Lemma rot_un_rot_id : forall n (i : Fin n), rot (un_rot i) = i.
 Proof.
   destruct i; simpl.
   destruct n; simpl; trivial.
   destruct (finEmtp (fs i)); simpl; trivial.
 Qed.

 Lemma un_rot_rot_id : forall n (i : Fin n), un_rot (rot i) = i. 
 Proof. 
   destruct i; simpl. 
   induction n; simpl; trivial.
   destruct (finEmtp (tp n)); auto.
   inversion IHn.
   induction i; simpl; trivial.
   destruct ( finEmtp (emb i)); simpl.
   inversion IHi. rewrite IHi; trivial.
 Qed.

End Rotate. 


(* Fixpoint eqFin (n :nat) (i  : Fin n): Fin n ->  bool :=
   match i in Fin e return Fin e -> bool with
  | fz _ => fun j => match finSN j with
                     | isfz => true
                     | _    => false
                     end
  | fs _ x => fun j => match finSN j with
                      | isfs x1 => eqFin x x1
                      | _ => false
                      end
  end.

 Lemma FinEq_ok : forall n (i j : Fin n), eqFin i j = true -> i = j.
 Proof.
   induction i. destruct j using FinSn_rect;  simpl; auto. 
   intro H; discriminate H.
   destruct j using FinSn_rect; simpl; auto.
    intro H; rewrite (IHi _ H); trivial.
   intro H; discriminate H.
 Qed. *)


Definition nofin (X: Type) (i : Fin 0) : X.
    intros X  i; inversion  i.
 Defined. 

Definition caseFin (n: nat) (X: Type) :  X ->  (Fin n -> X) -> Fin (S n) ->  X.
   intros n X x h i.
   destruct (finSN i) as [x | k].
   exact x.
   exact (h k).
Defined.

Definition finplus_swap (n m : nat) (i : Fin (n + m)) : Fin (m + n) :=
  match finsplit n m i with
  | is_inl a => fin_inr  m a
  | is_inr a => fin_inl n  a 
  end. 

 Lemma finsplit_unique : forall n m (i : Fin (n +m)) ( x : FinSum n m i) , 
    x = finsplit n m i.
 Proof.
    intros n m i x; destruct x.
    exact (sym_equal (finsplit_inl m i)).
    exact (sym_equal (finsplit_inr n j)).
 Defined.
 
 Lemma finsplit_inl_inr : forall (n m : nat) (i : Fin n) (j : Fin m), 
     fin_inl  m i = fin_inr n j -> False.
 Proof.
    intros n m i j; induction i; simpl.
    intro H; discriminate H.
    exact (fun x => IHi (fsInject x)).
 Qed.  

Lemma fin_inlS  (n : nat) (i j: Fin n):  forall m : nat, 
       fin_inl m i = fin_inl m  j -> fin_inl  (S m) i = fin_inl (S m) j.
Proof.
  intros n i j m; induction i; simpl; auto.  
  destruct j using FinSn_rect ; simpl; auto.
  intros H; discriminate H.  
  destruct j using FinSn_rect; simpl  ; auto. 
   exact (fun a => fs_eq (IHi j (fsInject a))).
  intro H; discriminate H.
Qed.

Lemma fin_inlP  (n : nat) (i j: Fin n):  
  forall m : nat,  fin_inl  m i = fin_inl  m j ->
        fin_inl  (pred m) i = fin_inl  (pred m) j.  
 Proof.
  intros n i j m; induction i; simpl; auto.
  destruct j using FinSn_rect ; simpl; auto.
  intros H; discriminate H.  
  destruct j using FinSn_rect; simpl  ; auto.
  exact (fun a => fs_eq (IHi j (fsInject a))).
  intro H; discriminate H.
 Qed.

Lemma fin_inrS (m : nat) (i j : Fin m) :
   forall n : nat, fin_inr n  i = fin_inr n  j ->
                     fin_inr (S n)  i = fin_inr (S n)  j.
Proof.
   destruct n; simpl; exact (fun a => fs_eq a).
Qed. 

Lemma fin_inrP (m : nat) (i j : Fin m) : 
     forall n : nat, fin_inr n  i = fin_inr n  j ->
                  fin_inr (pred n)  i = fin_inr (pred n)  j.
 Proof.
   destruct n; simpl; trivial.
   exact (fun a => fsInject a).
Qed.
 
 Require Import Arith.

Lemma fininl_embO (n : nat) ( i : Fin n) : 
    emb (fin_inl  0 i) = fin_inl  0 (emb i).
Proof.
   induction i; simpl ; auto.
   exact (fs_eq IHi).
Qed.

Lemma fin_inl_inr  (n m : nat) (i : Fin n) (j: Fin m): 
     fin_inl  m i = fin_inr n  j  -> False.
Proof.
  intros n m i j.
  induction i;  simpl.
  intro h; inversion h.
  exact (fun x => IHi (fsInject x)).
Qed.

Lemma rv_fin_inlO (n : nat) (i : Fin n) : rv (fin_inl  0 i) = fin_inl 0 (rv i).
  induction i; simpl.
  induction n; simpl ; auto.
  rewrite IHn; reflexivity.  
  rewrite <- (fininl_embO (rv i)). 
  rewrite IHi; reflexivity.
 Qed.

Lemma emb_tpm (n : nat) : emb (tp (S n)) = fz (S (S n)) -> False .
Proof.
 simpl;  intros n H. 
 discriminate H. 
Qed. 

Section FinTimes_.
  (** Products of finite types *)

 Fixpoint fpair  (n m : nat) (i : Fin n) (j : Fin m) : Fin (n * m) :=
   match i in (Fin e) return Fin (e * m) with
   | fz n => fin_inl (n * m) j
   | fs _ i1 => fin_inr m (fpair i1 j)
   end.


Inductive FinTimes (n m : nat) : Fin (n * m) -> Set :=
  |isfpair : forall (i : Fin n) (j : Fin m), FinTimes n m (fpair  i j).


 Fixpoint fintimes (n m : nat) : forall i :  Fin (n * m), FinTimes n m i :=
   match n as e return (forall i : Fin (e * m),  FinTimes e m i) with
   | O => fun i => match (fin_0_empty i) return ( FinTimes 0 m i) with end
   | S n0 => fun i => match finsplit _ _ i in (FinSum _ _ f0) 
                                    return (FinTimes (S n0) m f0) with
             | is_inl l => isfpair (fz _) l
             | is_inr r => match (fintimes _ _ r) in (FinTimes _ _ f1) 
                             return  (FinTimes (S n0) m (fin_inr m f1)) with
                           | isfpair i1 j0 => isfpair (fs i1) j0 
                           end
             end
   end. 


 (* distritutivity of times over plus *)
 Definition dist (n m o : nat) (x : Fin (n * (m + o))) : Fin (n * m + n * o) :=
   match fintimes n (m + o) x with
   | isfpair i j =>
      match finsplit m o j with
      | is_inl i0 => fin_inl (n * o) (fpair i i0)
      | is_inr j0 => fin_inr (n * m) (fpair i j0)
     end
 end.


End FinTimes_.


Definition finJmeq (n m : nat) (H : n = m) (i: Fin n) :
   JMeq i (eq_subs (fun x : nat => Fin x) H i).
 intros n m H; case H.
 intro i; auto.
Qed. 


Section JMeq_fin_inl_or_inr.
(** * Miscellaneous *)
Lemma fin_emb (n m : nat) (H : n = m) (i : Fin m) (J : Fin n) : 
     JMeq i J -> JMeq (emb i) (emb J).
 Proof.
   intros n m H; elim H.
   intros i J H0 ; elim H0; apply JMeq_refl.
 Qed.

 Lemma fin_inl_O : forall (n : nat) (i : Fin n), JMeq (fin_inl  0 i) i.
 Proof.
   intro n; induction i; simpl.
   apply  (eq_subs (fun x : nat => JMeq (fz (n + 0)) (fz x)) (sym_equal (plus_n_O n)) ).  
   apply JMeq_refl.  
   exact (fin_fs  (plus_n_O n) IHi).
 Qed.              
 
 Lemma match_simpl : forall (n m : nat) (i : Fin (n + m)) , 
             match
                match
                   match finsplit n m i with
                   | is_inl a => inl (Fin m) a
                   | is_inr a => inr (Fin n) a
                   end
                 with
                 | inl a1 => inl (Fin m) (rv a1)
                 | inr a1 => inr (Fin n) (rv a1)
                 end
               with
               | inl b => inr (Fin m) b
               | inr b => inl (Fin n)  b
               end =
             match finsplit n m  i  with
             | is_inl a => inr (Fin m) (rv a)
             | is_inr a => inl (Fin n) (rv a)
             end.
   Proof.
       intros n m i; destruct (finsplit n m i); trivial.
  Qed.

(*  Lemma match_simpl_rv : forall (n m : nat) (i : Fin (n + m)) , 
             match
                match
                   match finsplit n m (rv i) with
                   | is_inl a => inl (Fin m) a
                   | is_inr a => inr (Fin n) a
                   end
                 with
                 | inl a1 => inl (Fin m) (rv a1)
                 | inr a1 => inr (Fin n) (rv a1)
                 end
               with
               | inl b => inr (Fin m) b
               | inr b => inl (Fin n)  b
               end =
             match finsplit n m  i  with
             | is_inl a => inr (Fin m) (rv a)
             | is_inr a => inl (Fin n) (rv a)
             end.
   Proof.
       intros n m i.  rewrite (match_simpl _ _ (rv i)).
    
  destruct (finsplit n m i); trivial.
  Qed. *)

Lemma fin_Jmeq (n m : nat) (i : Fin  m) : 
     JMeq (fs (fin_inr n   i)) (fin_inr n  (fs i)).
Proof.
  induction n; simpl; auto.
  intros m i;
  apply  (fin_fs (sym_equal (plus_n_Sm n m)) (IHn m i) ).
Qed.

Lemma JM_rvEmb  (n m : nat) (i : Fin n) : 
    JMeq (emb (fin_inr m  i)) (fin_inr m  (emb i)).  
Proof.
  induction m; simpl.
  intro i; apply JMeq_refl.
  intro i; exact (fin_fs (sym_equal (plus_Snm_nSm m n)) (IHm i)).
Qed.

Lemma Jmeq_fsInject (n m : nat) (i :Fin n) (j : Fin m) :
     n = m -> JMeq (fs i) (fs j) -> JMeq i j.
Proof.
  intros n m i j H; destruct H. 
  intro H; elim (fsInject (JMeq_eq H)) ;  trivial.
Qed.

Implicit Arguments fin_inl [ ].
Implicit Arguments fin_inr [ ].
Lemma fin_Jmeq_l (n m : nat) (i : Fin n) :
    JMeq (fin_inl n (S m) i) (fin_inl (S n) m (fs i)) -> False.
Proof.
  intros n m i; induction i.
  intro H. 
  generalize (JMeq_eq (eq_subs (fun x : nat => JMeq (fz x) (fs (fz (n + m))))
              (sym_equal (plus_Snm_nSm n m)) H )).
  clear H; intro H; discriminate H.
 intro H; simpl in H.
 apply (IHi (Jmeq_fsInject (sym_equal (plus_Snm_nSm n m)) H) ).
Qed. 
   
Lemma JM_rvEmb1 (n m : nat) ( i : Fin n) : 
    JMeq (fin_inl n (S m) i ) (emb (fin_inl n m i)).
Proof.
 induction i.
 apply  (eq_subs (fun x : nat => JMeq (fz (n + S m)) (fz x))  (sym_equal (plus_Snm_nSm n m ))).
 apply JMeq_refl.
 apply (fin_fs (plus_Snm_nSm n m ) IHi).
Qed.


Lemma rvFin_inl (n m : nat) (i : Fin n) : 
     JMeq (rv (fin_inl n m i)) (fin_inr m n (rv i)).
Proof. 
  induction i. induction n; simpl.  
  induction m; simpl; auto.
  apply (fin_fs (sym_equal (S1 m)) IHm ).
  simpl in IHn. 
  apply (trans_JMeq  (fin_fs (plus_comm m (S n)) IHn) (fin_Jmeq m (tp n))).
  apply (trans_JMeq  (fin_emb (plus_comm m n) IHi) (JM_rvEmb m (rv i))).
Qed.
 
Lemma rvFin_inr (n m : nat) (i : Fin n) :  
 JMeq (rv (fin_inr m n i)) (fin_inl n m (rv i)).
Proof.
  induction m; simpl.  
  induction i; simpl.
  apply (sym_JMeq (fin_inl_O (tp n))).
  apply (sym_JMeq (fin_inl_O (emb (rv i)))). 
  apply (fun i => trans_JMeq (fin_emb (plus_comm  n m)  (IHm i) )
           (sym_JMeq (JM_rvEmb1 m (rv i)))).
Qed.


Lemma inl_inr_eq (n : nat) (i j : Fin n) : 
    JMeq (fin_inr 0 n i) (fin_inl n 0 j) -> i = j.
Proof.
  induction j; auto.
  destruct i using FinSn_rect; simpl.
  apply (eq_subs (fun x => JMeq (fs i) (fz x) -> fs i = fz n) 
         (sym_equal (plus_0_r n))) .
  intro H; apply (JMeq_eq H);auto.  
  trivial. 
  destruct i using FinSn_rect.
  intro H; rewrite (IHj i (Jmeq_fsInject (sym_equal (plus_0_r  n)) H)); trivial.
  apply  (eq_subs (fun x => JMeq (fz x) (fs (fin_inl n 0 j)) -> fz n = fs j)
           (plus_0_r n)).
  intro H; generalize (JMeq_eq H); intro h; discriminate h.
Qed.

Lemma finsumX (n m : nat) (i : Fin (n + m)) (j k : Fin (m + n))(g : k = (rv j))
              (si  : FinSum n m  i) (sk :   FinSum m n k) :  JMeq i j -> 
  match si with 
  | is_inl a => inr (Fin m) (rv a)
  | is_inr a => inl (Fin n) (rv a)
  end
  =
  match sk with
  | is_inl a => inl (Fin n) a
  | is_inr a => inr (Fin m) a
  end.  
 intros n m i j k g si sk H. 
 destruct si; destruct sk.  
 rewrite (rvdist j (sym_equal g)) in H.
case (fin_inl_inr i (rv i0) (JMeq_eq (trans_JMeq H (rvFin_inl n i0)))).
rewrite (rvdist j  (sym_equal g)) in H . 
rewrite (fin_inl_inject m i (rv j0) (JMeq_eq (trans_JMeq H (rvFin_inr m j0)))).  
rewrite (idem_rvFin j0) ; trivial.
rewrite (rvdist j (sym_equal g)) in H.
rewrite  (fin_inr_inject n j0 (rv i) (JMeq_eq (trans_JMeq H (rvFin_inl n i)))).  
rewrite (idem_rvFin i); trivial.
rewrite (rvdist j (sym_equal g)) in H.
case  (fin_inl_inr (rv j1) j0 (sym_equal (JMeq_eq (trans_JMeq H (rvFin_inr m j1))))).
Qed.


 Lemma finsplit_rv_swap : forall n m (i : Fin (n + m)) (j : Fin (m + n)),
   JMeq i j ->
    match finsplit n m (rv i) with
    | is_inl a => inl (Fin m) a
    | is_inr b => inr (Fin n) b
   end =
   match finsplit m n j with
   | is_inl a => inr (Fin n) (rv a)
   | is_inr b => inl (Fin m) (rv b)
   end.
 Proof.
   intros n m i j H; rewrite (finsumX  (refl_equal (rv i))  (finsplit m n j) 
      (finsplit n m (rv i)) (sym_JMeq H)); trivial.
 Qed.
   
 Implicit Arguments finsplit_rv_swap [n m].

   

Lemma fin_inr_inr (n x y : nat) (i : Fin y) :
  JMeq (fin_inr n (x + y) (fin_inr x y i)) (fin_inr (n + x) y i).
 Proof.
  intros n x y i; induction n; simpl; auto.
  apply (dp_rwt Fin (fun (a : nat) (fa : Fin a) => 
        JMeq (fs fa) (fs (fin_inr (n + x) y i)))
       (sym_equal (plus_assoc n x y)) (sym_JMeq IHn) ); trivial.
 Qed.

Lemma fin_inl_inrN (n m x z y : nat) (H : m + x = z + y) (i : Fin n ) (j : Fin y) 
  :  JMeq (fin_inl n (m + x) i) (fin_inr (n + z) y j) -> False .
 Proof.
  intros n m x z y H; rewrite H.
  clear H; intros .
  induction i; simpl in *.
  generalize (JMeq_eq (eq_subs (fun x : nat => JMeq (fz x) 
       (fs (fin_inr (n + z) y j))) (plus_assoc n z y) H));
  clear H; intro H.
  discriminate H .
  apply (IHi (Jmeq_fsInject (plus_assoc n z y) H )).
 Qed.
  
 Lemma fin_inr_inrPlus  (n x y a b: nat) (H : x + y  = a + b) (i : Fin (x + y))
  (j : Fin b) :  (JMeq i (fin_inr a b j) -> False) ->  
     JMeq (fin_inr n (x + y) i) (fin_inr (n + a) b j) -> False.
 Proof.
  intros n x y a b H; rewrite H.
  clear H; intros i j H.
  induction n; simpl in *; trivial. 
  apply (fun A => IHn (Jmeq_fsInject (plus_assoc n a b) A )).
 Qed. 

  Lemma finl_inl_inlx  (x z w : nat) (i : Fin x) :  
  JMeq (fin_inl x (z + w) i) (fin_inl (x + z) w (fin_inl x z i)).
Proof.
  intros; induction i;  simpl.
  apply (eq_subs (fun x => JMeq (fz x) (fz (n + z + w))) (plus_assoc_reverse n z w) ); trivial.
  apply (fin_fs  (plus_assoc_reverse n z w) IHi ).
Qed.

 Lemma fin_inl_JM (n m x : nat)(H : n = m ) (i : Fin n) (j : Fin m) :  
   JMeq (fin_inl n x i)(fin_inl m x j) -> JMeq i j.
 Proof.
  intros n m x  H; case H.
  intros i j h; rewrite (fin_inl_inject x i j (JMeq_eq h)); trivial.
 Qed.

Lemma fin_inr_inlJm (x y z : nat) (i : Fin y) :
   JMeq (fin_inr x (y + z) (fin_inl y z i)) (fin_inl (x + y) z (fin_inr x y  i)).
 Proof.
  induction x; simpl.
  intros; trivial.
   intros y z i.
  apply (fin_fs (plus_assoc_reverse x y z) (IHx y z i)).
Qed.

 Lemma fin_inl_inl_inr1 (x y k z w : nat) (H: y = k)  (i : Fin x ) (j : Fin k) :
   JMeq (fin_inl (x + (y + z)) w (fin_inl x (y + z) i))
        (fin_inl (x + k) (z + w) (fin_inr x k j)) -> False.
  Proof. 
  intros x y k z w H; case H.
  intros. induction x. inversion i.
  destruct i using FinSn_rect.
  simpl in *.
  apply (IHx i (Jmeq_fsInject
        (trans_equal
        ( trans_equal (plus_assoc_reverse x (y + z) w ) 
          (sym_equal (f_equal (plus x) (plus_assoc y z w))))
        (plus_assoc x y (z + w) )) H0)).
   simpl in H0.
    set (R := JMeq_eq (eq_subs (fun k : nat  => JMeq (fz k ) 
                 (fs (fin_inl (x + y) (z + w) (fin_inr x y j)))) 
       (trans_equal
        ( trans_equal (plus_assoc_reverse x (y + z) w )
          (sym_equal (f_equal (plus x) (plus_assoc y z w))))
        (plus_assoc x y (z + w))) H0 )).
  discriminate R.
  Qed.

 Lemma fin_inl_inr_lr (x y k w z : nat) (H : z = k + w) (i : Fin z ) (j : Fin x) :
   JMeq (fin_inr x (y + z ) (fin_inr y z i))
        (fin_inl (x + (y + k)) w (fin_inl x (y + k) j)) -> False.
 Proof.
  intros x y k w z H; try rewrite  H.   intros.
  induction j; simpl in *.
  set (R := JMeq_eq (eq_subs (fun p : nat =>  
      JMeq (fs (fin_inr n (y + (k + w)) (fin_inr y (k + w) i))) (fz p))
    ( trans_equal (plus_assoc_reverse n (y + k) w ) 
         (f_equal (plus n) (plus_assoc_reverse y k w))) H0 ));
     discriminate R.
  apply (IHj (Jmeq_fsInject
         (sym_equal (trans_equal (plus_assoc_reverse n (y + k) w ) 
        (f_equal (plus n) (plus_assoc_reverse y k w))))  H0 )).
 Qed.

 Lemma fin_inl_inrJm (x y z : nat) (i : Fin y) :
   JMeq (fin_inl (x + y) z (fin_inr x y i)) (fin_inr x (y + z) (fin_inl y z i)).
 Proof.
  induction x; simpl; auto.
   intros y z i;  apply (fin_fs (plus_assoc x y z) (IHx y z i)).
Qed.

Lemma fin_inrJm (x n m : nat) (H : n = m) (i : Fin n) (j : Fin m) :
  JMeq (fin_inr x n i) (fin_inr x m j) -> JMeq i j.
Proof.
  intros x n m H; case H.
  intros i j h; case (fin_inr_inject x i j (JMeq_eq h)); trivial.
Qed.

Lemma fin_inlJm (x n m : nat) (H : n = m) (i : Fin n) (j : Fin m) :
  JMeq (fin_inl n x i) (fin_inl m x j) -> JMeq i j.
Proof.
  intros x n m H; case H.
  intros i j h;  case (fin_inl_inject x i j (JMeq_eq h)); trivial.
Qed.

Lemma Jmeq_fin_inl_inr3 (x z k Y : nat) (H : Y = z + k) (i : Fin Y ) (j : Fin x ) :
   JMeq (fin_inr x Y i) (fin_inl (x + z) k (fin_inl x z j)) -> False.
Proof.  
 intros x z k Y H; try rewrite H.
 intros.
 induction j; simpl in *.
 set (P := JMeq_eq (eq_subs (fun q : nat => JMeq (fs (fin_inr n (z + k) i)) (fz q))
         (plus_assoc_reverse  n z k) H0 )); discriminate P.
 apply (IHj (Jmeq_fsInject (plus_assoc  n z k) H0 ))  .
 Qed.

Lemma Jmeq_fin_inr (z y x : nat) (H : y = x) (j : Fin x) (i : Fin y) :
   JMeq (fin_inr z x j) (fin_inr z y i) -> JMeq i j.
Proof.
 intros z y x H; case H; clear H.
 intros j i H; case (fin_inr_inject z j i (JMeq_eq H) ); trivial.
Qed.

Lemma fin_inl_inrZ1 ( n z y A : nat) (H : A = z + y)  (i : Fin n) (j : Fin y): 
       JMeq (fin_inl n A i) (fin_inr (n + z) y j) -> False.
Proof.
 intros n z y A H; rewrite  H.
 intros; clear H. 
 induction i; simpl in *.
  set (P := JMeq_eq (eq_subs (fun a => JMeq (fz a) (fs (fin_inr (n + z) y j)) )
              (plus_assoc n z y) H0)); discriminate P.
  apply (IHi (Jmeq_fsInject  (plus_assoc n z y) H0 )).
Qed.

End JMeq_fin_inl_or_inr.


Section ZipMaps.

 
 Definition ziP (n m : nat) : Fin (n + m) -> Fin n + Fin m.
    induction n. simpl.
    exact (fun _ i => inr _ i).
    intros m h. destruct m.
     destruct (finsplit _ _ h).
    exact (inl _ i). exact (inr _ j).
    destruct (finsplit _ _ h).
    destruct (finSN i).
    exact (inl _ (fz _ )).
    destruct i.
    exact (inr _ (fz _ )). 
    destruct (IHn _ (fin_inl m (fs i))).
    exact (inl _ (fs (fs i))). 
    exact (inr _ (fs f)).
    destruct (finEmtp j).
    exact (inr _ (tp _ )).
    destruct i. 
    exact (inl _ (tp _ )).
    destruct (IHn _ (fin_inr n i)).
    exact (inl _ (emb f)).
    exact (inr _ (fs (emb f))).
 Defined.
    

(* Eval compute in  ((ziP 2 3)  (fz 4)). *)

End ZipMaps.

Section Exponential.
  (** * Exponential of Finite Types  *)

  Fixpoint eXP (n m : nat) {struct n}:=
    match n,m with
    | O, m => 1
    | S n', m => m  * (eXP n' m)
    end. 
  Notation "m -^ n" := (eXP n m) (at level 14).

 Fixpoint finex (n m : nat) {struct n}: (Fin n -> Fin m) -> Fin (m -^ n) :=
  match n as e return ((Fin e -> Fin m) -> Fin (m -^ e)) with
  | O => fun _ => (fz 0)  
  | S n' => fun f =>
           fpair (f (fz n')) (finex (fun i => f (fs i)))
  end.

 Inductive FunView (n m : nat)  : Fin (m -^ n) -> Set := 
   lam : forall f : Fin n -> Fin m, FunView n m (finex f).
 
 Definition funView : forall n m i, FunView n m i.
    induction n; simpl.
    intros n  i; destruct (finSN i).  
    exact (lam (nofin (Fin n))).
    destruct (fin_0_empty i).
    intros m i.
    destruct (fintimes m (m -^ n) i) as [p0 ff].
    destruct (IHn m ff) as [ g ]. 
    replace (fpair p0 (finex g)) with (finex (caseFin p0 g)).
    exact (lam (caseFin p0 g)).
    destruct p0; simpl;
    repeat (rewrite (extensionality g (fun i => g i) (fun a => refl_equal (g a)));
    trivial).
 Defined.
  
 Definition fapp : forall (n m : nat), Fin (eXP n m) -> Fin n -> Fin m :=
    fun n m i => match  (funView n m i) with
                 | lam f => f
                 end.
     
 End Exponential.  


 (* some tactice for rewriting goals with fin *)

  Ltac rewriteHyp :=
  match goal with
    | [ H : _ |- _ ] => rewrite H; auto; [idtac]
  end.


 
