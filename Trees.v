Require Import Substitution Containers FiniteTypes Arith JMeq List.
Require Import MyTactics ZArith.

 Set Implicit Arguments.

(** Containers for binary trees *)

 Section Preliminaries.
  
  
   

 Inductive  Tree (A : Type) : Type :=
  | Leaf : A -> Tree A
  | Fork : Tree A -> Tree A -> Tree A.

 Definition tswap A (t : Tree A) : Tree A :=
   match t with
    | Leaf a =>  Leaf a
    | Fork l r => Fork r l
   end.

 Lemma swap_swap A (t : Tree A) : tswap (tswap t) = t.
   destruct t; simpl; trivial.
 Qed.


  Fixpoint  flatten A (t : Tree A) :  list A :=
    match t with
    | Leaf a =>  a::nil
    | Fork l r => flatten l ++ flatten r
   end.

  Fixpoint rotRight A (t : Tree A) :=
    match t with
    | Fork (Fork a b) x => Fork (rotRight a) (Fork (rotRight b) (rotRight x))
    | xs => xs
    end.
 
   Fixpoint rotLeft A (t : Tree A) :=
    match t with
    | Fork a (Fork b x) => Fork (Fork (rotLeft a) (rotLeft b)) (rotLeft x)
    | xs => xs
    end. (* *)

   Fixpoint mirror A (t : Tree A) :=
    match t with
    | Fork a b => Fork (mirror a) (mirror  b) 
    | xs => xs
    end.


  (* map and fold *)
   Fixpoint mapTree A B (f : A -> B) (t : Tree A) :=
     match t with
     | Leaf a => Leaf (f a)
     | Fork l r => Fork (mapTree f l) (mapTree f r)
     end.
 
   Fixpoint foldTree A B (f : A  -> B) (g : B -> B -> B) (t : Tree A) : B :=
     match t with
     | Leaf a => f a
     | Fork l r => g (foldTree f g l) (foldTree f g r)
     end.

 End Preliminaries.

 Section Trees.

 (** binary trees *)
  Inductive cTreeS : Set :=
  | sleaf : cTreeS
  | snode : cTreeS -> cTreeS -> cTreeS.

  Inductive cTreeP : cTreeS -> Set :=
  | phere  : cTreeP sleaf
  | pleft  : forall (l r: cTreeS) ,  cTreeP l ->  cTreeP (snode l r)
  | pright : forall (l r: cTreeS) (q : cTreeP r), cTreeP (snode l r). 

 (* CTreeS hace decidable equality  *
  Definition  cTreeS_dec : forall (x y : cTreeS), {x = y}+{x <> y}.
   induction x; destruct y.
   left; trivial.
   right; discriminate.
   right; discriminate.
   destruct (IHx1 y1); subst.
   destruct (IHx2 y2); subst.
   left; trivial.
   right; congruence.
   right; congruence.
  Defined. *)

  Inductive SnodeS (x y : cTreeS) : cTreeP (snode x y) -> Set :=
  | isl : forall z : cTreeP x, SnodeS (pleft y z)
  | isr : forall z : cTreeP y, SnodeS (pright x z).

  Inductive SnodeHere : cTreeP sleaf -> Set :=
  | justHere : SnodeHere phere.

  Definition snodeHere (i : cTreeP sleaf) : SnodeHere i :=
   match i in cTreeP t return match t return cTreeP t -> Set with
                              | sleaf => SnodeHere
                              | _ => fun _ => unit
                            end i with
   | phere => justHere
   | _ => tt
   end.

  Lemma onlyHere : forall x : cTreeP sleaf, x = phere.
   intro x; destruct (snodeHere x); trivial.
  Qed.
 
  Definition snodeS (x y : cTreeS) (i : cTreeP (snode x y)) : SnodeS i :=
   match i in cTreeP t return match t return cTreeP t -> Set with
                              | sleaf => fun _ => unit
                              | _ => @SnodeS _ _
                            end i with
   | pleft _ _ t => isl _ t
   | pright _ _ t => isr _ t
   | _ => tt
   end. 
  
  Definition ctree := ucont  cTreeP.

 Section leaf_and_fork.

   Variable X : Type.
 
   Definition noSleaf (x : X) :  cTreeP sleaf -> X :=
     fun i => match snodeHere i with
            | _ => x
            end.
 
   Definition cleaf x := uext ctree sleaf (noSleaf x).

   Definition caseTreeP  (x y : cTreeS) (f : cTreeP x -> X) (g : cTreeP y -> X) : cTreeP (snode x y) -> X :=
        fun i => match snodeS i with
                   | isl  t => f t
                   | isr t => g t
                   end.
 
   Definition cfork (x: X) (a b : Ext ctree X) : Ext ctree X :=
      match a, b with
     | uext x F,uext y G => 
         uext ctree (snode x y) (caseTreeP F G)
     end.
  
 End leaf_and_fork.
 
 
  (** swapping the nodes in binary trees *) 
  Definition swapS (x : cTreeS ) :=
  match x with
  | sleaf => sleaf
  | snode l r => snode r l
  end.

 (** the shape map is involutinve *)
  Lemma swap_inv : forall a, swapS (swapS a) = a.
   induction a; simpl; auto.
  Qed.

 (** position map for swap  *)
  Definition Pmirr  (a :cTreeS) :  cTreeP a -> cTreeP (swapS a) :=
   match a as c return (cTreeP c -> cTreeP (swapS c)) with
   | sleaf => fun H : cTreeP sleaf => H
   | snode a1 a2 =>
      fun x : cTreeP (snode a1 a2) =>
          match snodeS x with
          | isl z => pright a2 z
          | isr z => pleft a1 z
          end
   end. 

   Definition cmirP (a  : cTreeS) :  cTreeP (swapS a) ->  cTreeP a :=
   match a as c return (cTreeP (swapS c) -> cTreeP c) with
   | sleaf => fun _ : cTreeP (swapS sleaf) => phere
   | snode a1 a2 => fun b0 : cTreeP (swapS (snode a1 a2)) => Pmirr b0
   end.

   (** the swap morphism *)
   Definition cswap : cmr ctree ctree :=
     uCmr  (ucont cTreeP) (ucont cTreeP) swapS cmirP.

 (* ====================================================================================*)
   (**  Mirroring a binary tree  *)
     Fixpoint mirrorS (x : cTreeS ) :=
       match x with
       | sleaf => sleaf
       | snode l r => snode (mirrorS r) (mirrorS l)
      end.

    Lemma mirror1_inv : forall a, mirrorS (mirrorS a) = a.
      induction a; simpl; auto. rewrite IHa1. rewrite IHa2; trivial.
    Qed.


  Fixpoint cmirrP a : cTreeP (mirrorS a) -> cTreeP  a := 
   match a as c return (cTreeP (mirrorS c) -> cTreeP c) with
   | sleaf => fun H : cTreeP sleaf => H
   | snode a1 a2 => fun x : cTreeP  (mirrorS (snode a1 a2)) =>
                      match snodeS x with
                      | isl z => pright a1 (cmirrP _ z)
                      | isr z => pleft a2  (cmirrP _ z)
                      end
   end.
  
  (** The container morphism for mirror *)
   Definition cmirror : cmr ctree ctree :=
     uCmr  (ucont cTreeP) (ucont cTreeP) mirrorS cmirrP.
 
  (* we can now prove that this is involutive*)
  Lemma mirr_mir_ok a1 a2 (x : cTreeP (snode (mirrorS (mirrorS a1)) (mirrorS (mirrorS a2))))
     (y : cTreeP (snode  a1 a2)) : JMeq x y ->  match (snodeS x) , (snodeS y) with
                                  | isl p1 , isl q => JMeq p1 q
                                  | isr p1 , isr q => JMeq p1 q
                                  | _ , _  => False
                                  end.
      intros a1 a2. rewrite (mirror1_inv a1). rewrite (mirror1_inv a2).
      intros. elim H.  destruct (snodeS x); auto.
   Qed.

   Lemma mirPos_ok :
      forall (a : cTreeS) (p0 : cTreeP (comp mirrorS mirrorS a))
        (p1 : cTreeP (id cTreeS a)),
           JMeq p0 p1 -> comp (cmirrP a) (cmirrP (mirrorS a)) p0 = p1.
   Proof.
    intros. unfold comp. induction a; simpl in *. elim H. trivial.
    generalize ( mirr_mir_ok H  ). 
    destruct ( snodeS p0 ); simpl.
    destruct (snodeS p1); simpl in *.  
    intro H0; rewrite (IHa1 z z0 H0); trivial.
    intros H0; destruct H0. destruct (snodeS p1).
    intros H0; destruct H0. intros. 
    rewrite (IHa2 z z0 H0); trivial.
 Qed.
  
  (* mirroring binary trees in involutive*)
  Lemma cmir_inv :  Eqmor (m_comp cmirror cmirror) (idm ctree).
  Proof.
     contInitialize; 
      try (exact  mirror1_inv).  intros. 
      repeat ( match goal with
      | [ H : JMeq ?p ?p1 |-  context[cmirrP ?a (cmirrP (mirrorS ?a) ?p)]]  => 
              let mrp := constr:(mirPos_ok H) in apply mrp
       | |- context[comp] => unfold comp
      end). 
  Qed.


 (* ============================================================================*)

 (* laborious container proof that  mirror involutive *) 
 (* Lemma cmir_inv :  Eqmor (m_comp cmirror cmirror) (idm ctree).
 Proof.
   unfold m_comp; unfold cmirror; unfold idm.
   unfold comp; unfold id;
   apply morq; simpl. 
   exact  mirr_inv . 
   intros. destruct a;  simpl in p0.
   elim  H. simpl.
   destruct (snodeHere p0); trivial.
   simpl in p0.  elim H.  simpl.
   destruct (snodeS p0); trivial.
 Qed. *)

 (** flattening a tree into a list  *)
  Fixpoint Sum (s : cTreeS ) : nat :=
   match s with
   | sleaf => 1
   | snode l r => Sum l + Sum r
   end.

  Fixpoint cflatten_p (s : cTreeS) :  Fin (Sum s) -> cTreeP s :=
   match s as e return Fin (Sum e) -> cTreeP e with
   | sleaf => fun _ => phere
   | snode l r => fun i => match (finsplit  (Sum l) (Sum r)  i) with
                           | is_inl i => pleft r (cflatten_p l i)
                           | is_inr j => pright l (cflatten_p r j)
                           end
   end.         

  (** the flatten morphism for data trees  *)         
  Definition ctflat :=
      uCmr (ucont cTreeP) (ucont Fin) Sum cflatten_p.

 Fixpoint cflatten_inv (s : cTreeS) :  cTreeP s ->  Fin (Sum s)  :=
   match s as e return cTreeP e ->  Fin (Sum e) with
   | sleaf => fun _ => (fz _)
   | snode l r => fun i => match (snodeS (x := l) (y := r)   i) with
                           | isl  i => fin_inl (Sum r) (cflatten_inv  i)
                           | isr  j => fin_inr (Sum l) (cflatten_inv  j)
                           end
   end.  
  
 (* cTreePs is isomorphic to Fin (Sum s) *)
Lemma cflattL  (s : cTreeS) (i : cTreeP s) : cflatten_p _ (cflatten_inv i) = i.    
  Proof.
    induction s; simpl.  intro snh; destruct (snodeHere snh); trivial.
    intro slr.   destruct (snodeS slr); FSimpl. 
    rewrite (IHs1 z); trivial.
    rewrite (IHs2 z); trivial.
  Qed.

 Lemma cflattInvL  (s : cTreeS) (i : Fin (Sum s)) : cflatten_inv  (cflatten_p _ i) = i.    
  Proof.
    induction s as [ | bb IHbb cc IHcc ];  intros; simpl in *. FSimpl. 
    destruct (finsplit _ _ i); simpl.
    rewrite (IHbb i); trivial.
    rewrite (IHcc j); trivial.
 Qed.
(*

*) 

    


  Section treeFold.
  (* container fold for binary trees  *)

     Section tfoldSmap.
     (* The shape map for the folds *)
     Variables (S' A : Type) (a0 : S' -> A) (f0 : S' * (A * A) -> A).

     Fixpoint tld (n : cTreeS) (s  :S') {struct n} : A :=
       match n with
       | sleaf => a0 s
       | snode l r => f0 (s , (tld l s, tld r s))
       end.

     End tfoldSmap.

     Section cTreeFolds.

     (* fold on contaienrs for trees  -- this is not correct! *)
     Variables (S' A : Ucontainer)
             (a : cmr S' A)
             (F : cmr (cont_prod S' (cont_prod A A)) A).

     Definition tGenfold : cmr (cont_prod S' (ucont cTreeP)) A.
       refine (uCmr ( cont_prod S' (ucont cTreeP)) A 
                (fun sa =>  tld (v a) (v F) (snd sa) (fst sa ) ) _ ); simpl.
       destruct a0; simpl.
       induction c; simpl in *.
       exact (fun i =>  inl (cTreeP sleaf) (g a s i)).
       intro i; destruct (g F  (s, (tld (v a) (v F) c1 s, 
                         tld (v a) (v F) c2 s)) i);
       simpl in *. exact (inl (cTreeP (snode c1 c2)) p).
       destruct p as [p1 | p2].
       destruct (IHc1 p1) as [l1 | l2].
       exact (inl ( cTreeP (snode c1 c2)) l1).
       exact (inr ( p S' s) (pleft _ l2)).
       destruct (IHc2 p2) as [l1 | l2].
       exact (inl (cTreeP (snode c1 c2)) l1).
       exact (inr ( p S' s) (pright _ l2)).
     Defined.

    End  cTreeFolds. 

 End treeFold.
 
 End Trees.

 
 (* Exporting Notation and tactics *)

  Ltac treeDest_aux := 
     (* let treeDest_aux a :=
           match goal with
           | [ p0 : cTreeP (comp mirrorS mirrorS a) ,
                p1 : cTreeP (id cTreeS a) |- _] =>
             match goal with 
             | [ _ : JMeq p0 p1 |- _ ] => 
                  let mirpos := constr:(mirPos_ok _ p0 p1 _) in
                    rewrite mirpos
             end
           end in *)
    match goal with
    | |- forall _, _ => intros
    | |- context[comp] => unfold comp
      (* this rewrite is for shapes *)
    |  x : cTreeP (snode _ _  ) |- context [?i] => 
         match x with
         | i =>  let H := constr:(snodeS x) in destruct H
          end
    |  x : cTreeP sleaf |- context [?i] => 
         match x with
         | i =>   let H := constr:(snodeHere x) in destruct H
         end
    | |- context [swapS (swapS ?i)] =>
           let Eq := constr:(swap_inv i) in
             first [rewrite Eq in * ] (*| rewrite <- Eq in *] *)
    | |- context [mirrorS (mirrorS ?i)] =>
           let Eq := constr:(mirror1_inv i) in
             first [rewrite Eq in *] (* | rewrite <- Eq in *] *)
    | [ H : JMeq ?p ?p1 |-  context[cmirrP ?a (cmirrP (mirrorS ?a) ?x)]]  => 
              let mrp := constr:(mirPos_ok H) in apply mrp
    end.

  Ltac rewr_simpl :=
      match goal with
      | a : cTreeS |- _ =>
          match goal with
          | id : context [a] |- _ => destruct a; simpl in *
          end
      end.

 (* *)
  Ltac JMeq_elim :=
    match goal with
    | x : ?A , y : ?A |- _ =>
         match goal with
         | H : JMeq x y |- _ => elim H; clear H
         end 
    end.

  Ltac treeDest :=
     repeat ((JMeq_elim || treeDest_aux || rewr_simpl); auto).

  Tactic Notation "contInitialise" :=  repeat (contInit cmirror).
  Tactic Notation "Tcontainer" :=  contInitialise; treeDest. 

 Lemma test2 :  Eqmor (m_comp cswap cswap) (idm ctree).
      Tcontainer.
 Qed.

Lemma test1 :  Eqmor (m_comp cmirror cmirror) (idm ctree).
   (*contInitialize.  treeDest. treeDest. *)
     Tcontainer.
 Qed.


