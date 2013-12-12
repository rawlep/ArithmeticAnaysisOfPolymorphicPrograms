Require Import Arith JMeq FiniteTypes Substitution.
Require Import Containers Max Eqdep. 

(** * Vectors - lists with finite length *)

Set Implicit Arguments.

Section Vectors.
 
 Variable X : Type.

 Inductive Vec  : nat -> Type :=
  | vnil : Vec 0
  | vcons : forall (n : nat) , X ->  Vec n -> Vec (S n).

 (** concatenating two vectors *)
 Fixpoint vPlus (n m : nat)(i : Vec n) (j :  Vec m) {struct i}:  Vec (n + m) := 
 match i as e in (Vec n) return (Vec (n + m)) with
 | vnil => j
 | vcons _ x i' => vcons  x (vPlus i' j)
 end.

 (** concatenation is commutative  *)
 Lemma vPlus_comm (n m nm : nat) (i : Vec n) (j : Vec m) (k : Vec nm) :
  JMeq (vPlus (vPlus i j) k) (vPlus i (vPlus j k)).
 Proof.
  induction i; simpl; auto.
  intros j k. 
  exact (dp_rwt Vec 
         (fun (z : nat)  (px : Vec z) => 
             JMeq (vcons x px)
                      (vcons x (vPlus i (vPlus j k))) )
         (plus_assoc n m nm) (sym_JMeq (IHi j k))
        (JMeq_refl (vcons x (vPlus i (vPlus j k))))
         ).
 Qed.

 (** case non-standard eliminators for Vec 0 and Vec (S n)  *)
 Inductive VNil : Vec 0 -> Type := isvnil : VNil vnil.

  Inductive VCons (n : nat) : Vec (S n) -> Type :=
   isvcons : forall (a :X ) (i : Vec n), VCons (vcons a i) .

  Definition vNil (i : Vec 0): VNil i :=
  match i in Vec t return match t return Vec t -> Set with
                               | O => @VNil
                               | _ => fun _ => unit
                               end i with
  | vnil => isvnil
  | _ => tt
  end.

  Definition vCons (n : nat) (i : Vec (S n)) : VCons i :=
   match i in Vec t return match t return Vec t -> Type with
                           | S _ => @VCons _
                           | _   => fun _ => unit
                           end i with
  | vcons _ x j => isvcons x j
  | _ => tt
  end.


 (** compute a constant vector of some required size*)
 Fixpoint vec (n : nat) (x: X) : Vec n :=
   match n as e return (Vec e) with
   | O => vnil
   | S n' => vcons x (vec n' x) 
   end.

 (** head and tail  *)
 Definition vhead n (i : Vec (S n)) : X :=
    match vCons i with
    | isvcons a _ => a
    end.

 Definition vtail n (i : Vec (S n)) :  Vec n :=
  match vCons i with
  | isvcons _ a => a
  end.

 (** and dually, first and last *)
  Fixpoint vfirst_aux n a (v : Vec n) : Vec n :=
    match v in Vec e return (Vec e)  with
    | vnil => vnil
    | vcons _ x xs => vcons a (vfirst_aux x xs)
    end.

  (* removes the last element of a vector *)
  Definition vfirst n (v : Vec (S n)) := vfirst_aux (vhead v) (vtail v).
 
  Fixpoint vlast_aux n a (v : Vec n) :=
    match v with
    | vnil => a
    | vcons _ x xs => vlast_aux x xs
    end.

  (* returns the last element of a vector  *)
  Definition vlast n (v : Vec (S n)) := vlast_aux (vhead v) (vtail v).

  (* Vsnoc - adds an element to the end of a vector  *)
  Fixpoint vSnoc n (a : X) (v : Vec n) : Vec (S n) :=
     match v in Vec n return Vec (S n) with
     | vnil => vcons a vnil  
     | vcons _ x xs => vcons x (vSnoc a xs)
     end.

 (** reverse a vector  *)
  Fixpoint vrev n (v : Vec n) : Vec n :=
    match v in Vec n return Vec n with
    | vnil => vnil
    | vcons _ b bs => vSnoc b (vrev bs)
    end.

 (**  
-----
Some properties of vrev, vSnoc, vfirst and vlast *)
(* vrev is involutive *)
  Lemma vrevSnoc : forall  n (x : X) (v : Vec n), vrev (vSnoc x v) = vcons x (vrev v).
  Proof.
    induction v; simpl; auto.
    rewrite IHv; simpl; trivial.
  Qed.

 (** vrev is involutive  *)
 Lemma vrev_inv : forall n (v : Vec n), vrev (vrev v) = v.
 Proof. 
   induction v; simpl; trivial.
   rewrite (vrevSnoc x (vrev v)); rewrite IHv; trivial.
 Qed.

 Lemma vlast_vcons : forall  n (x : X) (v : Vec (S n)), vlast (vcons x v) = vlast v. 
 Proof.
   intros. destruct (vCons v); unfold vlast; unfold vhead; unfold vtail; simpl; trivial.
 Qed.

 Lemma vfirst_vcons : forall  n (x : X) (v : Vec (S n)), vfirst (vcons x v) = vcons x (vfirst v). 
 Proof.
   intros. destruct (vCons v); unfold vfirst; unfold vhead; unfold vtail; simpl; trivial.
 Qed.
 
 Lemma vlast_vSnoc : forall  n (x : X) (v : Vec n), vlast (vSnoc x v) = x.
  induction v; simpl; trivial;  rewrite (vlast_vcons x0 (vSnoc x v)); trivial.
 Qed.

 Lemma vfirst_vSnoc : forall  n (x : X) (v : Vec n), vfirst (vSnoc x v) = v.
  induction v; simpl; trivial. rewrite (vfirst_vcons x0 (vSnoc x v)); 
  rewrite IHv; trivial.
 Qed.

 Lemma vlast_rev n (v : Vec (S n)):  vhead v = vlast (vrev v).
 Proof. 
    intros n v; unfold vhead;  destruct (vCons v);  simpl.
    rewrite (vlast_vSnoc a (vrev i));  trivial.
 Qed.

 Lemma vfirst_rev n (v : Vec (S n)):  vrev (vtail v) = vfirst (vrev v).
 Proof. 
   intros n v; unfold vtail; destruct (vCons v); simpl. rewrite (vfirst_vSnoc a  _); trivial.
 Qed.
  
 (** fold for vectors *)
 Fixpoint vfold n ( B : Type) (f : X -> B -> B) (b : B) (v : Vec  n) : B :=
   match v with
   | vnil => b
   | vcons _ a ass => f a (vfold f b ass)
   end.

  
  (** Non-standard eliminator for  View (n + m) *)
  Inductive vPlusView (n m : nat) : Vec (n + m) -> Type :=
   | vplus : forall (i : Vec n) (j : Vec m), vPlusView n m (vPlus i j).
  
  Fixpoint vplusView (n m : nat) : forall i : Vec (n + m), vPlusView n m i :=
    match n as e return (forall i : Vec (e + m), vPlusView e m i) with
    | O    => fun i => vplus vnil i
    | S n' => fun i => 
          match (vCons i) in (VCons k) return (vPlusView (S n') m k) with
          | isvcons a i0 => let v0 := vplusView _ m i0 in
             match
             v0 in (vPlusView _ _ v1) return (vPlusView (S n') m (vcons a v1))
             with
             | vplus i1 j => vplus (vcons a i1) j
             end
         end
    end.


 (* Definition vTimes n m (i : Vec n) (j :  Vec m) : Vec (n * m).
    intros n m i; induction i; simpl.
    exact (fun _ => vnil ).
    intros h. exact (vPlus h (IHi h)).
  Defined. *)

 (*
  Fixpoint vTimes n m (i : Vec n) (j : Vec m)  : Vec (n * m) :=
    match i in Vec e return  Vec (e * m) with
    | vnil =>  vnil
    | vcons _ _ i1 =>  vPlus j (vTimes  i1 j)
    end.              
  
Inductive VecTimes (n m : nat)  : Vec (n * m) -> Type :=
  |isVecPair : forall (i : Vec n) (j : Vec m) , VecTimes n m (vTimes i j).

 Definition vectimes ( n m : nat)  : forall i : Vec (n * m), VecTimes n m i.
    cut (forall m  (i : Vec 0), VecTimes 0 m i). intro.
    induction n. simpl in *.  exact (X0 ).
    intros. cut (Vec (S n * m) -> Vec (S (n * m))). 
    intro H. simpl in *. destruct (vCons (H i)). clear i0.
    destruct (vplusView m (n * m) i).
    destruct (IHn m j).  set  (isVecPair (m :=m)  (vcons a i0) ). simpl in v.
    exact v. 
    simpl in i.
    
    cut ( forall   (i : Vec 0) ( j : Vec m) , VecTimes 0 m (vTimes i j)  -> VecTimes 0 m i).
    intros. induction m; simpl.
    exact (X0 i vnil (isVecPair (m := 0)  i vnil) ).

  *)

 (* decomposiiton i nterms of vhead and vtail *)
 Lemma vec_decompose : forall n (v : Vec (S n)), v = vcons (vhead v) (vtail v).
 Proof.
   intros n v; destruct (vCons v); auto.
 Qed.  

  (* decompositon in terms of vSnoc, vlast and vfirst *)
   Lemma vVsnoc n (v : Vec (S n)) : v = vSnoc (vlast v) (vfirst v).
   Proof.
     intros n v; destruct (vCons v) . generalize a; unfold vlast; unfold vfirst;
     unfold vhead; unfold vtail; simpl. 
    induction i ; simpl; trivial. intros; rewrite (IHi x); trivial.
  Qed.


 (** * Equality  *)
 Definition vecEq1 (n : nat) (H : forall x y : X, {x = y}+{x <> y}) (i j: Vec n) : bool.
  intros n H i; induction i. intro j; destruct  j.
  exact true. exact false. intro j; destruct (vCons j).
  destruct (H x a) as [l | r]. exact (IHi i0). exact false.
 Defined.

 Lemma VecEq1_sym (n : nat) (H : forall x y : X, {x = y}+{x <> y}) (i j: Vec n) :
   vecEq1 H i j = true -> vecEq1 H j i = true.
 Proof.
   induction i. intro j; destruct (vNil j); trivial.
   intro j; destruct (vCons j); simpl.
   destruct (H x a); subst. intros. destruct ( H a a).
   apply (IHi i0 H0). case (n0 (refl_equal a)).
   intro h; discriminate h.
 Qed.

 Lemma vecEq1_and (n m : nat) (H :forall x y : X, {x = y}+{x <> y}) (i i1 : Vec n) (j j1 : Vec m) :
  vecEq1 H i i1 = true -> vecEq1 H j j1 = true -> vecEq1 H (vPlus i j) (vPlus i1 j1) = true.
 Proof.
   induction i. intros. destruct (vNil i1); simpl in *. trivial.
   intros. destruct (vCons i1); simpl in *.
   destruct ( H x a). exact (IHi i0 j j1 H0 H1). exact H0.
 Qed.

 Lemma vec_and_Eq1 (n m : nat) (H :forall x y : X, {x = y}+{x <> y}) (i i1 : Vec n) (j j1 : Vec m) :
  vecEq1 H (vPlus i j) (vPlus i1 j1) = true -> vecEq1 H i i1 = true /\ vecEq1 H j j1 = true .
 Proof.
   induction i. intros. destruct (vNil i1); simpl in *. auto.
   intros. destruct (vCons i1); simpl in *.
   destruct ( H x a). exact (IHi i0 j j1 H0). 
   discriminate  H0.
 Qed.

 Fixpoint vecEqBool (n : nat) ( H : X -> X -> bool) (i  : Vec n) {struct i} : Vec n -> bool :=
   match i in Vec e return Vec e -> bool with
   | vnil => fun _ => true
   | vcons _ a ls => fun x => match vCons x with 
                            | isvcons b bs => if H a b then 
                                                 vecEqBool H ls bs
                                               else false
                            end
   end. 

 Lemma vecEqBool_and (n m : nat) (H : X -> X -> bool) (i i1 : Vec n) (j j1 : Vec m) :
  vecEqBool H i i1 = true -> vecEqBool H j j1 = true ->  vecEqBool H (vPlus i j) (vPlus i1 j1) = true.
 Proof.
   induction i. intros. destruct (vNil i1); simpl in *. trivial.
   intros. destruct (vCons i1); simpl in *.
   destruct ( H x a). exact (IHi i0 j j1 H0 H1). exact H0.
 Qed.

 Lemma VecInj1 : forall (n : nat) (a a1 : X) (i j : Vec n), vcons a i = vcons a1 j -> a = a1.
  Proof. 
    intros. injection H; auto.
  Qed.

 Definition vecEqDec (n : nat) (H : forall x y : X, {x = y}+{x <> y}): forall (i j: Vec n), {i = j}+{i <> j} .
   induction i. intro j; destruct (vNil j).
   left; trivial. intro j; destruct (vCons j).
   destruct (H x a); subst. destruct (IHi i0); subst. left ;trivial. 
   right. 
    cut (forall (n : nat) (i j : Vec (S n)),
    i = j -> vtail i = vtail j). intros.
   intro h;  set (r := H0 n (vcons a i) (vcons a i0) h); simpl in r.
   case (n0 r). intros. case H0; trivial.
   right. intro h; case (n0 (VecInj1 h)). 
 Defined.
 
 Definition vecEq (n m : nat) (H : forall x y : X, {x = y}+{x <> y}) (i : Vec n) (j : Vec m) : bool.
  intros n m; destruct (eq_nat_dec n m) as [l | r].
  destruct l. exact (fun H i j => vecEq1 H i j).
  intros; exact false.
 Defined.

  Definition vecEq_bool (n m : nat)  (H : X -> X -> bool) (i : Vec n) (j : Vec m) : bool.
  intros n m; destruct (eq_nat_dec n m) as [l | r].
  destruct l. exact (fun H i j => vecEqBool H i j).
   exact (fun _ _ _ => false).
 Defined.

 Definition VecEQt (n  : nat) (H : forall x y : X, {x = y}+{x <> y})(i j: Vec n) :  vecEq1 H i j = true -> vecEq H i j = true.
 Proof.   
  intros. unfold vecEq. replace (eq_nat_dec n n) with (left (n <> n) (refl_equal n)); auto. 
  destruct (eq_nat_dec n n); trivial. rewrite (UIP_refl nat n e); trivial.
  case (n0 (refl_equal n)).
 Defined.

 Definition eqvecEqn (n : nat) (H : forall x y : X, {x = y} + {x <> y}) (i j : Vec n) : vecEq H i j = true -> i = j.
 Proof.
   induction i. intro j;  destruct (vNil j); trivial. 
   intros. destruct (vCons j). unfold vecEq in H0.
   destruct (eq_nat_dec (S n) (S n)).
   rewrite  (UIP_refl nat (S n) e) in H0.
   destruct (H x a); simpl in *; subst.
   destruct (H a a). case (IHi i0 (VecEQt H i i0 H0)); trivial.
   discriminate H0. destruct (H x a) as [l | r ]. case (n0 l).
   discriminate H0.
   discriminate H0.
 Defined.
 
  Definition eqvecEq (n m : nat) (H : n = m) (H : forall x y : X, {x = y} + {x <> y})
   (i : Vec n) (j : Vec  m) : vecEq H i j  =  true ->  JMeq i  j.
    intros n m H; case H. intros. case (eqvecEqn H0 i j H1); trivial.
  Defined.

    
  Lemma VeqInj2 : forall (n : nat) (v1 v2 : Vec (S n)), v1 = v2 -> vhead v1 = vhead v2 /\ vtail v1 = vtail v2.
  Proof. 
    intros until v2. intro H; destruct H. 
    destruct (vCons v1); simpl. auto.
  Qed.

End Vectors.

  Fixpoint vmap (n : nat)  (A B : Set) (f : A -> B) (i : Vec A n) {struct i} :
     Vec B n :=
   match i in (Vec _ e) return (Vec B e) with
   | vnil => vnil B
   | vcons _ x xs => vcons (f x) (vmap f xs)
   end.
 
 Lemma vplusMap  (A B : Set) (n m : nat)  (f : A -> B)
  (i : Vec A n) (j : Vec A m) :  vPlus (vmap f i) (vmap f j) = vmap f (vPlus i j).
 Proof. 
   induction i; simpl; trivial.
   intros. rewrite (IHi j); trivial.
 Qed.

 Fixpoint vApp (X Y : Type) (n : nat) (i :  Vec (X -> Y) n ) {struct i} :
      Vec X n -> Vec Y n :=
   match i in (Vec _ e) return Vec X e -> Vec Y e with
   | vnil => fun _ => vnil Y
   | vcons _ F fi => fun i => 
                  match vCons i with
                  | isvcons x xs => vcons (F x) (vApp fi xs)
                  end
   end. 

 (** Matrix transpose*)
 Fixpoint vXpose (X : Type) (i j :nat) (a : Vec (Vec X j) i) {struct a} : Vec (Vec X i) j :=
  match a in (Vec _ e1) return Vec (Vec X e1) _ with
  | vnil => vec j (vnil X)
  | vcons n x xs => 
       vApp (vApp (vec j (vcons (X := X) (n := n) )) x) (vXpose xs)
  end. 


Section VecFin.
(** Vectors and Finite Sets *) 
 Fixpoint vecfin (A : Type) (n : nat) (i : Vec A n) {struct i} :  Fin n -> A :=
   match i in (Vec _ e) return (Fin e -> A) with
   | vnil  => fun x =>  match (fin_0_empty x) return A with end
   | vcons _ a i => fun j =>  match finSN j with
                            | isfz => a
                            | isfs j' => vecfin i j'
                            end
   end.
  
 Fixpoint finVec A (n : nat) {struct n} : (Fin n -> A) -> Vec A n :=
  match n as e return ((Fin e -> A) -> Vec A e) with
  | O => fun _ => (vnil A)
  | S n'  => fun f => vcons (f (fz n')) (finVec (fun i => f (fs i)))
  end.


(* Isomorphism extends to dependent sums : \Sigma n : nat. Fin n -> X *)
(* Here we use the extension of a container for lists *)
 Definition extVec (i : Ext (ucont Fin) nat) : Vec nat (u i) := finVec (f i).

 Definition vecExt  (n: nat) (i : Vec nat n) := uext (ucont Fin) n (vecfin i) .

 Lemma finVecfin A (n : nat) : forall (i : Vec A n), finVec (vecfin i) = i.
 Proof.
   induction i; simpl; trivial.
   rewrite <- (extensionality (vecfin i) (fun i0 => vecfin i i0) (fun x => refl_equal (vecfin i x))). 
   pattern i at 2; rewrite <- IHi; trivial.
 Qed.

 Lemma vecFinVec A (n : nat):
   forall (i : Fin n -> A), vecfin (finVec i) = i.
   induction n; simpl; auto.
   intros.  apply (extensionality (fun x : Fin 0 => match fin_0_empty x return A with
                     end) i).
   intro a; inversion a. intros.  apply extensionality .
   intro a; destruct (finSN a); trivial.
   rewrite (IHn (fun x => i (fs x))); subst; trivial. 
 Qed.

 Lemma finVecEQ A (n : nat): forall  (i j : Fin n -> A), (finVec i) = (finVec j) ->  i = j.
   intros A n i j H; set (r := f_equal (vecfin (A := A) (n := n)) H); simpl in r.
   rewrite (vecFinVec i) in r; rewrite (vecFinVec j) in r; trivial.
 Qed.

 Lemma vecJmeq X (n m : nat) (h : n = m)  (F : Fin n -> X) (G : Fin m -> X) : JMeq (finVec F) (finVec G) -> JMeq F G.
  intros X n m h; destruct h. intros F G h.
  replace F with (vecfin (finVec F)).  replace G with (vecfin (finVec G)).
  case (JMeq_eq h); trivial. apply vecFinVec. apply vecFinVec.
 Defined.

 Lemma ExtVecN X (n m : nat) (H : n = m) (F : Fin n -> X) (G : Fin m -> X) :
   (forall (x : Fin n) (x1 : Fin m), JMeq x x1 -> JMeq (finVec F) (finVec G))-> JMeq F G.
   intros X n m h; destruct h.
   intros F G H. apply (dextensionality Fin (refl_equal n) F G) .
   intros x y h; case (JMeq_eq h). case (finVecEQ F G (JMeq_eq (H x y h))); trivial.
  Qed.

 Lemma finVecJMeq A (n m : nat) (H : n = m)
                 (i : Fin n -> A) (j : Fin m -> A)
                 (H0 : JMeq (finVec i) (finVec j)) (ix : Fin n) (jx : Fin m):
                 JMeq ix jx -> i ix = j jx.
 Proof.
   intros A n m H; case H. intros F G H0; case (finVecEQ F G (JMeq_eq H0)).
   intros i j H1; case (JMeq_eq H1); trivial.
 Qed.

  (** Indexing a vector by a fnite type *)
  Fixpoint vecIn X n (i : Fin n) : Vec X n -> X :=
    match i in (Fin e) return Vec _ e -> X with
    | fz _ => fun v => match vCons v with
                       | isvcons x _ => x
                       end
    | fs _ i => fun v => match vCons v with
                       | isvcons _ j => vecIn i j
                       end
    end.

   (** indexing a vector from the last element *)
  Definition rev_ind X  (n : nat) (i : Fin n) (v : Vec X n) := vecIn (rv i) v.

  (* this belongs to the vectors file *)
  Lemma vecfin_emb A n (i : Fin n) (v : Vec A (S n)) : vecfin v (emb i) = vecfin (vfirst v) i.
    induction i; intros; repeat (match goal with
                                | [ v : Vec _ (S _ ) |- _ ] =>  destruct (vCons v)
                                end); simpl. unfold vhead; simpl; trivial.
     generalize (IHi (vcons a0 i0)); simpl. intro h; rewrite h.
    unfold vfirst; unfold vhead; unfold vtail; simpl; trivial.
  Qed.

  Lemma vecfin_tp A n  (v : Vec A (S n)) : vecfin v (tp n) =  vlast v.
  Proof.
    induction n; intros ; repeat (match goal with
                                | [ v : Vec _ (S _ ) |- _ ] =>  destruct (vCons v)
                                | [ v : Vec _ 0 |- _ ] =>  destruct (vNil v)
                                end); simpl.  unfold vlast; simpl; trivial.
    generalize (IHn (vcons a0 i)); simpl. intro h; rewrite h.
   unfold vlast; unfold vhead; unfold vtail; simpl; trivial.
  Qed.

End VecFin.

Section Tuples.

 Variable A: Type.
 (** * Vectors as Tuples *)
  Fixpoint Tuple (n:nat){struct n}: Type :=
  match n with
  O => unit
  | (S n') => (A*(Tuple n'))%type
  end.

 (* Vector is a n-tuple *)
 Fixpoint tup2vec n :  Tuple n -> Vec A n :=
   match n as n return Tuple n -> Vec A n with
   | O => fun _ => vnil _
   | S m => fun tp => vcons (fst tp) (tup2vec _ (snd tp))
   end.

 Fixpoint vec2tup n (i : Vec A n) : Tuple n :=
    match i in (Vec _ e) return Tuple e with
    | vnil => tt
    | vcons _ x xs => (x, (vec2tup xs))
   end.
  
 Fixpoint tuple_proj (n:nat){struct n}: forall k:nat, k<n -> Tuple n -> A :=
  match n return (forall k:nat, k<n -> Tuple n -> A) with
  O => fun (k:nat)(h:k<O)(v:Tuple 0) =>
         match (lt_n_O k h) return A with end
  | (S n') => fun k:nat =>
              match k return (k<(S n') -> Tuple (S n') -> A) with
                O => fun (h:0<(S n'))(v:Tuple (S n')) => (fst v)
              | (S k') => fun (h:S k' < S n')(v:Tuple (S n')) =>
                            (tuple_proj (lt_S_n k' n' h) (snd v))
              end
 end.

End Tuples.

Section Function_Tuples.

   Variables A B: Type.

   Fixpoint mult_app (n:nat){struct n}: Tuple (A->B) n -> A -> Tuple B n :=
     match n return Tuple (A->B) n -> A -> Tuple B n with
       0 => fun (f:unit)(a:A) => tt
       | (S n') => fun (f:(A->B)*(Tuple (A->B) n')) (a:A)
                     => let (f0,f'):=f in (f0 a, mult_app n' f' a)
     end.

End Function_Tuples.

 (** * Exporting notations and tactics *)
 
 (* Infix " >>> " := vmap (at level 20) : Vec_scope.
  Infix " `+` " := vPlus (at level 20) : Vec_scope.
  Notation "v !! i" := (vecfin v i) (at level 20) : Vec_scope. 
  Open Scope Vec_scope. *)

  (* decompose vCons, VNil and Vplus automatically *)
  Ltac vNil_vcons H x  :=
        match x with
        | context [?a + ?b] =>  destruct (vplusView a b H)
        | 0    => destruct (vNil H)
        | _ => destruct (vCons H)
        end.
  
   Ltac vecRwt :=
      match goal with
      | [ |- context[vrev (vrev ?v)]] => let R := constr:(vrev_inv v) in rewrite R
      | [|- context[vrev (vSnoc ?x ?v)]] => let R := constr:(vrevSnoc x v) in rewrite R
      | [ |- context[vlast (vcons ?x ?v)]] => let R := constr:(vlast_vcons x v) in rewrite R
      | [ |- context[vlast (vSnoc ?x ?v)]] => let R := constr:(vlast_vSnoc x v) in rewrite R
      | [ |- context[vfirst (vcons ?x ?v)]] => let R := constr:(vfirst_vcons v) in rewrite R
      | [ |- context[vfirst (vSnoc ?x ?v)]] => let R := constr:(vfirst_vSnoc x v) in rewrite R
      | [ |- context[vlast (vrev ?v)]] => let R := constr:(vlast_rev v) in rewrite <- R
      | [ |- _] => 
            match goal with
            | [ |- context[vPlus (vmap ?F v) (vmap _ ?h)]] =>
                     let R := constr:(vplusMap F v h) in rewrite R
             end
      end. 

   (* simpliy cases with vhead, vtail, vplus and do rewrites *)
  
   Ltac vSimp_aux :=
        match goal with
       | [ H : Vec _ ?n |- _ ] => vNil_vcons H n
       | [ |- context[vhead v]] =>  unfold vhead; simpl
       | [ |- context[vtail v]] =>  unfold vhead; simpl
       | [ H : ?X |- _ ] => match X with
                            | context[vhead] =>  unfold vhead in *; simpl in *
                            | context[vtail] =>  unfold vhead in *; simpl in *
                            | context[vfirst] =>  unfold vfirst in *; simpl in *
                            | context[vlast] =>  unfold vlast in *; simpl in *
                            end
       end. 
   Ltac vSimp := repeat vecRwt; repeat vSimp_aux.
