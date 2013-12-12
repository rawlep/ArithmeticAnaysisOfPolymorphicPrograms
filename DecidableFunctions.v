Require Import FiniteTypes Arith MyTactics MPiecewise  VNArith.  


(* Top level definitions  of ellipsis functions using natural numbers *)

 Set Implicit Arguments.

 (** * Top level definitions *)



  (** Linear function in n variables.   *)
 Inductive lfun (n : nat)  : Set :=
   | adD :  lfun n -> lfun n -> lfun n
   | suB :  lfun n -> lfun n -> lfun n
   | vr :  Fin n -> lfun n
   | cnst : nat ->  lfun n.

 (** interpretation  *) 
 Fixpoint evl n (i : lfun n) (v : Vec nat n) :  nat :=
   match i with 
   | cnst n =>  n
   | vr j =>  vecfin v j
   | adD l r => evl l v + evl r v
   | suB l r  => evl l v - (evl r v )
   end.

 (** composition *)
 Fixpoint cmp n (i j : lfun (S n)) : lfun (S n) :=
   match i with
   | adD  l r => adD (cmp l j) (cmp r j)
   | suB  l r => suB (cmp l j) (cmp r j)
   | vr  i  =>  match finEmtp i with
                 | isTp  =>  j
                 | isEmb l => vr (emb l)
                 end
   | cnst n => cnst _ n
  end.

  Fixpoint cmp' n (i : lfun 1) (j : lfun n) : lfun n :=
   match i with
   | adD  l r => adD (cmp' l j) (cmp' r j)
   | suB  l r => suB (cmp' l j) (cmp' r j)
   | vr  i  =>  j
   | cnst n => cnst _ n
  end.

 (* easy to see composition is correct *) 
 Lemma cmp'_ok n (i : lfun 1) (j : lfun n) : 
   forall v,  evl (cmp' i j) v = evl i (vcons (evl j v) (vnil _)).
 Proof.
   induction i; simpl; intros; FSimpl.
 Qed.

 (** fix the first n variables then treat it as a function in 1 variable *)
 Fixpoint plsn n (i : lfun (S n)) (v : Vec nat n) : lfun 1 :=
    match i with 
    | cnst n   =>   cnst _ n 
    | vr j     =>   match finEmtp j with
                    | isTp  =>  vr (fz _)
                    | isEmb l => cnst _ (vecfin v l)
                    end
    | adD l r => adD (plsn l v) (plsn r v)
    | suB l r => suB (plsn l v) (plsn r v)
   end. 
 
  (** check we did the correct thing with  *)
  Lemma plsn_ok n (a : lfun (S n)) : 
       forall v,  evl (plsn a (vfirst v)) (vcons (vlast v) (vnil nat)) = evl a (vSnoc (vlast v) (vfirst v)).
  Proof.
    induction a; simpl; intros; FSimpl; vSimp; simpl.
     try (unfold vlast; unfold vfirst; unfold vhead; unfold vtail; simpl).   
    rewrite vecfin_tp; vecRwt; trivial. rewrite vecfin_emb; vecRwt; trivial.
  Qed.

  (** compsition is correct *)
  Lemma cmp_ok n (i j : lfun (S n)) : forall v, 
    evl (cmp i j) v = (* evl (cmp' (plsn i (vfirst v)) (plsn j (vfirst v))) (vcons (vlast v) (vnil _ )). *)
                      evl (cmp (plsn i (vfirst v)) (plsn j (vfirst v)))  (vcons (vlast v) (vnil nat)).
  Proof.
    induction i; simpl; intros.
    rewrite (IHi1 j v); rewrite (IHi2 j v); trivial.
    rewrite (IHi1 j v); rewrite (IHi2 j v); trivial.
    destruct ( finEmtp f); simpl.
     (* *)
    induction j; simpl; auto.
    destruct ( finEmtp f); simpl. destruct (vCons v); simpl.
    generalize a.
    induction n; vSimp; simpl. unfold vlast; unfold vhead; simpl; trivial.
    rewrite (IHn i a0). unfold vlast. unfold vhead; unfold vtail; simpl; trivial.
    apply vecfin_emb.  apply vecfin_emb . trivial.
 Qed.


  (** embedding a function in n variables into one with n+1 variables from .   *)
    Fixpoint lemb n (i : lfun n) : lfun (S n) :=
    match i with 
    | cnst n =>  cnst _ n 
    | vr j =>  vr (emb j)
    | adD l r => adD (lemb l) (lemb r)
    | suB l r  => suB (lemb l) (lemb r)
   end.

   (*_ embedding a function in n variables into one with n+1 variables - avoid the first  *)
    Fixpoint lfs n (i : lfun n) : lfun (S n) :=
    match i with 
    | cnst n =>  cnst _ n 
    | vr j =>  vr (fs j)
    | adD l r => adD (lfs l) (lfs r)
    | suB l r  => suB (lfs l) (lfs r)
   end.

  (** embedding is fine *)
  Lemma lemb_ok : forall n (i : lfun n) v, evl i (vfirst v)  = evl (lemb i) v. 
  Proof.
   induction i; simpl; intros; try  rewrite vecfin_emb;  auto.  
  Qed.

  (* skip first  is fine *)
  Lemma lfs_ok : forall n (i : lfun n) v, evl i (vtail v)  = evl (lfs i) v. 
  Proof.
   induction i; simpl; intros; vSimp;  auto.  
  Qed.
  
   (**
    post composing with bivariate function 
     -- Given f : N x N -> N and  v : N^n -> N,  want: \lam (a : N^n) n =>  (f . (v n))  n *)
   Fixpoint pl2n n (i : lfun 2) (j : lfun n) : lfun (S n) :=
    match i with 
    | cnst n =>  cnst _ n 
    | vr i' =>   match finEmtp i' with
                 | isTp  =>  vr (tp _)
                 | isEmb l => lemb  j
                 end
    | adD l r => adD (pl2n l j) (pl2n r j)
    | suB l r  => suB (pl2n l j) (pl2n r j)
   end.

  (** correctness of bivariate post compositions  *)
   Lemma pl2n_ok n (l :  lfun 2) (ln :  lfun n) : forall vz,
     evl (pl2n l ln) vz =  evl l (vcons (evl ln (vfirst vz)) (vcons (vlast vz) (vnil _))).
   Proof.
     induction l; intros; simpl; FSimpl. rewrite lemb_ok. trivial. clear.
     induction n; vSimp; simpl. unfold vlast; unfold vhead; trivial.
     generalize (IHn (vcons a0 i)); simpl. intro h; rewrite h.
     unfold vlast; unfold vhead; unfold vtail; auto.
  Qed.

 
 Section TLPiecewise.
   (** * Now extend definitions and proofs to piecewise-linear functions  *)
   Definition Plfun n := Piecewise (lfun n). 
   
   Fixpoint pevl n  (i : Plfun n) v  :=
   match i with 
   | lp a => evl a v
   | pf l cl cr => if lt_le_dec 0 (pevl l v) then pevl cl v else pevl cr v
   end. 

  
   Section Composition.
    
    Fixpoint pcmp' n (l : lfun 1) (ln : Plfun n) :=
     match ln with
     | lp a => lp (cmp' l a)
     | pf a b c => pf a  (pcmp' l b)  (pcmp' l c)
     end.

    Lemma pcmp'_ok n l (ln : Plfun n) v : pevl (pcmp' l ln) v = evl l (vcons (pevl ln v) (vnil _ )).
    Proof.
      induction ln; simpl; intros; try apply cmp'_ok.
      rewrite (IHln2  v);  rewrite  (IHln3 v); destruct ( lt_le_dec 0 (pevl ln1 v)); trivial.
   Qed.

   (** post composing with a univariate piecewise-linear function  *)
   Fixpoint pcmp1 n (i : Plfun 1) (j : Plfun n) :=
    match i with
    | lp l => pcmp' l j
    | pf c l r => pf (pcmp1 c j) (pcmp1 l j) (pcmp1 r j)
   end.

  (** correctness of this composition  *)
  Lemma pcmp1_ok n (i : Plfun 1) (j : Plfun n) : forall v, pevl (pcmp1 i j) v = pevl i (vcons (pevl j v) (vnil _ )).
  Proof. 
    induction i; try apply pcmp'_ok; simpl.
    intros j v; rewrite (IHi1 j v); rewrite (IHi2 j v); rewrite (IHi3 j v); trivial.
  Qed.

    (* piecewise case for plSn2n *)
   Fixpoint pplsn n (i :  Plfun (S n)) (v : Vec nat n) : Piecewise (lfun 1) := 
     match i with
     | lp l => lp (plsn l v)
     | pf c l r => pf (pplsn c v)  (pplsn l v) (pplsn r v)
     end.

   (* correctness *)
   Lemma pplsn_ok n (l :  Plfun (S n))  : forall v,
       pevl (pplsn l (vfirst v)) (vcons (vlast v) (vnil _)) = pevl l (vSnoc (vlast v) (vfirst v)) .
   Proof. 
     induction l; simpl; intros; try apply plsn_ok.
     rewrite (IHl1 v); rewrite (IHl2 v); rewrite (IHl3 v); trivial.
   Qed.

   (** composition of two n+1-variate piecewise-linear functions, by fixing the 
    first n varaibles and treating them as a univariate function *)
  Fixpoint pcmp_aux n (l : lfun (S n)) (i : Plfun (S n)) : Plfun (S n) :=
    match i with
    | lp ll => lp (cmp l ll)
    | pf c ll rr => pf c (pcmp_aux l ll) (pcmp_aux l rr)
    end.

  Lemma cmp_cmp' (i j : lfun 1): forall v,  evl (cmp i j) v = evl (cmp' i j) v.
  Proof.
    induction i; simpl; intros; FSimpl.
  Qed.

 (*  Lemma pcmp_cmp' (i : lfun 1) (j : Plfun 1) : forall v,  pevl (pcmp' i j) v = pevl (pcmp_aux i j) v. *)

  (* correctness proof for pcompSn1*)
  Lemma pcmp_aux_ok n (i : lfun (S n)) (j : Plfun (S n)) : forall v, 
    pevl (pcmp_aux i j) v = pevl (pcmp' (plsn i (vfirst v)) (pplsn j (vfirst v))) (vcons (vlast v) (vnil _ )).
   Proof.
     induction j; simpl; intros.  rewrite  (cmp_ok i a v); rewrite  cmp_cmp'.  trivial. 
     rewrite (IHj2 v);  rewrite (IHj3 v). 
     replace (pevl j1 v) with (pevl (pplsn j1 (vfirst v)) (vcons (vlast v) (vnil _))); trivial. 
     rewrite (pplsn_ok j1 v); rewrite <- (vVsnoc v); trivial.
  Qed.

  (** main function *) 
  Fixpoint pcmp n (i j : Plfun (S n)) :=
   match i with
   | lp l => pcmp_aux l j
   | pf c l r => pf (pcmp c j) (pcmp l j) (pcmp r j)
   end.

  (** correctness proof for pcompSn*)
  Lemma pcmp_ok n  (i j : Plfun (S n)) : forall v, 
    pevl (pcmp i j) v = pevl (pcmp1 (pplsn i (vfirst v)) (pplsn j (vfirst v))) (vcons (vlast v) (vnil _ )).
  Proof. 
   induction i; simpl; intros;  try apply pcmp_aux_ok.
   rewrite (IHi1 j v);  rewrite (IHi3 j v);  rewrite (IHi2 j v); trivial.
  Qed.

   (* push a piecewise-linear function in n variables into a functions in n + 1 variables
      such that  f v = (polwk f) (tail v) *)
  Fixpoint plfs n (i : Plfun n) :=
    match i with
    | lp l => lp (lfs l)
    | pf a b c => pf (plfs a) (plfs b) (plfs c)
    end.

  Lemma plfs_ok n (i : Plfun n) : forall v, pevl (plfs i) v = pevl i (vtail v).
  Proof.
    induction i; simpl; intros; try rewrite lfs_ok; trivial.
    rewrite (IHi1 v); rewrite (IHi2 v); rewrite (IHi3 v); trivial.
  Qed.

  (* push a piecewise-linear function in n variables into a functions in n + 1 variables
      such that  f v = (polwk f) (first v) *)
  Fixpoint pemb n (i : Plfun n) :=
    match i with
    | lp l => lp (lemb l)
    | pf a b c => pf (pemb a) (pemb b) (pemb c)
    end.

  Lemma pemb_ok n (i : Plfun n) : forall v, pevl (pemb i) v = pevl i (vfirst v).
  Proof.
    induction i; intros; simpl; try rewrite lemb_ok; trivial.
    rewrite (IHi1 v); rewrite (IHi2 v); rewrite (IHi3 v); trivial.
  Qed.

    (*
    post composing with bivariate piecewise-linear function 
    Given f : N x N -> N and  v : N^n -> N, \lambda (a : N^n) m =>  (f . (v a))  m *)
  Fixpoint ppl2n_aux n (l : lfun 2) (i : Plfun  n)  :=
    match i with
    | lp ll => lp (pl2n l ll)
    | pf c ll rr => pf (pemb c) (ppl2n_aux l ll) (ppl2n_aux l rr)
    end.

   Lemma ppl2n_aux_ok n (l :  lfun 2) (ln :  Plfun n) : forall vz,
      pevl (ppl2n_aux l ln) vz =  evl l (vcons (pevl ln (vfirst vz)) (vcons (vlast vz) (vnil _))).
   Proof.
     induction ln; simpl; try apply pl2n_ok.
     intros vz; rewrite (pemb_ok ln1 vz);  rewrite (IHln2 vz); rewrite (IHln3 vz).
     destruct (lt_le_dec 0 (pevl ln1 (vfirst vz))); trivial.
   Qed.

  (* case : bothe piecewise *)
   Fixpoint ppl2n n (l : Plfun 2) (i : Plfun  n)  :=
    match l with
    | lp ll => ppl2n_aux ll i
    | pf c ll rr => pf (ppl2n c i) (ppl2n ll i) (ppl2n rr i)
    end.

    (* correctness *)
    Lemma ppl2Sn_ok n (l : Plfun 2) (ln :  Plfun n) : forall vz,
      pevl (ppl2n l ln) vz =  pevl l (vcons (pevl ln (vfirst vz)) (vcons (vlast vz) (vnil _))).
    Proof.
      induction l; simpl; intros;  try apply ppl2n_aux_ok.  
      rewrite (IHl1 ln vz); rewrite (IHl2 ln vz); rewrite (IHl3 ln vz); trivial.
    Qed.
   
    (* --------------------------------------------------*) 
    Fixpoint ppl2n_ax n (l : Plfun 2) (i : lfun n)  :=
    match l with
    | lp ll => lp (pl2n ll i)
    | pf c ll rr => pf (ppl2n_ax c i) (ppl2n_ax ll i) (ppl2n_ax rr i)
    end.

  Lemma ppl2n_ax_ok n (l : Plfun 2) (i : lfun n) : 
      forall v, pevl (ppl2n_ax l i) v = pevl  l (vcons (evl i (vfirst v)) (vcons (vlast v) (vnil _))).
  Proof.  
    induction l; simpl; intros. apply pl2n_ok.
    rewrite (IHl1 i v); rewrite (IHl2 i v);  rewrite (IHl3 i v). trivial.
  Qed.
    

 End Composition.
  

 Section Representation.
  
   (** We can represent polymorphic functions whose shape maps are linear
     as a pair, given by a linear function for the shapes and a piecewise-linear function 
    for the positions. This representaiton does not have a on-to-one correspondence with
    container morphisms, but instead captures the operations inherent in the container representation
    in an intuitive way, amenable to geometric interpretation   *) 
   
    
    (** liner shape maps only *) 
    Definition PCm n :=  prod (lfun  (S n)) (Plfun (S  (S n))).

     (** piecewise-linear shape maps -- these are more general *)
     Definition PPCm n :=  prod (Plfun  (S n)) (Plfun (S  (S n))).

    (** Interpretation  *)
    Definition PCm_int' n (X : Set) :   PCm  n -> Vec nat (S n) * (nat -> X) ->   nat * (nat -> X) :=
       fun pl  vl => let (l , p) := pl in
                                (evl l (fst vl) , fun v => snd vl (pevl p (vSnoc v (fst vl)))).
     (* piecewise case *)
     Definition PPCm_int' n (X : Set) :   PPCm  n -> Vec nat (S n) * (nat -> X) ->   nat * (nat -> X) :=
       fun pl  vl => let (l , p) := pl in
                                (pevl l (fst vl) , fun v => snd vl (pevl p (vSnoc v (fst vl)))).
 
    (** unpacking  list of lists  *)
    Fixpoint  nf2pvf1 n (X : Set) (v : Vec (nat * (nat -> X)) n) (F : nat -> X) (i : nat) :   X :=
     match v with
     | vnil => F i
     | vcons _ x xs =>  if le_lt_dec (fst x ) i then  nf2pvf1 xs  (snd x) (i - (fst x)) else (snd x) i
     end.

  (*
    Fixpoint  vf2pvf1 n (X : Set) (v : Vec (Z * (Z -> X)) n) (k : Z * (Z -> X)) (z : Z) :   X :=
     match v with
     | vnil => snd k z
     | vcons _ x xs =>  if Z_lt_dec z (fst x) then  (snd x) z
                                 else vf2pvf1 xs k (z - fst x)
     end.
   *)

   Definition nf2pf n (X : Set) (v : Vec (nat * (nat -> X)) (S n)) :=
                (vmap  (fst (A := nat) (B := nat -> X)) v, nf2pvf1 (vtail v) (snd (vhead v))) .
  

   Definition PCm_int n (X : Set) :   PCm  n -> Vec (prod nat (nat -> X)) (S n) ->   nat * (nat -> X) := 
        fun i nm => PCm_int' i (nf2pf nm).  

   (* piecewise *)
    Definition PPCm_int n (X : Set) :   PPCm  n -> Vec (nat * (nat -> X)) (S n) ->   nat * (nat -> X) := 
        fun i nm => PPCm_int' i (nf2pf nm).              


 (** Composition : we only postcompose with a univariete functions *)
    Definition PComp n (l : PCm 0) (r : PCm n) := 
      let (v , G) := l in
         let (u , F) := r in
              (cmp' v u , pcmp F (ppl2n_ax G u)). 
   
    (** composition of lmors commute with composition of functions*)
    Lemma PCm_cmp_ok n (l : PCm 0)  (r : PCm n)  (X : Set) : 
       forall (k : Vec (prod nat (nat -> X)) (S n)),  PCm_int (PComp l r) k = PCm_int l (vcons (PCm_int r k) (vnil _)).
       unfold PCm; unfold PComp; unfold PCm_int; unfold PCm_int'.
       destruct l; destruct r; simpl. intros.
       assert (forall (A B : Type) (a b : A * B), fst a = fst b -> snd a = snd b -> a = b); 
        try (destruct a;  destruct b0; simpl; repeat( intro h; destruct h); trivial). 
       apply H; simpl; try apply (cmp'_ok l l0 ). 
       apply extensionality;  intros;  
       rewrite (pcmp_ok  p0 (ppl2n_ax p l0));  rewrite pcmp1_ok;
       rewrite (pplsn_ok (ppl2n_ax p l0) ); rewrite ppl2n_ax_ok;
       generalize (pplsn_ok p0 (vSnoc (pevl p (vcons (evl l0 (vmap (fst (A := nat) (B := nat -> X)) k)) (vcons a (vnil nat))))
         (vmap (fst (A := nat) (B := nat -> X)) k))); repeat vecRwt ; try ( intro H0; rewrite H0; trivial).
    Qed.

   (* piecewise composition *) 
    Definition PPComp n (l : PPCm 0) (r : PPCm n) := 
      let (v , G) := l in
         let (u , F) := r in
              (pcmp1 v u , pcmp F (ppl2n G u)).

    (** piecewise composition is correct *)
    Lemma PPCm_cmp_ok n (l : PPCm 0)  (r : PPCm n)  (X : Set) : 
       forall (k : Vec (prod nat (nat -> X)) (S n)),  PPCm_int (PPComp l r) k = PPCm_int l (vcons (PPCm_int r k) (vnil _)).
       unfold PPCm; unfold PPComp; unfold PPCm_int; unfold PPCm_int'.
       destruct l; destruct r; simpl. intros.
       assert (forall (A B : Type) (a b : A * B), fst a = fst b -> snd a = snd b -> a = b); 
        try (destruct a;  destruct b0; simpl; repeat( intro h; destruct h); trivial). 
       apply H; simpl. try apply (pcmp1_ok p p1 ). 
       apply extensionality;  intros.  
       rewrite (pcmp_ok  p2 (ppl2n p0 p1)); rewrite pcmp1_ok;
       rewrite (pplsn_ok (ppl2n p0 p1) ); rewrite ppl2Sn_ok;
       generalize (pplsn_ok p2 (vSnoc (pevl p0 (vcons (pevl p1 (vmap (fst (A := nat) (B := nat -> X)) k)) (vcons a (vnil nat))))
         (vmap (fst (A := nat) (B := nat -> X)) k))); repeat vecRwt ; try ( intro H0; rewrite H0; trivial).
    Qed.
  

   Fixpoint pcmpm_aux (n : nat) (i : Plfun (S n)) (j : lfun (S n))  :=
    match i with
    | lp l => lp (cmp l  j) 
    | pf c l r => pf (pcmpm_aux c j) (pcmpm_aux l j) (pcmpm_aux r j)
    end.

   (* correctness *)
   Lemma pcmpm_aux_ok n (i : Plfun (S n)) (l : lfun (S n)) : 
    forall v,   pevl (pcmpm_aux i l) v =
       pevl (pcmp1 (pplsn i (vfirst v)) (pplsn (lp l) (vfirst v))) (vcons (vlast v) (vnil nat)). 
   Proof.
    induction i; simpl; intros. rewrite <- cmp_cmp'. apply cmp_ok.
    rewrite (IHi1 l v); rewrite (IHi2 l v); rewrite (IHi3 l v). trivial.
   Qed.

  Fixpoint pcmpm (n : nat) (i j : Plfun (S n))  :=
    match j with
    | lp l => pcmpm_aux i l
    | pf c l r => pf c (pcmpm i l) (pcmpm i r)
    end.
 

  (* correctness *-)
  Lemma pcmpm_ok n (i j : Plfun (S n)) : 
    forall v, *)

  (* post compoing a piecewise-linear function along hte if *)
  Fixpoint pmp m (l : PPCm 0) (r : PPCm m) :=
       let (v , G) := l in
         let (u , F) := r in
              (pcmp1 v u , pcmpm F (ppl2n G u)).
    
    
 End Representation. 
  

 End TLPiecewise.

  
 Section Normalizing.
     (** Euqality for linear functions  *)
     
     (* push a number into a vector at positions determined by Fin n *)
     Fixpoint push n (X : Set) (x0 : X) (i : Fin n) (z : X) : Vec X n :=
     match i in Fin e return (Vec X e ) with
     | fz m => vcons z (vec m x0)
     | fs _ j => vcons x0 (push  x0 j z)
     end. 

   (* in n variables, alpha is an array of length n *)
   Fixpoint alps n (i : lfun n) :  Vec nat n :=
    match i  with
    | cnst _ =>  vec n 0
    | vr j => push 0 j 1
    | adD l r => vAdd (alps l) (alps r) 
    | suB l r => vSub (alps l) (alps r)
   end.
 
   (* beta is just a constant *)
   Fixpoint bet n (i : lfun n)  :=
   match i  with
   | cnst n =>   n
   | vr _   => 0
   | adD l r => (bet l + bet r)
   | suB l r => (bet l - bet r)
   end.

   Definition norm n (i : lfun n) := (alps i , bet i). 
   
   (* decision procedure for Lfun n  *)
   Definition lfunEq n (i j : lfun n) :=  
     if (vecEqDec eq_nat_dec (alps i) (alps j)) then (if eq_nat_dec (bet i) (bet j) then true else false) else false.  

 End Normalizing.


Section Equality. 

   Definition vlst n (v : Vec nat n) :=
      match v with
      | vnil  => 0
      | xs    => vlast xs
      end.
 
   (** Equality:  *)   
  Inductive pcmEQ n (i j : PPCm n) : Prop :=
  | isEQ :  (* lfunEq  (fst i) (fst j) = true -> *)
            (forall v, pevl (fst i) v = pevl (fst j) v) ->
            (forall v, 
               vlast v < pevl (fst i) (vfirst v) -> 
               vlast v < pevl (fst j) (vfirst v) ->  pevl  (snd i) v = pevl (snd j) v) -> pcmEQ i j.
   


  (** Correctness of equality  *)
 Lemma pcmEQ_ok n (l r : PPCm n)  (X : Set) : 
       forall (k : Vec (prod nat (nat -> X)) (S n)),
    pcmEQ l r -> (forall a, a <  pevl (fst l)  (vmap (fst (A := nat) (B := nat -> X)) k) /\
                            a <  pevl (fst r)  (vmap (fst (A := nat) (B := nat -> X)) k) ) -> PPCm_int  l k = PPCm_int r k.
 Proof.
   unfold PPCm_int; unfold PPCm_int'; intros n l r X k H H0.
   destruct l; destruct r; destruct H as [H1 H2]; simpl in *. 
   generalize H2; generalize H0. clear H0 ; clear H2.
   rewrite (H1 (vmap (fst (A := nat) (B := nat -> X)) k) ).
   intros H0 H2; 
   cut (forall (A B :Set) (a a1 : A) (b b1 : B), a = a1 /\ b = b1 -> (a, b) = (a1 , b1)). 
  intros. apply H;split; clear H; trivial.
   apply extensionality. intros.
   generalize (H2 (vSnoc a (vmap (fst (A := nat) (B := nat -> X)) k)) ).
   clear H2; vecRwt.
   rewrite (vfirst_vSnoc  a (vmap (fst (A := nat) (B := nat -> X)) k)  ).
   rewrite (H1 (vmap (fst (A := nat) (B := nat -> X)) k)).
   intros. destruct (vCons k); unfold vhead; unfold vtail; simpl.
   destruct a0; simpl in *. 
   rewrite (H (proj1 (H0 a)) (proj2 (H0 a))); trivial.
   intros. destruct H as [L R]; destruct L; destruct R; trivial.
  Qed.


  End Equality. 
 

(** * Experiements with arithmetic representation *)

 (** first some basic tactics to introduce the assumptions, etc *)
  Ltac remLtLe' :=
     match goal with 
     | [|- context [lt_le_dec ?x ?y]] =>  destruct (lt_le_dec x y) 
  end.

 Ltac remLtLe := repeat remLtLe'. 

 Ltac initialise_tac :=
     apply isEQ; simpl; intros; vSimp; simpl in *; remLtLe.

  (** main tactic *)
  Ltac containers :=
      initialise_tac; optimiseOmega;  omega.


  Section Examples_and_Definitions.
(** Definitions and Exmaples*)

  (** reverse *)
  Definition Rev1 :  Plfun 1 *  Plfun 2  :=
   (  lp (vr (fz _ )) ,  
   (lp (suB (suB (vr (fz _)) (vr (tp _))) (cnst _ 1))) ). (*pf (lp (suB (vr (fz _))  (vr (tp _)))) (lp (cnst _ 0))). *)
 
  (** identity function  *)
  Definition Id1 n :  lfun n :=
    match n with
    | O => cnst _ 0
    | S n => vr (tp n)
    end.

  Definition Idf :  Plfun 1 *  Plfun 2  := (   lp (vr (fz _ )) , lp (Id1 2)).
  
  
  (** rev is involutive  *)
  Lemma rev_rev_idm  :  pcmEQ (PPComp Rev1 Rev1) Idf.
     containers.
   (*  currently takes 11 seconds *)
  Qed.

 
  (* Append = (n, f) where
      n = \lambda  n m. n + m
      f = \lambda n m i. if i < n + m then  
                               if i < n then i else n - i
                          else 0
   *)
  (** Append  *)
  Definition appn1 : PPCm 1 :=
     (lp (adD (vr (fz _ )) (vr (fs (fz _)))) , 
          (pf (lp (suB (vr (fz _)) (vr (tp _)))) (lp (vr (tp 2))) (lp (suB (vr (fz _)) (vr (tp 2))))) 
     ).

 
   (**  app reverse *)
  Lemma rev1_appn1 : pcmEQ (PPComp Rev1 appn1) (pmp Rev1 appn1).
  Proof.  
    containers.
   (* apply isEQ; simpl; intros; vSimp; simpl in *; remLtLe; repeat remMinus_0; auto. *)
  Qed.

  

 (* tail = (f ,g ) where
         f n = n - 1 
         g n i =  i + 1   *)

 (** tail  *)
 Definition tail1 : PPCm 0 :=
    ( lp (suB (vr (fz _)) (cnst _ 1)) , lp (adD (vr (tp 1)) (cnst _ 1)) ).

 (* butlast = (f , g)  where
       (f , g) where
       f n = n - 1
       g n i =  i (or i - 1) *)

 (** But last *)
 Definition butlast1 : PPCm 0 :=
     ( lp (suB (vr (fz _)) (cnst _ 1)) , lp (vr (tp _ ))) (*suB (vr (tp _)) (cnst _ 1)) *).

(** last *)
 Definition last1 : PPCm 0 :=
    ( lp (suB (vr (fz _)) (suB (vr (fz _)) (cnst _ 1))) ,
      pf (lp (suB (suB (vr (fz _)) (suB (vr (fz _)) (cnst _ 1))) (vr (tp _ ))))
         (lp (suB (vr (fz _)) (cnst _ 1))) (lp (cnst _ 0))).


 (** head  *)
 Definition head1 : PPCm 0 :=
    (lp (suB (vr (fz _)) (suB (vr (fz _)) (cnst _ 1))),
        pf (lp (suB (suB (vr (fz _)) (suB (vr (fz _)) (cnst _ 1))) (vr (tp _ ))))
         (lp (cnst _ 0)) (lp (cnst _ 0))).

 
 (** Theorems:  
 -- 1.  Theorem crev_chead_clast :  (m_comp cHead crev) ==== clast.
 -- 2.  Theorem crev_cbut_last_ctail :  (m_comp ctail crev) ==== (m_comp crev cbut_lst).
 *)
 
 Lemma  rev_head_last : pcmEQ (PPComp head1 Rev1) last1.
    containers. 
 Qed.


 Lemma  crev_butlast_tail : pcmEQ (PPComp tail1 Rev1) (PPComp Rev1 butlast1).
   containers. 
 Qed.


  (** Take               *)
 Definition take1 m : PPCm 0 :=
    ( pf (lp (suB (cnst _ m) (vr (fz _)))) (lp (cnst _ m)) (lp (vr (fz 0)))  ,
       (pf (lp (suB (cnst _ m) (vr (tp 1)))) (lp (cnst _ m)) (lp (vr (tp 1))))
    ).
   

  (** drop m   *)
  Definition drop1 m : PPCm 0 :=
    ( lp (suB (vr (fz _)) (cnst _ m)) , lp (adD (vr (tp _)) (cnst _ m)) ).


 (**  drop n (drop m xs) = drop (n + m) xs  *)
 Lemma drop_drop n m : pcmEQ (PPComp (drop1 n) (drop1 m)) (drop1 (n + m)). 
 Proof.
   intros. containers.
 Qed.

 (* drop n (take m xs) = take (m - n) (drop n xs)  *)
 Lemma drop_take n m : pcmEQ (PPComp (drop1 n) (take1 m)) (PPComp (take1 (m - n)) (drop1 n)).
 Proof. 
   intros. containers.
 Qed.

 (**  take n (drop m xs) = drop m (take (n + m) xs) *)
 Lemma take_drop n m : pcmEQ (PPComp (take1 n) (drop1 m)) (PPComp (drop1 m) (take1 (n + m))).
 Proof.
    intros. containers.
 Qed.


  (* rot1 = (f ,g ) where
        f = id
        g = \lambda n i.  if i < 1 then n- 1 else i -1
                           *)
   (** unrotate  - put last element at the front  *)
  Definition unrot1 : PPCm 0 :=
    (lp (Id1 1) ,
     pf (lp (vr (tp _))) 
         (lp (suB (vr (tp _)) (cnst _ 1)))  (lp (suB (vr (fz _)) (cnst _ 1)))
    ).

  (* rotate - dual to unrotate *)
  Definition rot1 : PPCm 0 :=
    (lp (Id1 1) ,
     pf (lp (suB (suB (vr (fz _))  (cnst _ 1)) (vr (tp _)))) 
         (lp (adD (vr (tp _)) (cnst _ 1)))
        (* (lp (suB (vr (tp _)) (suB (vr (fz _))  (cnst _ 1)))) *)
          (lp (cnst _ 0)) 
    ).

  (** roatate (unrotate x) = xs *)
 Lemma rot_unrot : pcmEQ (PPComp rot1 unrot1)  Idf.
 Proof.
     containers.
  Qed.

 (** head  head (reverse ( rotate xs )) = head xs  *)
 Lemma head_rev_rot : pcmEQ (PPComp head1 (PPComp Rev1 rot1)) head1.
 Proof.
    containers.
 Qed.
  

 (**  last (rotate xs) = head xs *)
 Lemma last_rot_head : pcmEQ (PPComp last1 rot1) head1.
 Proof.
   containers.
 Qed.

 (** head (unrotate xs) = last xs  *)
 Lemma head_unrot_last : pcmEQ (PPComp head1 unrot1) last1.
 Proof.
   containers.
 Qed.

 (**   drop 1 (unrotate xs) =  butlast xs *)
 Lemma drop_unrot_but_last : pcmEQ (PPComp (drop1 1) unrot1) butlast1.
 Proof.
   containers.
 Qed.

 (**  butlast (rotate xs) = tail xs*)
 Lemma butlast_rot_tail : pcmEQ (PPComp butlast1 rot1) tail1.
 Proof.
   containers.
 Qed.
   
End Examples_and_Definitions.

