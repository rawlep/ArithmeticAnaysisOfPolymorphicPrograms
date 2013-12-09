Require Import Bool.

 Set Implicit Arguments.  

  Lemma bool_dec : forall b, {b = true}+{b = false}.
    destruct b; auto.
  Qed.
 
 Section TreeS. 
  (** Representing Piecewise functions *)

   Variables  (A : Set) (Aeq : A -> A -> bool)
            (Haq : forall a b, Aeq a b =  true -> Aeq b a = true).
  
  Inductive Piecewise : Set :=
   | lp : A -> Piecewise
   | pf : Piecewise -> Piecewise -> Piecewise -> Piecewise.

  Inductive Cond : Set :=
   | Ret :  A -> Cond 
   | Cif :  A -> Cond-> Cond -> Cond.

  (* trivial equality for Cond *)
  Fixpoint CondEq i j :=
    match i, j with
    | Ret a, Ret b => Aeq a b
    | Cif a l r, Cif b l1 r1 => 
       if Aeq a b then CondEq l l1 && CondEq r r1 else false
    | _ , _ => false
    end.
   
  Fixpoint  cif  (a b c : Cond)  : Cond :=
   match a  with
   | Ret x => Cif  x b c
   | Cif x bt be => Cif x (cif bt b c) (cif be b c) 
   end.
  
  (* From Piecewise to Cond  *)
  Fixpoint pNrm' ( p : Piecewise)  :=
    match p with
   | lp a => Ret a
   | pf c l r => cif (pNrm' c) (pNrm' l) (pNrm' r)
   end.


  (* cif is associative *)
  Lemma ciflemm (a b c x y : Cond) :
    cif (cif a b c) x y = cif a (cif b x y) (cif c x y).
  Proof. 
   induction a; simpl; auto.
   intros b c x y; rewrite (IHa1 b c x y);  rewrite (IHa2 b c x y); trivial.
  Qed.

 Section Normalization.

  (** We can flatten the tree to the right and check each interval, but this
      of course is subject ot the ordering of the intervals, hence thos does not really work *)

   Inductive ST : Set :=
    | sl   : A -> ST 
    | sf : A -> A -> ST -> ST.

   Fixpoint STeq i j :=
     match i, j with
     | sl a, sl b => Aeq a b
     | sf c a x, sf c1 a1 y => if (Aeq c c1) then (Aeq a a1) && (STeq x y) else false
     | _ , _ => false
     end.

  Fixpoint flatn_aux a (b c : ST) : ST :=
    match b with
    | sl x => sf a x c
    | sf x l r => sf x l (flatn_aux a r c)
    end.

  Fixpoint flatn (i : Cond ) : ST  :=
    match i with
    | Ret a => sl a
    | Cif a l r => flatn_aux a (flatn l) (flatn r)
    end.
    

 End Normalization.

 End TreeS.

 (* Section TreeS.
  (* Set Implicit Arguments. *)

  Variables (A : Set) (Aeq : A -> A -> bool)
            (Haq : forall a b, Aeq a b =  true -> Aeq b a = true).
  

  Inductive Piecewise : Set :=
   | lp : A -> Piecewise
   | pf : Piecewise -> Piecewise -> Piecewise -> Piecewise.

  Inductive Cond :     Set :=
   | Ret :  A -> Cond 
   | Cif :  A -> Cond-> Cond -> Cond.

 
  Fixpoint CondEq i j :=
    match i, j with
    | Ret a, Ret b => Aeq a b
    | Cif a l r, Cif b l1 r1 => 
       if Aeq a b then CondEq l l1 && CondEq r r1 else false
    | _ , _ => false
    end.
   
  Fixpoint  cif  (a b c : Cond)  : Cond :=
   match a  with
   | Ret x => Cif  x b c
   | Cif x bt be => Cif x (cif bt b c) (cif be b c) 
   end.

  Fixpoint pNrm' ( p : Piecewise)  :=
    match p with
   | lp a => Ret a
   | pf c l r => cif (pNrm' c) (pNrm' l) (pNrm' r)
   end.

 Fixpoint intervals i :=
   match i with
   | Ret a => (a :: nil)
   | Cif _ l r => intervals l ++ intervals r  
  end.

 (*Lemma intervals_cif : forall a b c (F : A -> A),
  map F (intervals (cif a b c)) =  match a with
                          | Ret _ => map F (intervals b) ++ map F (intervals c) 
                            | Cif _ x y => map F (intervals (cif x b c)) ++ 
                                           map F (intervals (cif y b c))
                             end.
   destruct a; simpl. intros. apply map_app.
   intros. apply map_app.
 Qed. *)

 (*Lemma intervals_cif : forall a b c,  
   intervals (cif a b c) =  match a with
                            | Ret _ => intervals b ++intervals c 
                            | Cif _ x y => intervals (cif x b c) ++ 
                                           intervals (cif y b c)
                             end.
 Proof.
   induction a; simpl; trivial. 
 Qed. *)

 Fixpoint break_points i :=
   match i with
   | Cif a l r => break_points l ++ (a :: break_points r)
   | _  => nil
   end.



 Lemma int_bps_len1 : 
     forall l, (length (intervals l) = 1 + length (break_points l))%nat.
  Proof.
    induction l; simpl;  try auto with arith.
    rewrite (app_length (intervals l1) (intervals l2));
    rewrite (app_length (break_points l1) (a:: break_points l2)). simpl.
    replace (length (break_points l1) + S (length (break_points l2)))%nat with
    (S (length (break_points l1) +  (length (break_points l2))))%nat; 
    try auto with arith;  omega. 
  Qed.


(* Lemma int_bps_len : 
     forall l, (length (break_points l) < length (intervals l))%nat.
  Proof.
    induction l; simpl; try auto with arith.
    rewrite (app_length (break_points l1) (a:: break_points l2));
    rewrite (app_length (intervals l1) (intervals l2)); simpl.
    replace (length (break_points l1) + S (length (break_points l2)))%nat with
    (S (length (break_points l1) +  (length (break_points l2))))%nat; 
    try auto with arith; omega.
  Qed. *)

 Variable a0 : A.

  Fixpoint seq bps inv   :=
   match bps, inv with
   | nil,   x::xs => Ret x
   | y::ys, x::xs => Cif y  (Ret x) (seq ys xs)
   | _ , _        =>   Ret a0
   end.
   
  Definition norm l := seq  (break_points l) (intervals l).

  Lemma intv_seq : forall l1 l2, length l2 = (1 + length l1)%nat  -> 
    intervals (seq l1 l2) = l2.
    induction l1; simpl. intros. destruct l2. simpl in H; discriminate H.
    destruct l2; simpl in *; trivial. discriminate H.
    intros. destruct l2; simpl in *. discriminate H.
    injection H. intros.  pattern l2 at 2. 
    rewrite <- (IHl1 l2 H0); trivial.
  Qed.

   Lemma bps_seq : forall l1 l2, length l2 = (1 + length l1)%nat  -> 
    break_points (seq l1 l2) = l1.
    induction l1; simpl. intros l2 H; destruct l2.
    simpl in H; discriminate H. trivial.
    destruct l2; simpl in *.  intro H; discriminate H.
     intros H;  injection H. intro H0;  pattern l1 at 2; 
    rewrite <- (IHl1 l2 H0); trivial.
  Qed.

  Lemma nf_intv : forall l, (intervals l) = (intervals (norm l)).
  Proof.
    unfold norm;  intro l;
    rewrite (intv_seq (break_points l) (intervals l) (int_bps_len1 l));
    trivial.
  Qed.

  Lemma nf_bps : forall l, (break_points l) = (break_points (norm l)).
  Proof.
    unfold norm;  intro l;
    rewrite (bps_seq (break_points l) (intervals l) (int_bps_len1 l));
    trivial.
  Qed.

 (* nf is a "normal" form *)
 Lemma nf_nf_idem : forall l, norm (norm l) = norm l.
  unfold norm at 1. intro l;
   rewrite <- (nf_bps l); rewrite <- (nf_intv l);
   unfold norm; trivial.
 Qed.


 (* Equating lists of A *)
  Inductive EQL : list A -> list A -> Set :=
  | eq_nil  : EQL nil nil
  | eq_cons : forall l r ls rs, Aeq l r = true -> EQL ls rs ->
                    EQL (l :: ls)  (r :: rs).
  (*| eq_app  : forall l l1 r r1, EQL l l1 -> EQL r r1 -> 
   EQL (l ++ r) (l1 ++ r1). *)


 Fixpoint ListEq  i j :=
  match i, j with
  | nil, nil => true
  | x :: xs, y :: ys => if Aeq x y then ListEq xs ys else false 
  | _ , _ => false
  end.


 Lemma ListEq_len : forall l l1, ListEq l l1 = true -> length l = length l1.
 Proof.
  induction l; destruct l1; simpl; try (intro h; discriminate h); auto.
  destruct (bool_dec ( Aeq a a1)). rewrite e.
  intro h; rewrite (IHl  _ h); trivial.
  rewrite e; intro h; discriminate h.
 Qed.

 Lemma listEq_EQL : forall l l1, ListEq l l1 = true -> EQL l l1.
 Proof.
  induction l; destruct l1; simpl; try (intro h; discriminate h).
  exact (fun _ => eq_nil).
  destruct (bool_dec (Aeq a a1)). rewrite e.
  intro h; exact (eq_cons e (IHl _ h)).
  rewrite e; intro h; discriminate h.
 Qed.

 Lemma intv_not_nill : forall l, intervals l <> nil.
  induction l; simpl; auto. discriminate.
  intuition. case (IHl1 (proj1 (app_eq_nil (intervals l1)  (intervals l2) H))).
 Qed.

 (* Lemma ListEq_append : forall l l1 r r1, ListEq (l ++ r) (l1 ++ r1) = true ->
   ListEq l l1 = true /\ ListEq r r1 = true.
 Proof.
   induction l; destruct l1; simpl; auto. simpl. *)

  
   (* cnd to piecewise *)
  Fixpoint cnd2P (i : Cond ) :=
    match i with
   | Ret a => lp a
   | Cif c l r => pf (lp c) (cnd2P l) (cnd2P r)
   end. 

   Lemma cnd2P_ok : forall i, pNrm' (cnd2P i) = i.
      induction i; simpl; auto.
      rewrite IHi1; rewrite IHi2; trivial.
   Qed.

 (* Definition pNRm p :=  cnd2P (flatten (pNrm' p)).
  Definition pNrm p :=  (flatten (pNrm' p)).
  Definition PEq i j := CndEq (pNrm i) (pNrm j). *)

  (* cif is associative *)
  Lemma ciflemm (a b c x y : Cond) :
    cif (cif a b c) x y = cif a (cif b x y) (cif c x y).
  Proof. 
   induction a; simpl; auto.
   intros b c x y;
   rewrite (IHa1 b c x y); 
   rewrite (IHa2 b c x y); trivial.
  Qed.

 Section Normalization.

   Inductive ST : Set :=
    | sl   : A -> ST 
    | sf : A -> A -> ST -> ST.

   Fixpoint STeq i j :=
     match i, j with
     | sl a, sl b => Aeq a b
     | sf c a x, sf c1 a1 y => if (Aeq c c1) then (Aeq a a1) && (STeq x y) else false
     | _ , _ => false
     end.

  Fixpoint flatn_aux a (b c : ST) : ST :=
    match b with
    | sl x => sf a x c
    | sf x l r => sf x l (flatn_aux a r c)
    end.

  Fixpoint flatn (i : Cond ) : ST  :=
    match i with
    | Ret a => sl a
    | Cif a l r => flatn_aux a (flatn l) (flatn r)
    end.
    

 End Normalization.

 End TreeS. *)
