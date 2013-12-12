Require Import Arith FinSummDefs  Omega JMeq ZArith Ring Containers.

(**
------
  Rewrites objects (from left to right) in foo Fin n using foo: Fin n -> nat,
    the function which reduces an object in Fin n to its representation in nat.
-- 1.  nat_finite_id: forall (n k:nat)(h:k<n), (foo (nat_finite k h)) = k.
-- 2.  finite_nat_id_general:
      forall (n:nat)(i:Fin n)(h:(foo i)<n),  (nat_finite (foo i) h) = i.
-- 3.  finite_nat_id:
      forall (n:nat)(i:Fin n), (nat_finite (foo i) (finite_lt_n i)) = i.
-- 4.  foo_emb : forall n (i : Fin n), foo (emb i) = foo i.
-- 5.  foo_rvtp:  forall n : nat, foo (rv (tp n)) = 0.
-- 6.  foo_tp : forall n, foo (tp n) = n.
 
*)  

 Ltac foosimpl :=
      match goal with
      | [ |- context[foo (emb ?x) ]] =>  
            let H := constr:(foo_emb x) in rewrite H 
      | [ |- context[foo(rv (tp ?x))]] => 
           let H := constr:(foo_rvtp x) in rewrite H
      | [ |- context[foo(tp ?x)]] => 
           let H := constr:(foo_tp x) in rewrite H
      | |- context[(nat_finite (foo ?a) ?b)] =>  
         match goal with
         | [ i : Fin ?n |- _ ] =>
             match goal with
             | [ H : (foo i) <  n |-  _ ] => 
                     let E := constr:(finite_nat_id_general i H) in rewrite E
             end
         end      
      | [ n : nat, m : nat |- context[foo ?X] ] => 
            match type of X with
            | Fin n => 
                 match goal with
                 [ H : m < n  |- _ ]  =>  
                  let E := constr:(nat_finite_id H) in rewrite E
                 end
            end   
      | [ |- context [nat_finite (foo ?i) (finite_le_n ?i)] ] =>
             let H := constr:(finite_nat_id i) in rewrite H 
     end.


  (** Repeatedly rewrite using foosimpl - rewriting all cases *)
  Ltac fooSimpl := repeat foosimpl.


 (** rewrites cases where 0 occur at the non-recursive argument *)
  Ltac rewrite_right_0' :=
    match goal with
    | [|- context [(?x - 0 ) ] ] => 
         match type of x with
          | nat => let H := constr:(minus_n_O x) in rewrite <- H
          end
    | [|-  context [(?x + 0 ) ] ] => 
         match type of x with
          | nat => let H := constr:(plus_n_O x) in rewrite <- H
          end
    | [|- context [(?x * 0 ) ]]  => 
         match type of x with
          | nat => let H := constr:(mult_0_r x) in rewrite  H
          end     
    end.
   
   (* repeatedly rewrite cases with 0  at the non-recursive argument *)
   Ltac rewrite_right_0 := repeat rewrite_right_0'.
   
 (* rv i = n - i - i *) 
 Lemma rv_foo_m1 : forall n (i : Fin n),  foo (rv i) = n - (foo i) - 1.
   induction i; simpl; foosimpl; rewrite_right_0; auto. 
 Qed.

 (* 

 rewrites using :
1. forall n m, (n + m - n) = m
2. n - n = 0
3. n <= m ->  n + (m - n) = m
 
*)
  Ltac minus_simpls :=
    match goal with
    | [|- context [(?n -?n)]] => 
          let H := constr:(minus_diag n) in rewrite H
    | [|- context [(?n + ?m - ?n) ]] => 
          let H := constr:(minus_plus n m) in rewrite H
    | [H : ?n <= ?m |- context[ ?n + (?m - ?n)]] =>
          let Eq := constr:(le_plus_minus_r _ _ H) in rewrite Eq
   end.

 Ltac minus_simpl := repeat minus_simpls.
      
 Ltac Foosimpl :=
    let rvFoo := (
         match goal with
         | [|- context[foo(rv ?x)]] => 
              let E := constr:(rv_foo_m1 x) in rewrite E
         end) in  repeat (rvFoo ||  foosimpl).
  
 Ltac FooSimpl := progress Foosimpl. 

 (**  Obvious results that can be deduced form m < n  *)
 Lemma n_minus_le : forall (n m : nat), m <= n ->  (n - m - 1) <= n. 
 Proof.
   intros; omega.
 Qed.

 Lemma n_minus_lt : forall (n m : nat), m < n ->  (n - m - 1) < n. 
 Proof.
   intros; omega.
 Qed.

 Lemma one_minus_nm : forall (n m : nat), m < n -> 1 <= n - m.
 Proof.
    intros; omega. 
 Qed.

 Lemma one_minus_nm_minus_1 : forall n m, m < n -> 1 <= n - (n - m - 1).
 Proof.
   intros; omega.
 Qed.
 
 (** check for a <= b and a < b in the context and then use the
    preceeding lemmas as assimptions *)
 Ltac nm_minus1 :=
   match goal with
   | [ H : ?a <= ?b , Hyp : ?a < ?b |- _ ] =>
       match type of a with
       | nat => 
          let H := constr:(n_minus_le _ _ H) in
            let H1 := constr:(one_minus_nm _ _ Hyp) in
              let H0 := constr:(one_minus_nm_minus_1 _ _ Hyp) in
                let h0 := fresh "h0" in 
                  let h1 := fresh "h1" in 
                    let h := fresh "h" in 
                         set (h := H) ; set (h0 := H1); set (h1 := H0) 
       end
   end.

   (** if there is a (n - (foo i)) or ((foo i) - n) in the goal, we may need 
      to express the goal in terms of integers rather than natural numbers.
      Here we add (foo i) < n (and (foo i) <= n) to the context and some 
      deductions from them, which facilitates the conversion to integers *)
   Ltac add_foo_le_lt :=
      let if_foo_minus_i tac T :=
          (match T with
            | context [ ((foo ?x) - ?y) ] => Foosimpl || tac 
            | context [ (?x - (foo ?y)) ] => Foosimpl || tac
            | _ => fail 1
           end) in 
       match goal with  
       | [ i :  Fin ?n |- ( ?X = ?Y :> nat) ] => 
                  let set_le_lt := 
                     (let H := constr:(finite_le_n i) in
                        let H1 := constr:(finite_lt_n i) in
                          let H0 := fresh "H0" in let h := fresh "h" in 
                               set (H0 := H) ; set (h := H1) ) in
                   repeat (if_foo_minus_i set_le_lt X) ; repeat (if_foo_minus_i set_le_lt Y)     
        end.
              
  (** change equality between natural numbers to an equality between 
    integers, then try solving it using the ring tactic*)
  Ltac natEq_to_Zeq :=
     match goal with
    | [|- (?X = ?Y :> nat) ] =>
          apply inj_eq_rev; try intros ;
            repeat      (match goal with
                   | [|- context[Z_of_nat(?x + ?y)]] => 
                       let Ijp := constr:(inj_plus x y) in rewrite Ijp  
                   | [|- context[Z_of_nat(?x * ?y)]] => 
                       let Ijp := constr:(inj_mult x y) in rewrite Ijp 
                   | [ H : ?a <= ?b |-  context[Z_of_nat(?b - ?a) ]] =>
                       let Ijp := constr:(inj_minus1 _ _ H) in rewrite Ijp
                   | [ H : ?a > ?b |- context[Z_of_nat(?b - ?a) ]] =>
                       let Ijp := constr:(inj_minus2 _ _ H) in rewrite Ijp   
                  end) ; ring 
    end.

  (*Ltac natEq_to_Zeq := repeat natEq_to_zeq. *)

 (* put them together *)
 Ltac foo_minus := 
  rewrite_right_0 ;
    (add_foo_le_lt ;  nm_minus1 ; minus_simpl ; natEq_to_Zeq) .

(*  Lemma test : 
    forall (n : nat) ( i : Fin n), 
     (n - (n - (foo i) - 1) - 1) = foo i  - (n +  (foo i) - n) + foo i.
    intros; foo_minus. 
   Qed. *)

 (** * More arithmetic simplifications *)
  (* evaluations *)
   Definition lt_le_dec  n m : {n < m} + {~ n < m} :=
     match le_lt_dec m n with
     | left l => right (n < m) (le_not_lt m n l)
     | right l => left (~ n < m) l
     end.
   

 Lemma minus_gt_0 : forall n m, 0 < n - m -> m < n. 
   intros; omega. 
  Qed.

   Lemma not_minus : forall n m, ~(0 < n - m) -> m < n -> False. 
     intros. omega.
   Qed.
 
   
   Lemma not_minus1 : forall n m, ~ 0 < n - (n - m - 1) -> m < n -> False. 
     intros. omega.
   Qed.

  Lemma nminus_minus1 : forall a b, 0 < b -> a < b - (b - 1) -> a < 1.
    intros; omega.
  Qed.

   Lemma nm_minus_plus : forall n m, n < m - 1 -> n + 1 < m.
    intros; omega.
   Qed.

   Lemma minus1_nm a a0 : a0 < a -> a - (a - a0 - 1) - 1 = a0.
     intros;  omega.
   Qed.

(** Is this really necessary?  *)
  Ltac optimiseOmega_aux := 
     match goal with
     | [ H : ?m < ?n |- context[?n - ?m]] =>
             let h:= constr:(minus1_nm H) in rewrite h 
     | [ H : ?m < ?n  |- _ ] => 
          match m with 
          |  0  =>  match n with
                    | ?a - ?b => 
                       let h := constr:(minus_gt_0 _ _ H) in generalize h; clear H; intros
                   end
          end
     | [ H : ?a < ?b - 1  |- _] =>
           let K := constr:(nm_minus_plus H) in generalize K; clear H; intros

     | [ H : ~(?a  < ?n - ?m) , H1 : ?m < ?n |- _ ] =>
           match a with 
           | 0 => let Cn := constr:(not_minus  H H1) in destruct Cn
           end
     | [H : ~ ?a < ?n - (?n - ?m - ?k) , H1 : ?m < ?n |- _] =>
       match a with
       | 0 => match k with
              | 1 =>  let K := constr:(not_minus1  H H1) in destruct K
              end
       end
    
    | [H : 0 < ?b , H1 : ?a < ?b - (?b - 1) |- _ ] =>
             let K := constr:(nminus_minus1 H H1) in generalize K; 
                      clear H; clear H1; intros
     | [ H : ?X |- _ ] => 
         match X with
         | context[match ?y with  
                   | 0 => ?K
                   | S _ => ?K1
                   end ] =>  destruct y
         | context[lt_le_dec ?x ?y] => destruct (lt_le_dec x y)
         end
      (* simplify vlast * )
      | [ H : ?X |- _ ] => 
          let simpV := unfold vlast in *; unfold vhead in *; unfold vtail in *; simpl in * in
             match X with
             | context[vlast] => simpV
             | context[vfirst] => simpV
             end *)
     (* remove duplicate and redundant hypotheses*)
     |[ H : ?a < ?b ,  H1 : ?a < ?b |- _ ] => clear H1
     |[ H : ?a < ?b ,  H1 : ?b > ?a |- _ ] => clear H1
     |[ H : ?a < ?b ,  H1 : ?a <= ?b |- _ ] => clear H1
     |[ H : ?a < ?b ,  H1 : ?b >= ?a |- _ ] => clear H1
 
     |[ H : ?a > ?b ,  H1 : ?a > ?b |- _ ] => clear H1
     |[ H : ?a > ?b ,  H1 : ?b < ?a |- _ ] => clear H1
     |[ H : ?a > ?b ,  H1 : ?a >= ?b |- _ ] => clear H1
     |[ H : ?a > ?b ,  H1 : ?b <= ?a |- _ ] => clear H1

     |[ H : ?a <= ?b ,  H1 : ?a <= ?b |- _ ] => clear H1 
     |[ H : ?a <= ?b ,  H1 : ?b >= ?a |- _ ] => clear H1 
     | [ H : ?a - ?b - ?c < ?a ,   H1 : ?b < ?a  |- _ ] =>  match c with
                                                           | 1 => clear H 
                                                           end
     | [ H : ?a - ?b  < ?a ,   H1 : ?b < ?a  |- _ ] => clear H
    (* no do the same for integers  *)
     end.



(** 
------
 end of arithemetic conversion and simplification 
------
*) 

 (* Given an equality H :  t1 = t2 or H1 : JMeq t1 = t2, the tactic 
    "add_eq_then_tac H tac" adds H to the local context if H or 
     its symmetry does not already exist in the context, or it adds
     K if K is equivalent to H   *)

  Ltac add_hyp_then_aux1 H tac := 
   match type of H with
   | ?t1 = ?t2 => 
         match goal with
         | id : context [t1] |- _ => 
             match type of id with 
              | t1 = t2 => fail 2
              | t2 = t1 => fail 2
              | t1 = ?t3 => let E := constr:(sym_eq H) in
                              let H1 := constr:(trans_eq E id) in
                                  add_hyp_then_aux1 H1 tac
              end
         | _ =>  let Hyp := fresh "Hyp" in set (Hyp := H); tac
         end 
    | JMeq ?t1 ?t2 =>
          match goal with
         | id : context [t1] |- _ => 
             match type of id with 
              | JMeq t1 t2 => fail 2
              | JMeq t2 t1 => fail 2
              | JMeq t1 ?t3 => let E := constr:(sym_JMeq H) in
                                 let H1 := constr:(trans_JMeq E id) in
                                    add_hyp_then_aux1 H1 tac
              end
         | _ =>  let Hyp := fresh "Hyp" in set (Hyp := H); tac
         end 
    end.

 Ltac add_hyp_then_tac H tac :=
   match type of H with
   | ?t1 = ?t2 =>
           add_hyp_then_aux1 H tac 
   | JMeq ?t1 ?t2 =>
            add_hyp_then_aux1 H tac 
  end.


 (** naieve heuristic to determine whether to use finSN or finEmtp *)
 Ltac finSn_dest H := 
    match goal with
    | [  |- context [finEmtp ?i]] =>   destruct (finEmtp i)
         (*match i with
         | H =>  destruct (finEmtp i)
         end *)
    | _ => destruct (finSN H)
    end.


 (** * FSimpl  *)
 Ltac Finsimpl := 
   let finsplit_destruct H N :=
        (let fin_decomp H1 N1 :=
           (match N1 with
            | context [ ?a * ?b ] => destruct (fintimes _ _ H1)
            | S _  => finSn_dest H1
            | ?K    => let k := eval compute in K in
                          match k with
                          | 0    => inversion H1
                          end
            end) in
         
      match goal with
      | [  i : Fin ?n |- _ ] =>
          match goal with
          | _ => match N with
                 | ?n  + ?m =>  
                   match goal with
                   | [ i : Fin ?M |- _ ] =>
                        match M with
                        | m + n => 
                            match goal with
                            | [Jm : JMeq H i  |- _ ]  =>
                                let Eq := constr:(finsplit_rv_swap _ _ Jm) in
                                  let Eq1 := constr:(finsplit_rv_swap _ _ (sym_JMeq Jm)) in
                                     rewrite Eq  || rewrite Eq1
                            | [Jm : JMeq i H  |- _ ]  =>
                                let Eq := constr:(finsplit_rv_swap _ _ Jm) in
                                  let Eq1 := constr:(finsplit_rv_swap _ _ (sym_JMeq Jm)) in
                                     rewrite Eq || rewrite Eq1
                            end 
                        end
                    | _  =>  let Eq := constr:(match_simpl _ _ H) in
                                  rewrite Eq || destruct (finsplit _ _ H)
                    end
                
                  | _ => fin_decomp H N
                  end
          end
       end) in

    match goal with 
    | [x : ?A, y : ?A |- _ ] =>
             match goal with
             | [ H : JMeq x y |- _ ] =>
               let Eq := constr:(JMeq_eq H) in  
                 first [ rewrite Eq in * | rewrite <- Eq in *]; clear H
             end
    | [  H : fs _ = fz _ |- _ ] => inversion H
    | [  H : fz _ = fs _ |- _ ] => inversion H
    | [  |- context [finsplit _ _ (fin_inl ?x ?i) ] ] =>
             let H := constr:(finsplit_inl x i)  in rewrite H
    | [  |- context [finsplit _ _ (fin_inr ?x ?i) ] ] =>
             let H := constr:(finsplit_inr x i)  in rewrite H
    | [ H : fin_inl _ _ = fin_inr _ _ |- _ ] => 
              let H1 := constr:(finsplit_inl_inr _ _  H) in  destruct H1
    | [ H : fin_inr _ _ = fin_inl _ _ |- _ ] => 
              let H1 := constr:(finsplit_inl_inr _ _  (sym_eq H)) in  destruct H1
    
   (** fincase casefin - etc *)
    | [ |- context[fincase _ _ _ ] ] => unfold fincase; simpl; Finsimpl 
    | [ |- context [ ?f (fincase ?l ?r ?i) ] ] =>
            match type of f with
            | ?X -> ?Y => let Eq := constr:(f_fincase f l r i) in
                             rewrite Eq; simpl
            end
    | [ |- context [ (fincase ?f ?g (fs ?i)) ] ] =>
            match type of f with
            | Fin (S _) -> ?Y => let Eq := constr:(fincase1 f g i) in
                             rewrite Eq; simpl
            end
    | [ |- context [FinCase _ ?x (fin_inl  ?x ?i)] ] =>   
             let Eq := constr:(FinCase_inl x i) in rewrite Eq 
    | [ |- context [FinCase ?x _ (fin_inr  ?x ?i)] ] =>   
             let Eq := constr:(FinCase_inr x i) in rewrite Eq 
    | [ |- context [FinCase _ ] ] =>
           first  [ (match goal with
                   | [ |- context [sum_n _ ]] => fail 1
                   end) | (unfold FinCase; simpl;  Finsimpl) ]
    | [ |- context [CaseFin _ ] ] => unfold CaseFin; simpl;  Finsimpl
    | [ |- context [ FinCase _ _ (CaseFin ?i) ]] => 
            let Eq := constr:(FinCaseFin i) in rewrite Eq 
    | [ |- context [ CaseFin _ _ (FinCase ?i) ]] => 
            let Eq := constr:(CaseFinCase i) in rewrite Eq

    | [ |- context [finplus_swap _ _ _ ] ] => unfold finplus_swap; Finsimpl
    | [ H : fin_inl _ ?i = fin_inl _ ?j  |- _ ] => 
               let H1 := constr:(fin_inl_inject _ _ i j H) in
                  (rewrite H1; auto)  || add_hyp_then_tac H1 Finsimpl
    | [ H : fin_inr _ ?i = fin_inr _ ?j  |- _ ] => 
               let H1 := constr:(fin_inr_inject _ _ i j H) in
                  (rewrite H1; auto) || add_hyp_then_tac H1 Finsimpl
    | [ H : emb _ = emb _ |- _ ] =>
               let H1 := constr:(embInject H) in 
                  (rewrite H1; auto) || add_hyp_then_tac H1 Finsimpl
    | [ H : fs _ = fs _ |- _ ] =>
               let H1 := constr:(fsInject H) in 
                  (rewrite H1; auto) || add_hyp_then_tac H1 Finsimpl
   
    (** rewriting using proven results*)
    | [ |- context[rv (emb ?i) ] ] => let H := constr:(emb_S i) in
                  rewrite H  (*||  rewrite <- H *)
    | [ |- context [rv (rv ?i) ] ] => 
              let H := constr:(idem_rvFin i) in rewrite H
    | [ |- context [rot (un_rot ?i) ] ] => 
              let H := constr:(rot_un_rot_id i) in rewrite H
    | [ |- context [un_rot (rot ?i) ] ] => 
              let H := constr:(un_rot_rot_id i) in rewrite H
    | [ |- context [emb (fin_inl 0 ?i) ] ] => 
              let H := constr:(fininl_embO i) in rewrite H
    | [ |- context [rv (fin_inl 0 ?i) ] ] => 
              let H := constr:(rv_fin_inlO i) in rewrite H
    | [ H : rv _ = rv _ |- _ ] => let H1 := constr:(rvInject _ _ H) in 
               rewrite H1 || add_hyp_then_tac H1 Finsimpl
    | [ H : rot ?i = rot ?j |- _ ] => let H1 := constr:(rot_inject _ _ H) in 
               rewrite H1 || add_hyp_then_tac H1 Finsimpl 
    | [ H : un_rot _ = un_rot _ |- _ ] => let H1 := constr:(un_rot_inject _ _ H) in 
               rewrite H1 || add_hyp_then_tac H1 Finsimpl
    | [ H : ?n = ?m |- _ ] =>  
         match goal with     
         | [ i : Fin n, j : Fin m, Hj : JMeq (rv ?i) ?j |- _ ] => 
             let Eq := constr:(rvdistJM H Hj) in add_hyp_then_tac Eq Finsimpl
         end
    | [ i : Fin ?n |- _ ] =>
         match goal with
          (* discharge some contradictions *)
          | [ H1 : ?m + ?x = ?z + ?y , 
              H2 : JMeq (fin_inl ?a (?m + ?x) i) (fin_inr (?a + ?z) ?y ?j) |- _ ] =>
               let C := constr:(fin_inl_inrN m x z H1 H2) in destruct C        
          | [ C : emb i = fs i |- _ ] => 
                       let H1 := constr:(fs_emb (sym_eq C)) in destruct H1
          | [ C : fs i = emb i |- _ ] => 
                       let H1 := constr:(fs_emb C) in destruct H1
          | [ C : tp n = emb i |- _ ] => 
                       let H1 := constr:(tp_emb C) in destruct H1
          | [ C : emb i = tp n |- _ ] => 
                       let H1 := constr:(tp_emb (sym_eq C)) in destruct H1
          | [ C : emb (tp (S _ )) = fz (S (S _ )) |- _ ] => 
                       let H1 := constr:(emb_tpm C) in destruct H1
          | [ C : fz (S (S _ )) =  emb (tp (S _ )) |- _ ] => 
                       let H1 := constr:(emb_tpm (sym_eq C)) in destruct H1
          | [ C : rv (fz ?m)  = rv (fs i) |- _ ] => 
                       let H1 := constr:(fsFz i C) in destruct H1
          | [ C : rv (fs i)  = rv (fz ?m) |- _ ] => 
                       let H1 := constr:(fsFz i (sym_eq C)) in destruct H1
          | [ C : JMeq (fin_inl (S ?m)  ?i) (fin_inl _ ?m (fs ?i)) |- _ ] =>
                    let K := constr:(fin_Jmeq_l _ _ C) in destruct K
          | [ C : JMeq (fin_inr _ _) (fin_inl _ (fin_inl _ _)) |- _ ] =>
                   let K := constr:(Jmeq_fin_inl_inr3 _ _ _ _ _ C) in destruct K 
        
         (** augment the hypothesis space *)
         | [ |- context [rv (fin_inl _ _ ) ] ]  =>
                   let K := constr:(rvFin_inl _ i) in  add_hyp_then_tac K Finsimpl
         | [ |- context [fin_inr _ (rv ?i ) ] ] =>
                   let K := constr:(rvFin_inl _ i) in add_hyp_then_tac K Finsimpl
         | [|- context[fs (fin_inr ?m ?i)] ]  =>
             let Jeq := constr:(fin_Jmeq m i)  in add_hyp_then_tac Jeq Finsimpl
         | [|- context[emb (fin_inr ?m ?i)]]  =>
             let Jeq := constr:(JM_rvEmb m i)  in add_hyp_then_tac Jeq Finsimpl
         | [|- context[rv (fin_inl ?m ?i)]]  =>
             let Jeq := constr:(rvFin_inl m i)  in add_hyp_then_tac Jeq Finsimpl
         | [|- context[rv (fin_inr ?m ?i)]]  =>
             let Jeq := constr:(rvFin_inr m i)  in add_hyp_then_tac Jeq Finsimpl
         | [|- context[(fin_inr ?a (?x + n) (fin_inr ?x i)) ]] =>
             let Jeq := constr:(fin_inr_inr a x i)  in add_hyp_then_tac Jeq Finsimpl
         | [ H : JMeq (fin_inr 0 n i) (fin_inl n 0 ?j) |- _ ] => 
             let Req := constr:(inl_inr_eq H) in
                   rewrite H || add_hyp_then_tac Req Finsimpl
         | [ H : JMeq (fin_inl n 0 i) (fin_inr 0 n ?j) |- _ ] => 
             let Req := constr:(inl_inr_eq (sym_JMeq H)) in
                  rewrite H || add_hyp_then_tac Req Finsimpl

          | [ j : Fin ?m |- _ ] =>
              match goal with
              | [  H : ?N = m,  H1 : JMeq (fin_inl _ i)(fin_inl _ j)  |- _ ] =>  
                 let Eqt := constr:( fin_inlJm _ H _ _ H1) in
                    let Eqt1 := constr:( fin_inlJm _ (sym_eq H) _ _ (sym_JMeq H1)) in
                      add_hyp_then_tac Eqt Finsimpl || add_hyp_then_tac Eqt1 Finsimpl 
                      (* fin_inl_inrZ1*)

              | [  H : ?N = m,  H1 : JMeq (fin_inr _ i)(fin_inr _ j)  |- _ ] =>  
                  let Eqt := constr:(fin_inrJm _ H _ _ H1) in (* here *)
                     let Eqt1 := constr:(fin_inrJm _ (sym_eq H) _ _ (sym_JMeq H1)) in
                       add_hyp_then_tac Eqt Finsimpl || add_hyp_then_tac Eqt1 Finsimpl

              | [ H : ?N = m,  H0 : JMeq (fs i) (fs j) |- _  ] =>
                   let Ieqj := constr:(Jmeq_fsInject H H0) in
                     let Ieqj1 := constr:(Jmeq_fsInject (sym_eq H) (sym_JMeq H0)) in
                       add_hyp_then_tac Ieqj Finsimpl || add_hyp_then_tac Ieqj1 Finsimpl

              | [ H : m = ?N,  H0 : JMeq (fs j) (fs i) |- _  ] =>
                  let Ieqj := constr:(Jmeq_fsInject H H0) in
                    let Ieqj1 := constr:(Jmeq_fsInject (sym_eq H) (sym_JMeq H0)) in
                        add_hyp_then_tac Ieqj Finsimpl || add_hyp_then_tac Ieqj1 Finsimpl

              | [  H : ?N = m ,  H1 : JMeq i j  |- _ ] =>  
                   destruct H; let Eqt := constr:(JMeq_eq H1) in 
                        rewrite Eqt ||  rewrite <- Eqt || add_hyp_then_tac Eqt Finsimpl

              | [  H : m = ?N ,  H1 : JMeq j i  |- _ ] =>  
                 destruct H; let Eqt := constr:(JMeq_eq H1) in
                      rewrite Eqt ||  rewrite <- Eqt || add_hyp_then_tac Eqt Finsimpl
               end (*  return here *)
     
         | _ =>  finsplit_destruct i n
         (* need to add a few caseses*)
         end
    end.


 (** Repeatedly apply the above rewrites and finSumn_simplify *)
  Ltac FSimpl := 
     repeat (FooSimpl || Finsimpl || finSumn_simplify) ; auto.

 (** Combining FSimpl with the conversion integers. foo_minus *)

 Tactic Notation "FSimpl" "with" "arith" :=
    let prog_foo := progress FSimpl in
     repeat (prog_foo || foo_minus || auto with arith).


  Ltac  optimiseOmega := 
       repeat  optimiseOmega_aux; rewrite_right_0 ; minus_simpl; 
               repeat (foo_minus || auto with arith).
