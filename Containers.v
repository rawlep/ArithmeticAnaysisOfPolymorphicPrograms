Require Import JMeq Substitution.

(** * Unary Contaienrs  *)
Set Implicit Arguments.

Section preliminaries.  

 Definition sumPos (S1 S2:Type) (f : S1 -> Set)  
                    (g : S2 -> Set) (H: S1 + S2)  :  Set :=
    match H with
    | inl a => f a
    | inr a => g a
    end. 
 
 Definition comp (A B C : Type) (g : B -> C) (f  : A ->B) (a : A) :
                 C := g (f a). 
  Notation " f <o> g " := (comp f g) (at level 20).
 
 Definition id (A:  Type):= fun a:A => a.
     
 (* Family of "being true" *)
 Inductive So:  bool ->  Set := oh : So true.
 Definition notSo (X:Set) (p: So false) : X.
    intros X p; inversion p.
 Defined.

  (** Isomorphisms *)
  Inductive Iso (A B : Type) : Type :=
    isIso : { ab : A -> B & 
            { ba : B -> A & (forall a, ba (ab a) = a) -> 
                            (forall b, ab (ba b) = b) }} -> Iso A B.

  

  Section Extensionality. 
  (** need to assume extensionality  *)
   Axiom extensionality : forall (A B: Type)  (f g: A ->  B ),  (forall a , f a = g a )-> f =g. 


   Axiom exTd 
     : forall (A : Type) (B : A -> Type) (F G : forall (a : A) , B a),
       (forall a ,  F a  = G a ) -> F =  G.

  (** Other Dependent versions can now be defined *)
  Definition extN (A : Type) (Q B: A -> Type) (f g : forall n, Q n -> B n) :
     (forall n (i j : Q n), i = j ->  f n i = g n j) -> f = g :=
     fun H => 
        exTd (fun n => Q n -> B n) f g (fun n => 
         extensionality (f n) (g n) (fun i => H n i i (refl_equal i))).



   Definition  dextensionality :
     forall (A C : Type) (B : A -> Type) (a a' : A) (H : a = a')
          (F  : B a -> C) (G : B a' -> C), 
         (forall (x : B a) (y : B a'), JMeq x y ->  F x = G y) -> JMeq F G.
     intros A C B a a' H; case H.
     intros F G H0; 
     case  (extensionality F G (fun a0 : B a => H0 a0 a0 
         (eq_subs (fun x : B a => JMeq x a0) (refl_equal a0) (JMeq_refl a0))));
     trivial.
   Defined.

  Lemma eq_JMeq : forall A (x y : A), x = y -> JMeq x y.
     intros A x y H; destruct H; auto.
  Qed.
  
  (** and so can an even have  more general dependent version *)
   Definition  Jmextensionality : forall (A B : Type)
                                  (Q : forall A, Set) 
                                  (P : forall  B, Set) 
                                  (h h1 : A -> B)  (H : h = h1)
                                  (f : forall a: A, P (h a) -> Q a) 
                                  (g: forall a: A, P (h1 a)  -> Q a ) , 
                                  (forall (a: A) (p : P (h a)) (p1 : P (h1 a)), 
                                  JMeq p p1 ->  f a p = g a p1) ->  JMeq f g.
       intros A B Q P h h1 H; rewrite H.
       intros .  rewrite  (extN (A := A) (fun a => P (h1 a)) Q f g  
             (fun a i j H1 => H0 a i j (eq_JMeq H1)) ); trivial.
   Defined.

 End Extensionality. 

End preliminaries.
Implicit Arguments id [ ].

Section Unitary_containers.
(** Definitions of Unary Containers  *)
     
 Record Ucontainer : Type := ucont  { s: Type;  p: s -> Set}.

 (*Open Scope Container_scope. *)
 
(** Contaeinr morphism *)    
 Record cmr C D :Type := 
      uCmr {v: s  C -> s D; g: forall a: s C, p D (v a) -> p C a }.

 Record ccmr C D : Type :=
      cCmr { cv : s C -> s D; cg : forall a : s C, Iso (p D (cv a)) (p C a) }.

 Implicit Arguments uCmr [C D]. 

  
 (*Identity on Ucontainer morphism *) 
 Definition idm  C : cmr C C:= 
     uCmr (id (s C)) (fun z: s C => fun x:  p C ((id (s C)) z) =>  x).  

 (** identity cartesian morphisms *)
 Definition idcm C : ccmr C C.
  intros. refine ( cCmr _ _ (id (s C)) _ ).
  intros.  apply isIso. unfold id;  simpl.
  exists (id (p C a)). exists (id (p C a)).
  unfold id; simpl. exact (fun a => a).
 Defined.
    
 
 (** composition of Ucontainer morphisms *)
 Definition m_comp C D E  (de : cmr D E) (cd : cmr C D) : cmr C E :=
 match de with
| uCmr v0 g0 =>
    match cd with
    | uCmr v1 g1 =>
        uCmr (C:=C) (D:=E) (comp v0 v1)
          (fun (sc : s C) (pe : p E (comp v0 v1 sc)) =>
           comp (g1 sc) (g0 (v1 sc)) pe)
    end
end.

Section equality_of_container_morphisms.
  (**  * Equality of Container Morphisms *) 
 Variables C D : Ucontainer    .     
          
 (* equality of container morphisms  *)
 Inductive Eqmor (i j : cmr C D)   :   Prop := 
     morq : (forall a : s C,  v i a  = v j a ) ->
                 (forall (a : s C) (p0 : p D (v i a)) (p1 : p D (v j a)),  JMeq p0 p1 ->  
                 g i a p0 = g j a p1)  ->   Eqmor i j.
       
 (* reflexivity of this equality  *)
 Definition refl_eqm  (i : cmr C D) :     Eqmor i i :=
   morq i i (fun a : s C => refl_equal (v i a)) 
    (fun (a : s C) (p0 p1 : p D (v i a)) (H : JMeq p0 p1) => 
        JMeq_ind (fun p2 : p D (v i a) => g i a p0 = g i a p2) (refl_equal (g i a p0)) H).
                   
 (* symmetry of this equality  *)
 Definition sym_eqm (i j : cmr C D) (eij : Eqmor i j) : Eqmor j i :=
   match eij with 
   | morq H H0 =>
      morq j i (fun a : s C => sym_eq (H a))
         (fun (a : s C) (p0 : p D (v j a)) (p1 : p D (v i a)) (x : JMeq p0 p1) =>
          sym_eq (H0 a p1 p0 (sym_JMeq x)))
   end.

 (* Contaienr morphism equality implies leibez equality *)
 Lemma hom_eqmor (i j : cmr C D): v i = v j -> JMeq (g i) (g j) -> i = j.
 Proof.
   intros i j;  destruct i; destruct j; simpl.
   intro H;  destruct H; intro H0; elim H0; reflexivity. 
 Qed.

      
 (* analogous to JMeq_eq *)
 Lemma eqm_eq : forall (i j : cmr C D) ,  Eqmor i j -> i = j.
 Proof.
    intros i j E;  destruct E; destruct i; destruct j; simpl in * |- *.
    apply (hom_eqmor (uCmr v0 g0) (uCmr v1 g1)).  
    exact  (extensionality  v0 v1 H). simpl. 
    exact (Jmextensionality (p C ) (p D)  (extensionality  v0 v1 H) g0 g1 
              (fun a p0 p1 j1 => H0 a p0 p1 j1)). 
 Qed.
                               
 (** substitutivity  of container equality  *)
 Definition subst_eqm (i j : cmr  C D) (P : cmr C D -> Type) (qij : Eqmor i j)  (Pi : P i) : P j :=   
       eq_rect i (fun j0 : cmr C D => P j0) Pi j (eqm_eq qij)  . 

 (* transitivity *)
 Definition trans_eqm :=
   fun (i j k : cmr C D) (eqij : Eqmor i j) (eqjk : Eqmor j k) =>
     eq_ind i (fun _ : cmr C D => Eqmor i k)
     (eq_ind j (fun k0 : cmr C D => Eqmor i k0) eqij k (eqm_eq eqjk)) j
     (eqm_eq eqij).

End equality_of_container_morphisms.

(** Compositions of container morphisms are associative*)
 Lemma m_comp_assoc A B C D  (ab : cmr A B) (bc : cmr B C) (cd : cmr C D):
   Eqmor (m_comp (m_comp cd bc) ab) (m_comp cd (m_comp  bc ab) ).
 Proof.
  intros A B C D ab bc cd;
  destruct ab as [v0 g0 ]; destruct bc as [v1 g1]; 
  destruct cd as [v2 g2]; unfold comp; simpl. 
  apply morq; unfold comp; simpl; auto.
  intros a p0 p1 H;
  apply    (JMeq_rect  (fun x : p D (v2 (v1 (v0 a))) => 
            g0 a (g1 (v0 a) (g2 (v1 (v0 a)) x)) =
            g0 a (g1 (v0 a) (g2 (v1 (v0 a)) p1)))
            (refl_equal (g0 a (g1 (v0 a) (g2 (v1 (v0 a)) p1)))) (sym_JMeq H)).
Qed.
           

Section extension_of_containers.
            
 (** Every container give rise to a functor called its  its extension *)
 Record Ext S (X:Type) : Type := uext {u: s S;  f: p S  u -> X }.
 Implicit Arguments uext [S X].
(* Notation " [S : X ] " := (Ext S X) (at level 30) : Container_scope. *)

 Lemma ext_eq C  (X: Type) (s1 s2: s C)  (f : p C s1 -> X) (f' : p C s2 -> X): 
                s1 = s2 -> JMeq f f' -> uext s1 f = uext s2 f'.
 Proof.
   intros C X s1 s2 f0 f1 H; destruct H.
   intro H1; elim  H1; reflexivity.
 Qed. 

Lemma  ext_eq_dst C  (X:Type) (xs xy : Ext C X) : 
            xs = xy  -> (u xs) = (u xy) /\  JMeq (f xs) (f xy).
Proof.
  intros C X xs xy H; case  H; auto.
Qed.
  
(** Ext is really a functor: an arrow f : X -> Y in Set give rise to
   the arrow Ext C X -> Ext C Y in (Ext C ?K)  *)
Definition cmap C  (X Y : Type) (f : X -> Y) (c : Ext C X) : Ext C Y :=
    match c with
    | uext u0 f0 => uext u0 (comp f f0)
    end.

(* the identity os preserved  *)
Theorem  cmap_id C  (X : Set) (ex : Ext C X ) : cmap (id X) ex =  ex.
Proof.
  intros C X ex; unfold cmap; unfold id; unfold comp. 
  destruct ex; simpl.
  rewrite (extensionality (fun a : p C u0 => f0 a) f0 (fun a : p C u0 => refl_equal (f0 a)));
  reflexivity.
Qed.   

(* ... and also composition  *)
Theorem cmap_comp C  (X Y Z : Set) (f : X -> Y) (g : Y -> Z) (ex : Ext C X) :
  cmap (comp g f) ex = cmap g (cmap f ex).
Proof.
  intros C X Y Z f0 g0 ex;  unfold cmap; destruct ex; trivial.
Qed.

 (*unary containers give rise to a natural transformation  *)
 Definition mmap C D (cm: cmr C D) (X: Type) (cx :  Ext C X) : Ext D X := 
   match cx with 
   | uext u0 f0 => uext (v cm u0)  (comp f0 (g cm u0) )
   end .

 Definition mor_map C D (X Y : Set)  (cm: cmr C D ) 
      (f: X -> Y) (ex :  Ext C X)  :  Ext D Y := mmap cm (cmap f ex).


 (** lift a natural transformation  to a Ucontainer morphism  *)
 Definition ext_mor C D (nt: forall X:Set,  Ext C X -> Ext D X) : cmr C D :=
     let m (b:s C ): Ext D (p C b ) :=  nt (p C b) (uext  b (fun q: p C b => q)) in 
         let v' :=  fun z: s C => u (m z) in
              uCmr v' (fun w: s C => fun a: p D (v' w) => f (m w) a). 

 Lemma ext_mor_mmap C D (cm : cmr C D) : Eqmor cm (ext_mor (mmap cm)).
 Proof.
   intros. destruct cm. unfold mmap; unfold ext_mor;
   unfold comp; apply morq; simpl; trivial.
   intros a p0 p1 H; rewrite (JMeq_eq H); trivial.
 Qed.


Lemma mmap_ext_mor C D (nt: forall X:Set,  Ext C X -> Ext D X):
  forall (X : Set) (u0 : s C) (f0 : p C u0 -> X),  
   mmap ( ext_mor nt) (X := p C u0) (uext u0 (fun q : p C u0 => q)) =
   nt (p C u0) (uext u0 (fun q : p C u0 => q)). 
 Proof.  
   unfold ext_mor; unfold mmap; simpl; unfold comp.
   intros. destruct (nt (p C u0) (uext u0 (fun q : p C u0 => q))); simpl.
   replace (fun a : p D u1 => f1 a) with f1; trivial.
   exact (extensionality  f1 (fun a : p D u1 => f1 a) (fun a => refl_equal (f1 a)) ).
 Qed.   
 
  (* the naturality property for the Extension functor - I dont really need this 
 Inductive Natural A B  (Y Z : Type) (f : Y -> Z) :
     (forall X, Ext A X -> Ext B X) -> Type :=
  | natt : forall (nt : forall X, Ext A X -> Ext B X),
      comp (cmap (C := B) f) (nt Y)  = comp (nt Z) (cmap (C := A) f) -> Natural f nt. 
 *)

(*End extension_of_containers. *)

(** mmap preserves equality of container moprhisms *)
Lemma mmap_eqmor C D (ab ba: cmr C D) : Eqmor ab ba -> 
   forall X :Set, (mmap ab) X = (mmap ba) X.
 Proof.
  intros C D ab ba H.
  apply (subst_eqm (fun cd : cmr C D => forall X : Set, mmap ab (X:=X) = mmap cd (X:=X)) H 
   (fun X : Set => refl_equal (mmap ab (X:=X)))).
Qed.

   
 (* mmap is a natrual transformation - i.e. the diagram commutes*)
 Lemma mmap_nt C D (X Y : Set) (f : X -> Y) (cm : cmr C D) : 
     comp (mmap cm (X := Y))(cmap (C := C) f) = comp (cmap (C :=D) f)(mmap cm (X := X)).
 Proof.
  unfold mmap; unfold cmap; intros; unfold comp.
  apply extensionality.  intro a ; destruct a; trivial. 
 Qed.  

 (* naturality law *)
 Lemma cmap_mor_map C D (X Y : Set) (F : X -> Y) :
   forall (cm : cmr C D) (ex : Ext C X) ,  (cmap F (mmap cm ex)) = (mor_map cm F ex). 
    destruct ex; destruct cm ; unfold mor_map; unfold comp; simpl; trivial.
 Qed. 

End extension_of_containers.

          
Section constructions.

Set Implicit Arguments.

 Inductive Empty: Set := . 
 (*  Zero , One , Unary and maybe containers  *)     
 Definition  Zero_cont := ucont (fun _:  Empty   => Empty ).
 Definition One_cont := ucont (fun _:unit => Empty). 
 Definition Un_cont : Ucontainer := ucont (fun a:unit => unit ).
 Definition maybe_cont :  Ucontainer := ucont (fun  a:bool => So a).

   
 Section   Products_Sums_and_Compositions.
   (** * Sums Products and Compositions *)
  
    Section PSC_Definitions. 

    Variables C D : Ucontainer .

    Definition cont_prod  :=   
          ucont (fun q : (s C) * (s D) => (sum (p C (fst q)) (p D (snd q)))).
    Definition cont_sum  := ucont (sumPos (p C) (p D) ).

    (* CPos - the positions in a composion  *) 
    Record CPos (a : Ext C (s D) )  : Set := 
             cpos {cs : p C (u a) ; cp :  p D ((f a) cs)}.

    Lemma cpos_eq (a : Ext C (s D))  (x y : CPos a) : 
                  (cs x) = (cs y ) -> JMeq (cp x) (cp y) -> x = y.
    Proof.
     intros  a x y; destruct x; destruct y; simpl.
     intro H; destruct H. intro H; elim H; trivial.
    Qed.

    Lemma dst_cpos_eq (a : Ext C (s D)) (x y : CPos a) : 
        x = y -> cs x = cs y /\ JMeq (cp x) (cp y) .
    Proof.
      intros a x y ; simpl in *. intro H; destruct H; auto.
    Qed.   

    Lemma cpos_Jmeq  (a b : Ext C (s D))  (H : a = b)  (ca : CPos a) (cb : CPos b):
      JMeq ca cb -> JMeq (cs ca) (cs cb) /\ JMeq (cp ca) (cp cb).
    Proof.
     intros a b H; elim H. 
     intros ca cb H0; elim H0; auto.
    Qed.

    Lemma cpos_unique : forall (a : Ext C (s D) ) (x : CPos a),
        x = cpos a (cs x) (cp x).
    Proof.
      intros a x ; destruct x; trivial.
   Qed.

    (* composition of containers *)
    Definition cComp : Ucontainer :=   ucont (fun a : Ext C (s D)  => CPos a) .

    End PSC_Definitions.

  

  (**  We now prove that the extension of product/coproduct/composition of containers 
      are the pointwise product/coproduct/composition of their extension. *)
  
     (** ** Products *)
    Definition  extP  C D : forall X, Ext (cont_prod C D) X ->  prod (Ext C X) ( Ext D X) :=
      fun (X : Type) (H : Ext (cont_prod C D) X) =>
        match C as u return (Ext (cont_prod u D) X -> Ext u X * Ext D X) with
          | ucont s0 p0 =>
            fun H0 : Ext (cont_prod (ucont p0) D) X =>
              match D as u return (Ext (cont_prod (ucont p0) u) X -> Ext (ucont p0) X * Ext u X)
                with
             | ucont s1 p1 => fun H1 : Ext (cont_prod (ucont p0) (ucont p1)) X =>
                match H1 with
               | uext u0 f0 =>
                 (let (s2, s3) as p return
                   ((p0 (fst p) + p1 (snd p) -> X) ->
                    Ext (ucont p0) X * Ext (ucont p1) X) := u0 in
                  fun f1 : p0 (fst (s2, s3)) + p1 (snd (s2, s3)) -> X =>
                      (uext (ucont p0) s2 (fun i : p0 s2 => f1 (inl (p1 s3) i)),
                     uext (ucont p1) s3 (fun i : p1 s3 => f1 (inr (p0 s2) i)))) f0
             end
           end H0
        end H.

        
   Definition  extP1 C D  X  (H : Ext C X * Ext D X) := 
    let (e, e0) := H in  uext (ucont (fun q : s C * s D => (p C (fst q) + p D (snd q))%type))
     (u e, u e0)
     (fun H0 : p C (u e) + p D (u e0) =>
       match H0 with
         | inl p0 => f e p0
         | inr p0 => f e0 p0
         end).

  (** extP and extP1 are isomorphic *)
  Lemma iso_extP_P1 : 
     forall C D X (H: Ext C X  *  Ext D X ),  extP(extP1 H) = H.
  Proof.
    intros C D  X H.
    destruct C; destruct D; destruct H;  simpl in *.
    rewrite  (extensionality (fun i : p1 (u e0) => f e0 i) (f e0)
     (fun a :  p (ucont p1) (u e0) => refl_equal (f e0 a)) ). 
    rewrite  (extensionality (fun i : p0 (u e) => f e i)(f e)
     (fun a :  p (ucont p0) (u e) => refl_equal (f e a))).
    destruct e; destruct e0; simpl in *; trivial.
 Qed.
 
 Lemma iso_extP1_P C D X  (H: Ext (cont_prod C D) X) : extP1 (extP H) = H.
 Proof.
   unfold cont_prod; intros C D X H. 
   destruct C; destruct D; destruct H .
   destruct u0; simpl in *. apply ext_eq; trivial.
   replace  (fun H0 : p0 s2 + p1 s3 =>
      match H0 with
      | inl p2 => f0 (inl (p1 s3) p2)
      | inr p2 => f0 (inr (p0 s2) p2)
      end) with f0; trivial.
   apply extensionality. intro a ; destruct a; trivial.
 Qed.

(** ** Sums *)
 Definition  extS C D : forall X ,   Ext (cont_sum C D) X -> (Ext C X) + ( Ext D X) :=
  fun X cS => match cS with
   | uext u0 f0 =>
     match u0 as s return
       ((p (cont_sum C D) s -> X) -> Ext C X + Ext D X) with
     | inl s0 =>
        fun f1 : p (cont_sum C D) (inl (s D) s0) -> X =>
          inl (Ext D X) (uext C s0 f1)
     | inr s0 =>
        fun f1 : p (cont_sum C D) (inr (s C) s0) -> X =>
           inr (Ext C X) (uext D s0 f1)
     end f0
   end.

 Definition extS1 C D X  (H : (Ext C X) + ( Ext D X)) : Ext (cont_sum C D) X :=
  match H with
  | inl e => uext (ucont (sumPos (p C) (p D))) (inl (s D) (u e)) (f e)
  | inr e => uext (ucont (sumPos (p C) (p D))) (inr (s C) (u e)) (f e)
  end.

 (* extS and extS1 are isomorphic *)
  Lemma iso_extS_S1 C D X : forall H :  Ext (cont_sum C D) X,  extS1 (extS H) = H.
  Proof.
   intros C D X H; destruct H as [u0 f0];
   destruct u0;  simpl; trivial.
 Qed.

 Lemma iso_extS1_S C D X :  forall H :  Ext C X + Ext D X, extS (extS1 H) = H.
 Proof.
  intros C D X H; destruct H as [e | e0].
  destruct e;  trivial.
  destruct e0;  trivial.
 Qed. 
 
 (** ** Compositions *)
 Definition extC C D X : Ext (cComp C D) X -> comp (Ext C) (Ext D) X :=
  fun (H : Ext (ucont (fun a : Ext C (s D) => CPos D a)) X) =>
   match H with
   | uext u0 f0 =>
    uext C (u u0)
      (fun pc : p C (u u0) =>
       uext D (f u0 pc) (fun pdf : p D (f u0 pc) => f0 (cpos D u0 pc pdf)))
   end.
 

Definition  extC1 C D : forall X : Type,  comp (Ext C) (Ext D) X  ->  Ext (cComp C D) X :=
  fun (X : Type) (ex : Ext C (Ext D X)) =>
   uext (ucont (fun a : Ext C (s D) => CPos D a))
    (uext C (u ex) (fun x : p C (u ex) => u (f ex x)))
     (fun a : CPos D (uext C (u ex) (fun x : p C (u ex) => u (f ex x))) =>
       f (f ex (cs a)) (cp a)) .

Lemma iso_extCl_C C D X :  forall ex : Ext (cComp C D) X, extC1 (extC ex) = ex.
Proof.
  intros C D X ex.
  destruct ex; unfold extC1; unfold cComp; simpl in *.
  apply ext_eq; destruct u0; simpl.
  rewrite  (extensionality (fun x : p C u0 => f1 x) f1
           (fun x: p C u0 => refl_equal (f1 x))); trivial.
  apply  (dextensionality (CPos (C := C) D)
       (sym_equal (ext_eq C (refl_equal u0)
         (eq_subs (fun F : p C u0 -> s D => JMeq f1 F)
         (extensionality f1 (fun x : p C u0 => f1 x) 
           (fun x: p C u0 => refl_equal (f1 x)))
           (JMeq_refl f1)
         )))
        (fun a : CPos (C := C) D (uext C (X := s D) u0 (fun x : p C u0 => f1 x)) =>
      f0 (cpos D (uext C (X := s D) u0 f1) (cs a) (cp a))) f0 ).
  intros .
  apply (f_equal f0). 
  destruct  (cpos_Jmeq 
             (sym_equal (ext_eq C (refl_equal u0)
         (eq_subs (fun F : p C u0 -> s D => JMeq f1 F)
         (extensionality f1 (fun x : p C u0 => f1 x) 
           (fun x: p C u0 => refl_equal (f1 x)))
           (JMeq_refl f1)
         ))) H). clear H.
  apply cpos_eq;  simpl; auto.
  apply (JMeq_eq H0). 
 Qed.

 Lemma iso_extC_C1 C D X :
       forall ex : comp (Ext C) (Ext D) X, extC (extC1 ex) = ex.
 Proof.
   unfold comp; intros C D X ex; destruct ex; simpl.
   apply ext_eq; trivial.
   rewrite (extensionality 
          (fun pc : p C u0 =>
      uext D (X := X) (u (f0 pc)) (fun pdf : p D (u (f0 pc)) => f (f0 pc) pdf)) f0); trivial.
   intro a; destruct (f0 a); simpl.
   rewrite (extensionality  (fun pdf : p D u1 => f1 pdf) f1
          (fun pdf : p D u1 => refl_equal (f1 pdf))); trivial.
 Qed.


  (*  1 x A -> B  is A -> B*) 
  Definition oneTimes A B  (i : cmr (cont_prod One_cont A) B) := 
     match i with 
     | uCmr v0 g0 =>
         uCmr (C := A) (D :=  B) (fun a : s A => v0 (tt, a))
           (fun (a : s A) (i0 : p B (v0 (tt, a))) =>
              let s0 := g0 (tt, a) i0 in match s0 with
                                  | inr p0 => p0
                                  | inl e => match e with end
                                  end)
     end. 


 End Products_Sums_and_Compositions.


Section Properties_about_Morphisms.

 (** * Applying morphisms  *)
  Definition ap_mor C D (cd: cmr C D) (E: Ucontainer) : cmr (cComp C E) (cComp D E) :=
     let  smap : s (cComp C E) -> s (cComp D E) := 
             (fun a: s (cComp C E ) => uext D (v (cd) (u a)) (comp (f a) (g (cd) (u a)) )) in 
                   uCmr smap (fun  a: s (cComp C E) =>  fun pb : p (cComp D E) (smap a)
                                                => cpos E a (g (cd) (u a) (cs pb)) (cp pb)).
  (* products of morphsims *)  
   Definition mor_prod A B C D (ab : cmr A B) (cd: cmr C D): 
            cmr (cont_prod A C) (cont_prod B D ):=
      let smap: s (cont_prod A C) -> s (cont_prod B D) := 
           (fun a : s (cont_prod A C) => pair  (v ab (fst a))(v cd (snd a)) ) in
            let pmap := (fun aa : s (cont_prod A C) => 
                  fun ps : p (cont_prod B D ) (smap aa) => 
                     match ps with  
                     | inl p0 =>  inl (p C (snd aa)) (g ab (fst aa) p0)
                     | inr p0 =>  inr (p A (fst aa)) (g cd (snd aa) p0)
                     end ) in uCmr smap pmap.


  (* given C D: Ucontainer, maps C x D -> D x C *)
  Definition prod_swap C D  :=
    let smap := (fun cd  : s C * s D => pair (snd cd) (fst cd)) in
      let pmap := (fun cd : s C * s D => fun ps : p (cont_prod D C) (smap cd) =>  
                                                   match ps with
                                                   | inl d => inr (p C (fst cd)) d
                                                   | inr c => inl (p D (snd cd )) c
                                                   end) in
        uCmr (C := cont_prod C D) (D := cont_prod D C) smap pmap.

 (* prod_swap o prod_swap is the identity *)
 Lemma prod_swap_iso C D  :   
    Eqmor (m_comp (prod_swap D C) (prod_swap C D)) (idm (cont_prod C D)).
  intros C D; simpl.
  unfold comp; unfold id.
  apply morq; simpl. 
  intro a; destruct a; simpl; trivial.
  intro a; destruct a; simpl.
  intros p0 p1 H;  set (H1 := JMeq_eq H).
  destruct p0; destruct p1; trivial.
  (*injection H1.intro H2; case H2; trivial.
  discriminate H1. discriminate H1.
  injection H1. intro H2; case H2; trivial.*)
Qed.
 
 (* maps (C x D) x E  -> C x (D x E) *)
 Definition prod_swap1 C D E :
        cmr (cont_prod (cont_prod C D) E) (cont_prod C (cont_prod D E)).
    intros. refine (uCmr 
           (C := cont_prod (cont_prod C D) E )
     (D := cont_prod C (cont_prod D E))
       (fun cd  : s C * s D * s E => pair (fst  (fst cd)) (pair (snd (fst cd)) (snd cd)))
            (fun cd : s C * s D * s E => _ ) ).
    intro H. simpl in *. 
    destruct H.
    exact (inl (p E (snd cd)) (inl (p D (snd (fst cd))) p0)).
    destruct s0.
    exact (inl (p E (snd cd)) (inr (p C (fst (fst cd))) p0)).
    exact (inr (p C (fst (fst cd)) + p D (snd (fst cd))) p0).
Defined.

 (* maps  C x (D x E) -> (C x D) x E  *)
Definition prod_swap2 C D E : cmr (cont_prod C (cont_prod D E)) (cont_prod (cont_prod C D) E).
    intros.
    refine (uCmr (C := cont_prod C (cont_prod D E)) (D := cont_prod (cont_prod C D) E)
           (fun cd  : s C * (s D * s E) => pair (pair (fst cd) (fst (snd cd))) (snd (snd cd)))
            (fun cd : s C * (s D * s E) => _ ) ).
    intro H; destruct H; simpl in *.
    destruct p0.
    exact (inl (p D (fst (snd cd)) + p E (snd (snd cd))) p0).
    exact (inr (p C (fst cd)) (inl (p E (snd (snd cd))) p0)).
    exact (inr (p C (fst cd)) (inr (p D (fst (snd cd))) p0)).
Defined.

(* prod_swap1 o prod_swap2 is the identity*)
Lemma prod_swap12 C D E :
 Eqmor (m_comp (prod_swap2 C D E) (prod_swap1 C D E))  (idm (cont_prod (cont_prod C D) E)).
Proof.
  intros C D E; unfold idm;  simpl.
  unfold prod_swap1; unfold id. unfold cont_prod; unfold comp;  
  apply morq; simpl. intro a; destruct a.
  destruct p0;  simpl; trivial.
  intros a Q0 Q1 H;  destruct a; simpl in *.
  destruct p0; simpl in *.
  set (R := JMeq_eq H).
  destruct Q0; destruct Q1.
  destruct s3; destruct s4;  auto.
  discriminate R. discriminate R.
  injection R. intro h; case h; trivial.
Qed. 
 
(** The extension of the composition of container morphisms is the composition of their extensions*)   
Lemma extMcomp C D E (cd : cmr C D) (de : cmr D E): 
   forall X,  mmap (m_comp de cd) (X := X) =  comp (mmap de (X := X)) (mmap cd (X := X)) . 
Proof.
  unfold comp; unfold mmap.
  intros C D E cd de;
  destruct cd; destruct de; simpl. 
  intro X;  apply extensionality.
  intro a; destruct a; unfold comp ; trivial.
Qed.


End Properties_about_Morphisms.
 
End constructions.

End Unitary_containers.

(** Exporting Notations and tactics *)
 Infix " <x> " := cont_prod (at level 25) : Container_scope.
 Infix " <+> " := cont_sum (at level 24) : Container_scope.
 Infix " <o> " := cComp (at level 24) : Container_scope.
 Infix " ===> " := cmr (at level 20) : Container_scope.
 (*Notation "(S <| P )" := (ucont  P) (at level 40) : Container_scope.*)
 Notation " A ==== B " := (Eqmor A B) (at level 35) : Container_scope.
 Definition ONE  := One_cont.  

 Open Scope Container_scope.

 Delimit Scope Container_scope with container.

  (** Rewriting and simplification tactics *) 

  
  Ltac container_simplify :=
      let destruct_conj H := 
      (destruct H as [l r]; simpl in l; simpl in r) in
   match goal with
   | [ x : Ext _ _  |- _ ] => 
        match goal with
        | [ c : CPos _ x |- _ ] => 
               let Eq := constr:(cpos_unique x c) in
                 (rewrite Eq || rewrite <- Eq) ; trivial
        end
   | |- context [mor_map ?cm ?F ?ex ] => 
          match type of cm with
          | cmr ?C _ => 
              match type of ex with
              | Ext C _ => 
                  let Eq := constr:(cmap_mor_map F cm ex) in
                    first [ rewrite Eq | rewrite <- Eq]; trivial
              end
          end
    | [ H : _ = _ |- _ ] => 
         let D := constr:(ext_eq_dst H) in 
           let D1 := constr:(dst_cpos_eq H) in
               destruct_conj D || destruct_conj D1
   | [ Eq : Eqmor _ _ |- _ ] => 
         let H := constr:( mmap_eqmor _ Eq) in
            rewrite H || rewrite <- H
      
   end.

  Ltac Container_simplify := repeat container_simplify.

  (** initialization tactic  *)

  Ltac change_to_cmor_eq A tac1  :=
    let T := type of A  in
    match T with
    | cmr _ _ =>  
       match goal with
       | [ |- _ = _  ] =>
               apply eqm_eq; intros; tac1
       end
  end.

  Ltac contInit H :=
     let simp := unfold id in *;
    unfold m_comp in *; unfold idm in *;  unfold comp in *; unfold H in * ;
     try red;  simpl in *; auto in
      match goal with
      | [ |- ?X ==== ?Y] =>  apply morq; simpl
      | [ |- forall (x : _ ) , _ ] => let a := fresh "a" in
                 intro a; simp
      | [ |- ?X = ?Y ] => change_to_cmor_eq X contInit (* H *)
      | [ x : ?X |- _ ] => match type of x with
                           | prod _ _ => destruct x as [x1 x2]; simpl in x1; simpl in x2
                           end
      end.
 

  Ltac ContInit tac :=  (contInit Container_simplify); tac.
  
  Tactic Notation "contInitialize" "with" constr(h) :=  (ContInit h).

  Tactic Notation "contInitialize" := progress  (ContInit id).

                    


