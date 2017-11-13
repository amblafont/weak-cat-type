(* -*- coq-prog-name: "coqtop"; -*- *)

(* ici on n'utilise pas autosubst qui de toute manière ne marche pas pour
les types mutuellement inductifs *)
(* Je pack les interprétations dans un record pour la relation fonctionnelle *)
(* coqc -q -Q "WeakOmegaCat" WeakOmegaCat WeakOmegaCat/TypeSystem/libhomot.v *)
Require Import libhomot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* différences par rapport au papier :

Γ ⊢ B dans weakening des Tmes

Γ ⊢ dans la substitution du contexte vide

TODO :  remplacer la r_gle Γ,x:A ⊢ en prémisse par Γ ⊢ A

*)



Require Import EqdepFacts.
Require Import Coq.Logic.JMeq.
Require Import ssreflect ssrfun ssrbool .
(* From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq. *)
Set Bullet Behavior "Strict Subproofs".
(* Require Import Eqdep. *)
Notation "x ..1" := (projT1 x) (at level 2).
Notation "x ..2" := (projT2 x) (at level 2).
Notation "x ,Σ y" := (existT _ x y)  (at level 70).
Notation "x ≅ y" := (JMeq  x  y) (at level 70, y at next level, no associativity).

Ltac etrans := eapply trans_eq.

Lemma transport (A : Type) (x : A) (P : A -> Type) (y : A)(e : x = y)  (Px : P x) : P y.
Proof.
  apply:eq_rect e => //=.
Defined.
Lemma transport2 (A : Type)  (P : A -> Type)(Q : forall (a:A), P a -> Type)
      (x : A) (p : P x)(y : A)(q : P y)(e : x = y)(e' : p ≅ q)  (Px : Q _ p) : Q _ q.
Proof.
  destruct e.
  apply JMeq_eq in e'.
  by destruct e'.
Defined.

(* je le réécris en defined *)
Lemma JMeq_sym : forall (A B:Type) (x:A) (y:B), JMeq x y -> JMeq y x.
Proof. 
intros; destruct H; trivial.
Defined.

Axiom funext : forall (A : Type) (B : A -> Type) (f g : forall a, B a),
    (forall a, f a = g a) -> f = g.

Lemma uip (A : Type) (x y : A) (e e' : x =y) : e = e'.
  apply JMeq_eq.
  destruct e.
  destruct e'.
  reflexivity.
Qed.
Lemma JMeq_eq_refl A (x  : A) : JMeq_eq (JMeq_refl (x:=x)) = erefl.
  apply:uip.
  Qed.
Lemma JMeq_eq_rect (A : Type) (x : A) (P : A -> Type) (Px : P x) (y : A) (w : x= y) :
      eq_rect x P Px y w ≅ Px.
  now destruct w.
Defined.
Lemma JMeq_eq_rect_r (A : Type) (x : A) (P : A -> Type) (Px : P x) (y : A) (w : y= x) :
      @eq_rect_r A x P Px y w ≅ Px.
  now destruct w.
Defined.

Lemma JM_eq_eq_rect_r (A : Type) (x : A) (P : A -> Type) (Px : P x) (y : A) (w : y= x) Py :
    Px ≅ Py ->
      @eq_rect_r A x P Px y w = Py.
  destruct w.
  now move/(@JMeq_eq _ _ _).
Qed.
Lemma JM_eq_eq_rect (A : Type) (x : A) (P : A -> Type) (Px : P x) (y : A) (w : x= y) Py :
    Px ≅ Py ->
      @eq_rect A x P Px y w = Py.
  destruct w.
  now move/(@JMeq_eq _ _ _).
Qed.

Lemma JMeq_transport2  (A : Type)  (P : A -> Type)(Q : forall (a:A), P a -> Type)
      (x : A) (p : P x)(y : A)(q : P y)(e : x = y)(e' : p ≅ q)  (Px : Q _ p) :
  transport2 e e' Px ≅ Px.
Proof.
  destruct e.
  simpl.
  by destruct (JMeq_eq e').
Qed.
Lemma JM_projT2  (A : Type) (P : A -> Type) (a b : {x : A & P x})
      (e : a = b) : a..2 ≅ b..2.
Proof.
  now destruct e.
Qed.

Lemma JMeq_from_eq (A : Type) (x y : A) : x = y -> x ≅ y.
  by destruct 1.
Qed.

Ltac clear_jmsigma :=
  match goal with
  | x : (?C ,Σ ?D) = (?C ,Σ ?E) |- _ =>
    have {x} x : D = E by apply : JMeq_eq;apply:(JM_projT2  x)
  | x : ?C = ?C |- _ => clear x
  end.

  

Lemma JMeq_eq_r  (A : Type) (x y : A) : x = y -> x ≅ y.
now destruct 1.
Qed.

Lemma JMeq_congr3 (A : Type) (B : A -> Type)(D: Type) (C : forall a : A, B a -> D)
      (x x' : A) (b : B x) (b'  : B x') : x = x' -> b ≅ b' -> C x b = C x' b'.
destruct 1.
move => eb.
apply JMeq_eq in eb.
now destruct eb.
Qed.
Lemma JMeq_congr4 (A : Type) (B : A -> Type) (C : forall a : A, B a -> Type)
      (D : Type) (E : forall a b (c : @C a b), D)
      (x x' : A) (b : B x) (b'  : B x')
      (c : C _ b) (c' : C _ b')
  : x = x' -> b ≅ b' -> c ≅ c' -> E  _ _ c =  E _ _ c'.
destruct 1.
move => eb ec.
apply JMeq_eq in eb.
destruct eb.
apply JMeq_eq in ec.
now destruct ec.
Qed.
Lemma JMeq_reflh_eq_rect_r (A : Type) (x : A) (P : A -> Type) (Px : P x) (y : A) (w : y= x) :
      reflh (@eq_rect_r A x P Px y w) ≅ reflh Px.
  now destruct w.
Qed.
(* Examples/Poplmark.v *)
(* Notation "Gamma `_ x" := (dget Gamma x). *)
(* Notation "Gamma ``_ x" := (get Gamma x) (at level 3, x at level 2, *)
(*   left associativity, format "Gamma ``_ x"). *)

Reserved Notation "sigma ∘ tau"  (at level 56, left associativity).

Reserved Notation "s .[ sigma ]T" (at level 2, sigma at level 200, left associativity,
   format "s .[ sigma ]T" ).
Reserved Notation "s .[ sigma ]oT" (at level 2, sigma at level 200, left associativity,
   format "s .[ sigma ]oT" ).

Reserved Notation "s .[ sigma ]wT" (at level 2, sigma at level 200, left associativity,
   format "s .[ sigma ]wT" ).

Reserved Notation "s .[ sigma ]t" (at level 2, sigma at level 200, left associativity,
   format "s .[ sigma ]t" ).

Reserved Notation "s .[ sigma ]V" (at level 2, sigma at level 200, left associativity,
   format "s .[ sigma ]V" ).



Inductive Tm : Type :=
  | va (x:Var)
          (* Coh Γ A σ  *)
  | coh : Con -> Ty -> sub -> Tm
with Ty : Type :=
  | star
  | ar : Ty -> Tm -> Tm -> Ty
with  Con : Type :=
      | astar
          (* Γ A, u tq Γ ⊢ u : A *)
      | ext : Con -> Ty -> Tm -> Con
with sub : Type :=
       | to_star : Tm -> sub
       | to_ext : sub -> Tm -> Tm -> sub
with Var : Type :=
  | vstar
  (* toutes ces variables sont dans des contextes étendues *)
  | vwk (v : Var)
  | v0 
  | v1 .



Fixpoint sub_Var (σ : sub) (x : Var) : Tm :=
   match σ,x with
     to_star t, vstar => t
   | to_ext σ a f, vwk x => x .[ σ ]V
   | to_ext σ a f, v0 => f
   | to_ext σ a f, v1 => a
   | _,_ => va vstar (* dummy *)
   end
where "s .[ sigma ]V" := (sub_Var sigma s) : subst_scope.


Fixpoint sub_Tm (σ : sub) (t : Tm) : Tm :=
  match t with
  | va x => x .[ σ ]V
          (* Coh Γ A σ  *)
  | coh Γ A δ => coh Γ A (δ ∘ σ)
  end
    (*
Γ ⊢ σ : Δ
E ⊢ δ : Γ
E ⊢ σ ∘ δ : Δ
     *)
with compS (σ : sub) (δ : sub) : sub :=
       match σ with
         | to_star t => to_star (t .[ δ ]t)
         (* Γ ⊢ σ' : Δ' *)
         (* E ⊢ σ ∘ δ : Δ *)
         (* E ⊢ (σ ∘ δ)' : Δ' *)
         | to_ext σ a f => to_ext (σ ∘ δ) (a .[ δ ]t) (f .[ δ ]t)
       end
where "s .[ sigma ]t" := (sub_Tm sigma s) : subst_scope
  and "sigma ∘ delta" := (compS sigma delta) :subst_scope.


(* Γ ⊢ idS : Γ *)
Fixpoint idS (Γ : Con) : sub :=
  match Γ with
    astar => to_star (va vstar)
  | ext Γ A u => to_ext (idS Γ) (va v1) (va v0)
  end.


Fixpoint wkt (t : Tm) : Tm :=
  match t with
    va x => va (vwk x)
  | coh Γ A σ => coh Γ A (wkS σ)
  end
with wkS (σ : sub) : sub :=
  match σ with
  | to_star t => to_star (wkt t)
  | to_ext σ a f => to_ext (wkS σ) (wkt a) (wkt f)
  end.

Fixpoint wkT (A : Ty) : Ty :=
  match A with
    star => star
  | ar A t u => ar (wkT A) (wkt t) (wkt u)
  end.


Open Scope subst_scope.


Fixpoint sub_Ty (σ : sub) (A : Ty) : Ty :=
  match A with
    star => star
  | ar A t u => ar (A .[ σ ]T) (t .[ σ ]t) (u .[ σ ]t)
  end
    where "s .[ sigma ]T" := (sub_Ty sigma s) : subst_scope.


Definition sub_oTy (σ : sub) (A : option Ty) : option Ty :=
  if A is Some A then Some (A .[ σ ]T) else None.

Notation "s .[ σ ]oT" := (sub_oTy σ s) : subst_scope.

  

    
(* Compute ((coh astar star (to_star (ids 0))).[ ren(+1) ]t). *)

(* Fixpoint wV (Γ : Con) (B : Ty) (x : Var) := *)
(*   match Γ,x with *)
(*   | astar, vstar => B == star *)
(*   | ext Γ A u,vwk x => wV Γ *)
(*   | ext Γ A u,v0  => ar (A .[ wkS Γ A u ]T) v1 u *)
(*   | ext Γ A u,v1  => ar A v1 u *)
(*                        | *)
(*                   | 1 => A *)
(*                   | x.+2 => lookup Γ 1 *)
(*                   end *)
(*   end. *)


(*
Fixpoint lookup (Γ : Con) (x : Var) : option Ty :=
  match Γ,x with
  | astar, vstar => Some (star)
  | ext Γ A u,vwk x => (lookup Γ x) .[ wkS Γ A u ]oT
  | ext Γ A u,v0  => Some (ar (A .[ wkS Γ A u ]T) (va v1) (u .[ wkS Γ A u]t ))
  | ext Γ A u,v1  => Some (A .[ wkS Γ A u ]T)
  | _, _ => None
  end.
*)



(*
Fixpoint s_nth (σ : sub) (x : var) :=
  match σ with
  | to_star t => match x with
             | 0 => t
             | _.+1 => none
             end
  | to_ext σ a f => match x with
                  | 0 => f
                  | 1 => a
                  | x.+2 => s_nth σ x
                  end
  end.
*)

Fixpoint beq_var ( x y : Var) : bool :=
  match x,y with
    vstar,vstar => true
  | vwk v, vwk v' => beq_var v v'
  | v0,v0 => true
  | v1, v1 => true
  | _,_ => false
  end.
  
Fixpoint beq_tm (x y : Tm) : bool :=
        (match x,y with
       | va x, va x' => beq_var x x'
       | coh Γ A σ, coh Γ' A' σ' => [ && beq_Con Γ Γ' , beq_Ty A A' & beq_sub σ σ' ]
       | _,_ => false
         end)
with beq_Ty (x y : Ty) :=
       (
       match x,y with
       | star, star => true
       | ar A t u, ar A' t' u' =>
         [ && beq_Ty A A' , beq_tm t t' & beq_tm u u' ]
       (* | none,none => true *)
       | _,_ => false

       end)
with beq_Con (x y : Con) :   bool :=
      (match x , y with
  | astar, astar => true
  | ext Γ A u, ext Γ' A' u' => [ && beq_Con Γ Γ' , beq_Ty A A' & beq_tm u u' ]
  | _,_ => false
     end)
with beq_sub (x y : sub) :   bool :=
  (match x , y with
      | to_star t, to_star t' => beq_tm t t'
      | to_ext σ a f, to_ext σ' a' f' => [ && beq_sub σ σ' , beq_tm a a' & beq_tm f f']
        | _,_ => false
        end).

(*
Definition Var_eqP : Equality.axiom beq_var.
Admitted.
Definition tm_eqP : Equality.axiom beq_tm.
Admitted.
Definition Ty_eqP : Equality.axiom beq_Ty.
Admitted.
Definition sub_eqP : Equality.axiom beq_sub.
Admitted.
Definition Con_eqP : Equality.axiom beq_Con.
Admitted.

Canonical var_eqMixin := EqMixin Var_eqP.
Canonical var_eqType := Eval hnf in EqType Var var_eqMixin.

Canonical tm_eqMixin := EqMixin tm_eqP.
Canonical tm_eqType := Eval hnf in EqType Tm tm_eqMixin.

Canonical Ty_eqMixin := EqMixin Ty_eqP.
Canonical Ty_eqType := Eval hnf in EqType Ty Ty_eqMixin.

Canonical sub_eqMixin := EqMixin sub_eqP.
Canonical sub_eqType := Eval hnf in EqType sub sub_eqMixin.

Canonical Con_eqMixin := EqMixin Con_eqP.
Canonical Con_eqType := Eval hnf in EqType Con Con_eqMixin.

*)




(* La version inductive *)
Inductive WVar : Con -> Ty -> Var -> Type :=
  w_vstar : WVar astar star vstar
| w_vwk Γ A u B x : WVar Γ B x ->
                 (* Je dois aussi mettre les hypothèses suivantes *)
                    Wtm Γ A u ->
                    WVar (ext Γ A u) (wkT B) (vwk x)
| w_v1 Γ A u : Wtm Γ A u -> WVar (ext Γ A u) (wkT A) v1
| w_v0 Γ A u : Wtm Γ A u -> WVar (ext Γ A u) (ar (wkT A) (va v1) (wkt u)) v0

with WC : Con -> Type :=
  w_astar : WC astar
| w_ext Γ A u : WC Γ -> WTy Γ A ->  Wtm Γ A u -> WC (ext Γ A u)
with WTy : Con -> Ty -> Type :=
       | w_star Γ : WC Γ -> WTy Γ star
       | w_ar Γ A t u : WTy Γ A -> Wtm Γ A t -> Wtm Γ A u -> WTy Γ (ar A t u)
with Wtm : Con -> Ty -> Tm -> Type :=
       | w_va Γ A x : WVar Γ A x -> Wtm Γ A (va x)
       | w_coh Γ Δ A σ : WC Δ -> WTy Δ A -> WS Γ Δ σ ->  
                         (* en principe inutile, mais je le rajoute pour avoir la bonne hypothèse
                           de récurrence *)
                         (* WTy Γ A.[σ]T  -> *)
                         Wtm Γ A.[σ]T (coh Δ A σ) 
with WS : Con -> Con -> sub -> Type :=
     | w_to_star Γ t : Wtm Γ star t -> WS Γ astar (to_star t)
     | w_to_ext Γ A u Δ σ t f : WS Γ Δ σ ->
                                WTy Δ A ->
                                Wtm Δ A u ->
                                Wtm Γ A.[σ]T t ->
                                Wtm Γ (ar (A.[ σ ]T) t (u.[σ]t)) f ->
                                WS Γ (ext Δ A u) (to_ext σ t f).


Reserved Notation "Gamma ⊢ A : B"
  (at level 68, A at level 99, no associativity,
   format "Gamma  ⊢  A  :  B").
Reserved Notation "Gamma ⊢ A"
  (at level 68, A at level 99, no associativity,
   format "Gamma  ⊢  A").

Reserved Notation "Gamma ⊢ A ⇒ B"
  (at level 68, A at level 99, no associativity,
   format "Gamma  ⊢  A  ⇒  B").

Notation "Gamma ⊢ A" := (WTy Gamma A)  : wf_scope.
Notation "Gamma ⊢ s : A" := (Wtm Gamma A s) : wf_scope.
Notation "Gamma ⊢  s  ⇒ Delta" :=
  (WS Gamma Delta s)
    : wf_scope.

Open Scope wf_scope.

Fixpoint wkTm_inj (a b: Tm) (e : wkt a = wkt b) {struct a}: a = b
with wkS_inj (x y : sub)(e : wkS x = wkS y) {struct x} : x = y.
  - destruct a,b => //=.
    +  by case:e => ->.
    + case:e .
      move => ?? /wkS_inj .
      intros; subst.
      f_equal.
  - destruct x,y => //=.
    + case:e.
      by move/wkTm_inj => ->.
    + case:e.
      by move => /wkS_inj -> /wkTm_inj -> /wkTm_inj -> .
Qed.

Fixpoint wkTy_inj  (a b: Ty) (e : wkT a = wkT b) {struct a}: a = b.
  destruct a,b => //=.
  - case:e .
    move =>/wkTy_inj ->.
    move/wkTm_inj => ->.
    move/ wkTm_inj ->.
    reflexivity.
Qed.
Definition is_center (A : Type) (a : A) :=
  forall ( a' : A),  a' = a.
Fixpoint WC_hp Γ (wΓ : WC Γ) : is_center wΓ
with WTy_hp Γ A (wA : Γ ⊢ A) : is_center wA
with WTm_hp Γ A t (wt : Γ ⊢ t : A) : is_center wt
with WVar_hp Γ A x (wx : WVar Γ A x) : is_center wx
with WS_hp Γ Δ σ (wσ : (Γ ⊢ σ ⇒  Δ)) : is_center wσ.
-  destruct wΓ.
   + move => w.
     apply:JMeq_eq.
     set (C := astar) in w.
     (* need to do that otherwise it odes not genralize proper;ly
before : 
  @JMeq (WC astar) w (WC astar) w_astar
after :
@JMeq (WC C) w (WC astar) w_astar
*)
     change (w ≅ w_astar).
     have  : C = astar by reflexivity.
     case:w => //=.
   + move => wΓe.
     set (C := ext _ _ _) in wΓe.
     apply:JMeq_eq.
     change (  wΓe ≅ w_ext wΓ w w0).
     have  : C = ext Γ A u by reflexivity.
     case : wΓe => //=.
     move => ?????? [? ? ?].
     subst.
     apply:JMeq_from_eq.
     f_equal.
     * apply:WC_hp.
     * apply:WTy_hp.
     * apply:WTm_hp.
- destruct wA.
  + move => wst.
    set (Ct := Γ) in wst.
    set (C := star) in wst.
    apply:JMeq_eq.
    change (  wst ≅ w_star w).
    have  : C = star  by reflexivity.
    have  : Ct = Γ  by reflexivity.
    case : wst => //=.
    intros; subst.
    apply:JMeq_from_eq.
    f_equal.
    apply:WC_hp.
  +  move => wAr.
     set (Ct := Γ) in wAr.
     set (C := ar A t u) in wAr.
    apply:JMeq_eq.
    change (  wAr ≅ w_ar wA w w0).
    have  : C = ar A t u  by reflexivity.
    have  : Ct = Γ  by reflexivity.
    case : wAr => //=.
    intros; subst.
    case:x0; intros; subst.
    apply:JMeq_from_eq.
    f_equal.
    * apply:WTy_hp.
    * apply:WTm_hp.
    * apply:WTm_hp.
- destruct wt.
  + move => wt'.
     set (CC := Γ) in wt'.
     set (CT := A) in wt'.
     set (Ct := va x) in wt'.
     apply:JMeq_eq.
     change   (wt' ≅ w_va w).
     move:(erefl CC) (erefl CT) (erefl Ct).
     rewrite {2}/CC {2}/CT {2}/Ct.
     case:wt' => //=.
     intros ; subst.
     case:H1; intros; subst.
     apply:JMeq_from_eq.
     f_equal.
     by apply:WVar_hp.
  + move => wt'.
     set (CC := Γ) in wt'.
     set (CT := A.[σ]T) in wt'.
     set (Ct := coh Δ A σ) in wt'.
     apply:JMeq_eq.
     change   (wt' ≅ w_coh w w0 w1).
     move:(erefl CC) (erefl CT) (erefl Ct).
     rewrite {2}/CC {2}/CT {2}/Ct.
     case:wt' => //=.
     intros ; subst.
     case:H1 => ???; subst.
     apply:JMeq_from_eq.
     f_equal.
     * apply:WC_hp.
     * apply:WTy_hp.
     * apply:WS_hp.
- destruct wx.
  + move => wx'.
    (* cette technique marche super bien !! *)
    refine (match wx' with w_vstar => _ | _ => _ end).
    all:easy.
  + move => wx'.
    apply:JMeq_eq.
    match goal with [ H : WVar ?C ?B ?X |- ?a ≅ ?b] =>
                      set (CC := C) in H;
                      set (CT := B) in H;
                      set (Ct := X) in H;
                      change (a ≅ b)
    end.
    move:(erefl CC) (erefl CT) (erefl Ct).
    rewrite {2}/CC {2}/CT {2}/Ct.
    case:wx' => //=.
    intros; subst.
    case:H ; intros ;subst.
    case:H1 ; intros ;subst.
    apply wkTy_inj in H0.
    subst.
    apply:JMeq_from_eq.
    f_equal.
    * apply:WVar_hp.
    * apply:WTm_hp.
  + move => wx'.
    apply:JMeq_eq.
    match goal with [ H : WVar ?C ?B ?X |- ?a ≅ ?b] =>
                      set (CC := C) in H;
                      set (CT := B) in H;
                      set (Ct := X) in H;
                      change (a ≅ b)
    end.
    move:(erefl CC) (erefl CT) (erefl Ct).
    rewrite {2}/CC {2}/CT {2}/Ct.
    case:wx' => //=.
    intros; subst.
    case:H ; intros ;subst.
    apply:JMeq_from_eq.
    f_equal.
    * apply:WTm_hp.
  + move => wx'.
    apply:JMeq_eq.
    match goal with [ H : WVar ?C ?B ?X |- ?a ≅ ?b] =>
                      set (CC := C) in H;
                      set (CT := B) in H;
                      set (Ct := X) in H;
                      change (a ≅ b)
    end.
    move:(erefl CC) (erefl CT) (erefl Ct).
    rewrite {2}/CC {2}/CT {2}/Ct.
    case:wx' => //=.
    intros; subst.
    case:H ; intros ;subst.
    apply:JMeq_from_eq.
    f_equal.
    * apply:WTm_hp.
- destruct wσ.
  + move => wσ'.
    apply:JMeq_eq.
    match goal with [ H : ?C ⊢ ?B ⇒ ?C2 |- ?a ≅ ?b] =>
                      set (CC := C) in H;
                      set (CS := B) in H;
                      set (CC2 := C2) in H;
                      change (a ≅ b)
    end.
    move:(erefl CC) (erefl CS) (erefl CC2).
    rewrite {2}/CC {2}/CS {2}/CC2.
    case:wσ' => //=.
    intros; subst.
    case:H0 ; intros ;subst.
    apply:JMeq_from_eq.
    f_equal.
    * apply:WTm_hp.
  + move => wσ'.
    apply:JMeq_eq.
    match goal with [ H : ?C ⊢ ?B ⇒ ?C2 |- ?a ≅ ?b] =>
                      set (CC := C) in H;
                      set (CS := B) in H;
                      set (CC2 := C2) in H;
                      change (a ≅ b)
    end.
    move:(erefl CC) (erefl CS) (erefl CC2).
    rewrite {2}/CC {2}/CS {2}/CC2.
    case:wσ' => //=.
    intros; subst.
    case:H0 ; intros ;subst.
    case:H1 ; intros ;subst.
    apply:JMeq_from_eq.
    f_equal; (apply WTm_hp || apply:WTy_hp || apply:WS_hp).
Qed.
(* sinon je ne peux plus faire de ltac
*)
Ltac clear_hprop :=
  match goal with
  | x : WC ?C, x' : WC ?C |- _ =>
    destruct (WC_hp x x')
  | x : WTy ?C ?A, x' : WTy ?C ?A |- _ =>
    destruct (WTy_hp x x')
  | x : Wtm ?C ?A ?t, x' : Wtm ?C ?A ?t |- _ =>
    destruct (WTm_hp x x')
  | x : WVar ?C ?A ?t, x' : WVar ?C ?A ?t |- _ =>
    destruct (WVar_hp x x')
  | x : WS ?C ?A ?t, x' : WS ?C ?A ?t |- _ =>
    destruct (WS_hp x x')
  end.
(* TODO définir sbVcomp avant et sbTcomp après *)
Fixpoint sbTcomp  (σ δ : sub) C C' Γ 
         (wδ : C ⊢ δ ⇒ C')
               (wσ : C' ⊢ σ ⇒ Γ)
               (A :Ty)
         (wA : Γ ⊢ A)
  :
  A.[σ]T.[δ]T = A.[σ ∘ δ]T
with sbTmcomp  (σ δ : sub) C C' Γ
               (wδ : C ⊢ δ ⇒ C')
               (wσ : C' ⊢ σ ⇒ Γ)
               A (t :Tm)
               (wt : Γ ⊢ t : A)
     :
       t.[σ]t.[δ]t = t.[σ ∘ δ]t
with sbVcomp  (σ δ : sub) C C' Γ 
               (wδ : C ⊢ δ ⇒ C')
               (wσ : C' ⊢ σ ⇒ Γ)
               A (x :Var)
              (wx : WVar Γ A x)
     : x.[σ]V.[δ]t = x.[σ ∘ δ]V
with sbScomp  (σ δ : sub) C C' Γ
               (wδ : C ⊢ δ ⇒ C')
               (wσ : C' ⊢ σ ⇒ Γ)
              Δ (s :sub)
               (ws : Γ ⊢ s ⇒ Δ )
     : (s ∘ σ) ∘ δ = s ∘ (σ ∘ δ).
- destruct wA.
  + reflexivity.
  + cbn.
    move/sbTcomp:wA => /(_ _ _ _ _ wδ wσ) ->.
    move/sbTmcomp:w => /(_ _ _ _ _ wδ wσ ) ->.
    move/sbTmcomp:w0 => /(_ _ _ _ _ wδ wσ ) ->.
    reflexivity.
- destruct wt.
  + apply:sbVcomp; last by apply:w.
    eassumption.
    eassumption.
  + simpl.
    erewrite sbScomp => //; eassumption.
- destruct wx.
  + inversion wσ.
    reflexivity.
  + inversion wσ; subst.
    move/sbVcomp:wx => /(_ _ _ _ _ wδ).
    now apply.
  + inversion wσ.
    reflexivity.
  + inversion wσ.
    reflexivity.
- destruct ws.
  + simpl.
    move/sbTmcomp:w => /(_ _ _ _ _ wδ wσ ) ->.
    reflexivity.
  + simpl.
    f_equal.
    * apply:sbScomp; eassumption.
    * apply:sbTmcomp; eassumption.
    * apply:sbTmcomp; eassumption.
Qed.

Lemma wkt_ext  σ t f u : (wkt u).[to_ext σ t f]t = u.[σ]t
with wkS_ext  σ t f δ : (wkS δ) ∘ (to_ext σ t f) = δ∘σ.
  - destruct u.
    + reflexivity.
    + simpl.
      rewrite wkS_ext.
      reflexivity.
  - destruct δ.
    + simpl.
      rewrite wkt_ext.
      reflexivity.
    + simpl.
      f_equal.
      * apply: wkS_ext.
      * apply: wkt_ext.
      * apply: wkt_ext.
Qed.


Lemma wkT_ext σ t f B : (wkT B).[to_ext σ t f]T = B.[σ]T.
  induction B => //=.
  now rewrite IHB !wkt_ext .
Qed.
  
  
  

  Fixpoint wkV_wkS Γ Δ σ  B (x : Var)
        (wσ : Γ ⊢ σ ⇒ Δ)
        (wx : WVar Δ B x)  : wkt (x .[σ]V) = x.[wkS σ]V.
  destruct wx.
  + inversion wσ; subst.
    reflexivity.
  + inversion wσ; subst.
    simpl.
    apply:wkV_wkS; eassumption.
  + by inversion wσ; subst.
  + by inversion wσ; subst.
  Qed.

  Fixpoint wkt_wkS Γ Δ σ  B (t : Tm)
        (wσ : Γ ⊢ σ ⇒ Δ)
        (wt : Δ ⊢ t : B)  : wkt (t .[σ]t) = t.[wkS σ]t
    with wkS_wkS Γ Δ σ E δ 
        (wσ : Γ ⊢ σ ⇒ Δ)
        (wδ : Δ ⊢ δ ⇒ E)
        : (wkS (δ ∘ σ)) = δ ∘ (wkS σ).
  - destruct wt.
    + apply:wkV_wkS; eassumption.
    + simpl.
      erewrite wkS_wkS ; reflexivity ||  eassumption.
  - destruct wδ.
    + simpl.
      erewrite wkt_wkS ; reflexivity ||  eassumption.
    + simpl.
      erewrite wkS_wkS.
      erewrite wkt_wkS.
      erewrite wkt_wkS.
      reflexivity.
      all:eassumption.
  Qed.
  Fixpoint wkT_wkS Γ Δ σ  B 
        (wσ : Γ ⊢ σ ⇒ Δ)
        (wB : Δ ⊢ B)  : wkT (B .[σ]T) = B.[wkS σ]T.
    destruct wB.
    - reflexivity.
    - simpl.
      erewrite wkT_wkS.
      erewrite wkt_wkS.
      erewrite wkt_wkS.
      reflexivity.
      all:eassumption.
  Qed.
    
Lemma WVar_wk
      (Γ  : Con)(A: Ty) (u : Tm)
      (wu : Γ ⊢ u : A)
      (B : Ty)(x : Var) (wx : WVar Γ B x) :
  WVar (ext Γ A u) (wkT B) (vwk x).

  move:A u wu.
  induction wx.
  + move => A u wu.
    apply:w_vwk.
    repeat constructor.
    assumption.
  + move => A' u' wu'.
    apply:w_vwk => //.
    by apply:IHwx.
  + move => A' u' wu'.
    apply:w_vwk => //.
    by constructor.
  + move => A' u' wu'.
    apply:w_vwk => //.
    by constructor.
Qed.
Lemma WTm_wk
      (Γ  : Con)(A: Ty) (u : Tm)
      (wu : Γ ⊢ u : A)
      (B : Ty)(t : Tm) (wt : Γ ⊢ t : B) :
   (ext Γ A u) ⊢ wkt t : (wkT B)
  with WS_wk
         (Γ  : Con)(A: Ty) (u : Tm)
         (wu : Γ ⊢ u : A)
         Δ σ (wσ : Γ ⊢ σ ⇒ Δ) : ext Γ A u ⊢ wkS σ ⇒ Δ.

  - move:A u wu.
  induction wt.
  + move => A' u' wu'.
    constructor.
    now apply:WVar_wk.
  + move => A' u' wu'.
    simpl.
    erewrite wkT_wkS; try eassumption.
    constructor => //=.
    by apply:WS_wk.
  - destruct wσ.
    + simpl.
      constructor.
      change star with (wkT star).
      by apply:WTm_wk.
    + simpl.
      constructor; try assumption.
      * by apply:WS_wk.
      * erewrite <- wkT_wkS; try eassumption.
          by apply:WTm_wk.
      * erewrite <- wkT_wkS; try eassumption.
        erewrite <- wkt_wkS; try eassumption.
        move/WTm_wk:(wu) => I.
        by move/I:w2.
Qed.

Fixpoint WTy_wk
      (Γ  : Con)(A: Ty) (u : Tm)
      (wu : Γ ⊢ u : A)
      (wA : Γ ⊢ A)
      (B : Ty) (wB : Γ ⊢ B) :
   (ext Γ A u) ⊢  (wkT B).
  destruct wB.
  - constructor.
    constructor => //.
  - simpl.
    constructor.
    + apply:WTy_wk => //.
    + apply:WTm_wk => //.
    + apply:WTm_wk => //.
Qed.
    
(* with WS_wk *)
Lemma WVar_sb
         (Γ Δ : Con)(σ : sub)(A : Ty)(x : Var) 
         (wΓ : WC Γ) (wΔ : WC Δ)
         (wσ : Γ ⊢ σ ⇒ Δ) (wx : WVar Δ A x) :  Γ ⊢ (x.[σ]V) : (A.[σ]T)   .
  move : wx σ    wσ  wΓ wΔ.
  induction 1.
  + now inversion 1.
  + inversion 1.
    subst.
    rewrite wkT_ext.
    simpl.
    intros.
    apply:IHwx => //.
    now inversion wΔ.
  + inversion 1; subst=> //.
    now rewrite wkT_ext.
  + inversion 1; subst=> //.
    simpl.
    now rewrite wkT_ext wkt_ext.
Defined.
Lemma
  Wtm_sb
         (Γ Δ : Con)(σ : sub)(A : Ty)(t : Tm) 
         (wΓ : WC Γ) (wΔ : WC Δ)
         (wσ : Γ ⊢ σ ⇒ Δ) (wt : Δ ⊢ t : A) : Γ ⊢ t.[σ]t : A.[σ]T
with WS_sb
         (Γ Δ : Con)(σ : sub)(E : Con)(δ : sub) 
         (wΓ : WC Γ) (wΔ : WC Δ)
         (wσ : Γ ⊢ σ ⇒ Δ) (wδ : Δ ⊢ δ ⇒ E) : Γ ⊢ δ ∘ σ ⇒ E.
- destruct wt.
  + move/WVar_sb:w.
    apply => //.
  + simpl.
    erewrite sbTcomp; try eassumption.
    {
    constructor ; try eassumption.
    apply:WS_sb; last first; eassumption.
    }
- destruct wδ.
  + simpl.
    constructor.
    apply:(Wtm_sb _ _ σ star); last first; eassumption.
  + simpl.
    constructor.
    * apply:WS_sb; last first; eassumption.
    * assumption.
    * assumption.
    * erewrite <- sbTcomp; try eassumption.
      {
         apply:Wtm_sb; last first; eassumption.
      }
    * erewrite <- sbTcomp; try eassumption.
      erewrite <- sbTmcomp; try eassumption.
      move/Wtm_sb:w2.
      apply ; assumption.
Defined.

Lemma WTy_sb
         (Γ Δ : Con)(σ : sub)(A : Ty)
         (wΓ : WC Γ) (wΔ : WC Δ)
         (wσ : Γ ⊢ σ ⇒ Δ) (wA : Δ ⊢ A): Γ ⊢ A.[σ]T.
 induction wA.
  + constructor => //.
  + cbn.
    constructor.
    * apply:IHwA => //. 
    * apply:Wtm_sb => //;[| eassumption |] => // .
    * apply:Wtm_sb => //;[| eassumption |] => // .
Defined.


(* Définir ce qu'est un type globulaire qui est un omega groupoide *)
(*
Record omega_groupoid :=
  mkGroup
    { s_C : forall {Γ : Con}  (wΓ : wC Γ) ,  Type ;
      s_T : forall {Γ : Con} {A : Ty} (wΓ : wC Γ) (wA : wTy Γ A), s_C wΓ -> Type;
      s_tm : forall {Γ : Con} {A : Ty}{ t : Tm} (wΓ : wC Γ) (wA : wTy Γ A) (wt : wtm Γ A t)
                (γ : s_C wΓ), s_T wA γ }.
*)

(* Require Import Coq.Logic.JMeq. *)

(* Notation "x ≅ y" := (eq_dep x y)  (at level 70). *)

Section OmegaGroupoid.
  Variable (T : Type).
  Hypothesis (fibT : Fib T).

(* en utilisant uip *)
(* Notation "x ≅ y :> P" := (eq_dep _ P _  x _ y) (at level 70, y at next level, no associativity). *)

Record rC :=
  mkRC { C_TY : Type ;
         C_fib : Fib C_TY;
         idA :  T -> C_TY;
         JA : forall (P : C_TY -> Type)
                (fibP : (forall (δ : C_TY), Fib (P δ)))
                (d : forall (a : T) , P(idA a))
                (δ :  C_TY ) , P δ ;
        JA_idA : forall (P : C_TY -> Type)
          ( fibP : forall (δ :  C_TY ) , Fib (P δ) )
          (d : forall (a : T) , P(idA a))
          (a : T) ,
          JA fibP d (idA a) = d a

       }.

Lemma rCeq (x y : rC)
      (e : C_TY x = C_TY y)
      (ef : C_fib x ≅ C_fib y )
      (eidA : forall(a:T), (idA x a ≅ idA y a))
      (eJA : forall P P' fibP fibP' d d' δ δ',
          P ≅ P' -> fibP ≅ fibP' -> d ≅ d' -> δ ≅ δ' ->
          @JA x P fibP d δ ≅ @JA y P' fibP' d' δ') : x = y.
  destruct x,y; simpl in *.
  destruct e.
  have e: idA0 = idA1.
  {
    apply:funext => a.
    apply JMeq_eq.
    apply:eidA.
  }
  subst.
  have e: JA0 = JA1.
  {
    repeat (apply:funext ; intros).
    intros.
    apply JMeq_eq.
    now apply:eJA.
  }
  subst.
  have e: JA_idA0 = JA_idA1.
  {
    repeat (apply:funext ; intros).
    apply:uip.
  }
  now subst.
  Qed.



Record rT (Γ : rC) :=
  mkRTy { T_TY : C_TY Γ  -> Type;
          iA : forall (a : T) , T_TY (idA Γ a) ;
          T_fib : forall (γ : _) , Fib (T_TY γ)
        }.

Lemma rTeq (C C' : rC) (x : rT C) (y : rT C') :
  C = C' ->
  (forall γ γ', γ ≅ γ' -> T_TY x γ ≅ T_TY y γ') ->
    (forall a, iA x a ≅ iA y a)  ->
    (forall γ γ', γ ≅ γ' -> T_fib x γ ≅ T_fib y γ') 
  -> x ≅ y.
  intros.
  subst.
  destruct x,y; simpl in *.
  have e : T_TY0 = T_TY1.
  {
    repeat (apply:funext ; intros).
    apply:JMeq_eq.
    auto.
  }
  subst.
  have e : iA0 = iA1.
  {
    repeat (apply:funext ; intros).
    apply:JMeq_eq.
    auto.
  }
  subst.
  have e : T_fib0 = T_fib1.
  {
    repeat (apply:funext ; intros).
    apply:JMeq_eq.
    auto.
  }
  subst.
  reflexivity.

Qed.

Record rS (Γ Δ : rC ) :=
  mkRS { S : C_TY Γ -> C_TY Δ;
         sb_idA : forall (a : T) , S (idA Γ a) = idA Δ a }.

Lemma rSeq (C C' D D' : rC) (x : rS C D) (y : rS C' D') :
  C = C' -> D = D' ->
  (forall γ γ', γ ≅ γ' -> S x γ ≅ S y γ') ->
   x ≅ y.
  intros.
  subst.
  destruct x,y; simpl in *.
  have e : S0 = S1.
  {
    repeat (apply:funext ; intros).
    apply:JMeq_eq.
    auto.
  }
  subst.
  have e : sb_idA0 = sb_idA1.
  {
    repeat (apply:funext ; intros).
    apply:uip.
  }
  subst.
  reflexivity.
Qed.


Record rtm {Γ : rC} (A : rT Γ) :=
  mkRt { t_t : forall (γ : _) , T_TY A γ;
         eq_iA : forall (a : T) , t_t (idA Γ a) = iA A a }.

Lemma rtmeq (C C' : rC) (A : rT C) (A' : rT C') (x : rtm A) (y : rtm A') :
      ( C = C') -> (A ≅ A') -> (forall γ γ', γ ≅ γ' -> t_t x γ ≅ t_t y γ') -> x ≅ y.
  intros.
  subst.
  destruct x,y; simpl in *.
  apply JMeq_eq in H0.
  subst.
  have e : t_t0 = t_t1.
  {
    repeat (apply:funext ; intros).
    apply:JMeq_eq.
    auto.
  }
  subst.
  have e : eq_iA0 = eq_iA1.
  {
    repeat (apply:funext ; intros).
    apply:uip.
  }
  now subst.
Qed.






Definition r_rl_ext 
         (sΓ : rC) (sA : rT sΓ) (su : rtm sA) : rC.
  unshelve refine (
               {| C_TY := { γ : { a : C_TY sΓ & T_TY sA a } & γ..2 =h t_t su γ..1} ;
            C_fib := _;
            idA := fun a => idA sΓ a ,Σ
                                     (* iA sA a ,Σ _; *)
                                     t_t su (idA sΓ a) ,Σ reflh _;
            JA := _;
            JA_idA := _
         |}).
  cbn.
  (* Fin de idA *)
  (* - rewrite (eq_iA su a). *)
  (*   apply reflh. *)
  -
    intros P fibP d γzu.
    destruct γzu as [[γ z] f].
    set (fibP' :=  ((fun y e => fibP ((γ ,Σ y) ,Σ e)))).
    cbn in fibP'.
    cbn in d.
    refine (Jh (T_fib sA γ) fibP'
                  (JA (r := sΓ)
                      (fun δ => fibP (δ ,Σ t_t su δ ,Σ reflh _)  )
                      (* (fun δ => fibP (δ ,Σ _ δ ,Σ  _)  )  *)
                      d γ
                  )
                  f
                ).
    (* exact d. *)

  - repeat apply sigma_Fib.
    + apply C_fib.
    + apply T_fib.
    + intro a.
      apply eq_Fib.
      apply : T_fib.
  -  intros P fibP d a.
     cbn.
     etrans.
     apply : βJh.
     apply : JA_idA.
Defined.

Definition r_rl_ar 
             (sΓ : rC) (sA : rT sΓ) (st : rtm sA)(su : rtm sA) : rT sΓ.
  unshelve refine (
             {| T_TY := fun γ => t_t st γ =h t_t su γ;
                T_fib := fun γ => eq_Fib (T_fib sA γ ) _ _ ;
                iA := _ |}
         ).
  - intro a.
    rewrite (eq_iA st) (eq_iA su).
    apply reflh.
Defined.

Definition r_rl_astar : rC :=
                    {| C_TY := T;
                     C_fib := fibT ;
                     idA := id;
                     JA := fun P fibP d δ => d δ;
                     JA_idA := fun P fibP d a => erefl
                  |}.

Definition r_rl_star {Γ : rC} : rT Γ :=
                {| T_TY := fun _ => T;
                 T_fib := fun _ => fibT;
                 iA := id |}.

Definition r_rl_vstar   : rtm (Γ := r_rl_astar) r_rl_star :=
  {| t_t := fun (x : (C_TY r_rl_astar)) => (x : T_TY r_rl_star _); eq_iA := fun a => erefl |}.

Definition r_sbT (Γ Δ : rC)(σ : rS Γ Δ) (A : rT Δ)  : rT Γ.
  refine ({| T_TY := fun x => T_TY A (S σ x);
            T_fib := fun x => T_fib A (S σ x); 
            iA := _  |}).
  (* iA *)
  intro a.
  rewrite  (sb_idA σ a).
  exact  ( iA A a).
Defined.

Definition r_sbS (Γ Δ E : rC)(σ : rS Γ Δ)(δ : rS Δ E)   : rS Γ E.
  refine ({| S := fun x => (S δ (S σ x)) |}).
  intro a.
  rewrite sb_idA.
  apply:sb_idA.
Defined.

Lemma J {A : Type} (x : A) (P : forall (y : A) (w : y = x) , Type) : P x erefl ->
                                                                forall (y : A)(w : y = x) , P y w.
   now destruct w.
Defined.
Lemma J_r {A : Type} (x : A) (P : forall (y : A) (w : x = y) , Type) : P x erefl ->
                                                                forall (y : A)(w : x = y) , P y w.
   now destruct w.
Defined.

Definition r_sbt (Γ Δ : rC)(σ : rS Γ Δ) (A : rT Δ) (t : rtm A)  : rtm (r_sbT σ A).
  refine ({| t_t := fun x => (t_t t (S σ x) : T_TY (r_sbT σ A) _);
             eq_iA := _ |}).
  (* iA *)
  intro a.
  cbn.
  pattern (S σ (idA Γ a)) ,(sb_idA σ a).
  apply J.
  exact  (eq_iA t a).
Defined.

(* TODO remplacer ça par une utilisation adéquate de  r_sbT *)
Definition r_wkT (sΓ : rC)(sA : rT sΓ)(su : rtm sA)(sB : rT sΓ) :
   rT (r_rl_ext su) :=
                  {| T_TY := fun (γzu : C_TY (r_rl_ext su)) => T_TY sB (γzu ..1..1);
                 T_fib := fun γzu => T_fib sB (γzu ..1..1);
                 iA := iA sB |}.


(* TODO remplacer ça en utilisan r_sbt *)
Definition r_wkt 
               (sΓ : rC) (sA : rT sΓ) (su : rtm sA)(sB : rT sΓ)(sx : rtm sB)
                :
  rtm (r_wkT su sB) :=
      {| t_t := fun (x : (C_TY (r_rl_ext su))) =>
                   (t_t sx x..1..1 : T_TY (r_wkT su sB) x)
          ; eq_iA := eq_iA sx |}.

Definition r_wkS (sΓ : rC)(sA : rT sΓ)(su : rtm sA) sΔ (sσ : rS sΓ sΔ) :
  rS (r_rl_ext su) sΔ :=
  {| S := fun γ : C_TY (r_rl_ext su) => S sσ (γ ..1) ..1;
     sb_idA := [eta sb_idA sσ] |}.


Definition r_rl_v1  (sΓ : rC) (sA : rT sΓ) (su : rtm sA) : rtm (r_wkT su sA) :=
  ({| t_t := fun (x :C_TY (r_rl_ext su)) => (x..1..2 : T_TY (r_wkT su sA) x)
             ; eq_iA := eq_iA su |}).
 
Definition r_rl_v0  (sΓ : rC) (sA : rT sΓ) (su : rtm sA) :
  rtm (r_rl_ar (r_rl_v1 su) (r_wkt su su)).
  refine ({| t_t := fun (x :C_TY (r_rl_ext su)) =>
               (x..2 : T_TY (r_rl_ar (r_rl_v1 su) (r_wkt su su)) x)
             ; eq_iA := _ |}).
  intro a.
  cbn.
  case (eq_iA su a).
  reflexivity.
Defined.

Definition r_rl_coh (sΓ : rC) (sΔ : rC) (sB : rT sΔ) (sσ : rS sΓ sΔ) : 
  rtm (r_sbT sσ sB).
  refine ( {| t_t := fun γ : C_TY sΓ =>
                       (JA (T_fib sB) (iA sB) (S sσ γ) : T_TY (r_sbT sσ sB) _);
              eq_iA := _ |}).
  intro a.
  cbn.
  pattern (S sσ (idA sΓ a)) ,(sb_idA sσ a).
  apply J.
  apply : JA_idA.
Defined.

                  
Definition r_rl_to_star (sΓ : rC) (st : rtm (Γ := sΓ) r_rl_star) :
  rS sΓ r_rl_astar :=
   ({| S := fun γ => (t_t st γ : C_TY r_rl_astar) ;  sb_idA :=  eq_iA st |}).





(* TODO supprimer ce lemme et remplacer l'énoncé des lemmes dont l'utilisation
nécessite ce lemme
 *)
Lemma eq_rect_inv (A : Type) (x : A) (P : A -> Type)  (y : A) (w : x= y) Py :
  @eq_rect A x P (@eq_rect A y P Py x (esym w)) y w = Py.
Proof.
  by destruct w.
Qed.

Definition r_rl_to_ext 
                    (sΓ : rC) (sΔ : rC)(sA : rT sΔ) (su : rtm sA)
                    (sσ : rS sΓ sΔ) (sa : rtm (r_sbT sσ sA))
                    (sf :  rtm (r_rl_ar sa (r_sbt sσ su))) : rS sΓ ( r_rl_ext su).
  refine ( {| S := fun γ : C_TY sΓ => ((S sσ γ,Σ t_t sa γ),Σ t_t sf γ : C_TY (r_rl_ext su));
              sb_idA := _ |}).
  intro a.
  cbn.
  (* cbn. *)
  (* rewrite (eq_iA sf a). *)
  (* cbn. *)
  (* rewrite (eq_iA su a). *)
  apply eq_sigT_sig_eq.
  unshelve econstructor; [apply eq_sigT_sig_eq; unshelve econstructor|].
  -  apply (sb_idA sσ).
  - 
    (* rewrite (eq_iA sa)(eq_iA su). *)
    pattern (t_t sa (idA sΓ a)),(eq_iA sa a).
    apply:J.
    pattern (t_t su (idA sΔ a)),(eq_iA su a).
    apply:J.
    cbn.
    pattern (S sσ (idA sΓ a)), (sb_idA sσ a).
    apply:J.
    reflexivity.
  - cbn.
    rewrite (eq_iA sf).
    cbn.
    apply JMeq_eq.
    apply:JMeq_trans.
    + match goal with
        |   [ |-   eq_rect ?x ?P ?Px ?y ?w ≅ _]  => apply: (@JMeq_eq_rect _ x P Px y w)
          end.
    + apply:JMeq_trans; first by apply:JMeq_eq_rect_r.
      apply:JMeq_trans; first by  apply:JMeq_eq_rect_r.
      rewrite (eq_iA su).
      pattern ( S sσ (idA sΓ a)),(sb_idA sσ a).
      now apply:J.
Defined.


(* pack record *)
Record pT :=
  mkpT {
      pT_C : rC;
      pT_T : rT pT_C
    }.

Record pTm :=
  mkpt {
      pt_C : rC;
      pt_T : rT pt_C;
      pt_t : rtm pt_T
      }.

Record pS :=
  mkpS {
      pS_C1 : rC;
      pS_C2 : rC;
      pS_S : rS pS_C1 pS_C2
      }.

Arguments mkpT [sΓ] _ : rename.
Arguments mkpt [sΓ] [sA] _ : rename.
Arguments mkpS [sΓ] [sΔ] _ : rename.

(* Spécification de la fonction qu'on veut définir *)
(* TODO : peeut etre donner une définition plus spécifique du weakening plut$pt
que d'utiliser les subtitutions *)
(* Rétrospectivement, c'était pas uen bone idée d'imposer la forme du jugement
de typage, notamment pour les variables, les termes
Par exemple, pour rl_ext, ca aurait pu mieux se passer avec
    rl_C (Γ := ext Γ A u) wΓe
         (r_rl_ext  su)
*)
Inductive rl_C : forall (Γ : Con) (wΓ : WC Γ), rC -> Type :=
  rl_astar : rl_C (Γ := astar) w_astar r_rl_astar
| rl_ext (Γ : Con)  (A : Ty) (u : Tm)
         (wΓ : WC Γ) (wA : Γ ⊢ A) (wu : Γ ⊢ u : A)
         (sΓ : rC) (sA : rT sΓ) (su : rtm sA) :
    rl_C wΓ sΓ -> rl_T wΓ wA (mkpT sA) -> rl_t wΓ wA wu (mkpt su) ->
    rl_C (Γ := ext Γ A u) (w_ext wΓ wA wu )
         (r_rl_ext  su)

         
with rl_T : forall (Γ : Con) (A : _) (wΓ : WC Γ)  (wA : Γ ⊢ A)  , pT  -> Type :=
       rl_star (Γ : Con) (wΓ : WC Γ) (sΓ : rC ) : rl_C wΓ sΓ ->
         rl_T wΓ  (A := star) (w_star wΓ) (mkpT (sΓ := sΓ) r_rl_star)
     | rl_ar (Γ : Con) (A : _) (t u : Tm)
             (wΓ : WC Γ) (wA : Γ ⊢ A) (wt : Γ ⊢ t : A) (wu : Γ ⊢ u : A)
             (sΓ : rC) (sA : rT sΓ) (st : rtm sA)(su : rtm sA) :
         rl_C wΓ sΓ -> rl_T wΓ wA (mkpT sA) -> rl_t wΓ wA wt (mkpt st)
         -> rl_t wΓ wA wu (mkpt su) ->
         rl_T wΓ (A := ar A t u) (w_ar wA wt wu) (mkpT (sΓ := sΓ) (r_rl_ar st su))

with rl_t : forall (Γ : Con)  (A : _) (t : Tm)
              (wΓ : WC Γ)(wA : Γ ⊢ A) (wt : Γ ⊢ t : A)
              , pTm -> Type :=
     | rl_va  (Γ : Con)  (A : _) (x : Var)
              (wΓ : WC Γ)(wA : Γ ⊢ A) (wx : WVar Γ A x)
              (sΓ : rC) (sA : rT sΓ) (sx : rtm sA) :
         (* rl_C wΓ sΓ -> rl_T wΓ wA sA -> *)
         rl_V wΓ wA wx (mkpt sx) -> 
         rl_t wΓ wA (w_va wx) (mkpt sx)
     | rl_coh (Γ : Con)     (Δ : Con) (B : Ty) (σ : sub)
              (wΓ : WC Γ) (wΔ : WC Δ) (wB : Δ ⊢ B)(wBσ : Γ ⊢ B.[σ]T)
              (wσ : Γ ⊢ σ ⇒ Δ)
             (sΓ : rC) (sΔ : rC) (sB : rT sΔ) (sσ : rS sΓ sΔ)  :
             rl_C wΓ sΓ -> rl_C wΔ sΔ -> rl_T wΔ wB (mkpT sB) ->
             rl_S wΓ wΔ wσ (mkpS sσ) ->
             rl_t (A := B .[ σ ]T) (t := coh Δ B σ)  wΓ wBσ (w_coh wΔ wB  wσ (* wBσ *))
                  (mkpt (sA := r_sbT sσ sB) (r_rl_coh sB sσ))


with rl_V :  forall (Γ : Con)  (A : Ty) (x : Var)
               (wΓ : WC Γ)(wA : Γ ⊢ A) (wx : WVar Γ A x), pTm -> Type :=
    | rl_vstar :
         rl_V (Γ := astar) (A := star) (x :=  vstar) w_astar (w_star w_astar) w_vstar
              (mkpt (sΓ := r_rl_astar) (sA := r_rl_star) r_rl_vstar)
    | rl_vwk (Γ : Con)  (A : Ty) (u : Tm) (B : Ty) (x : Var)
             (wΓ : WC Γ) (wA : Γ ⊢ A)  (wu : Γ ⊢ u : A) (wB : Γ ⊢ B) (wx : WVar Γ B x)
             (* redondant *)
               (wBe : ext Γ A u ⊢ wkT B )
               (sΓ : rC) (sA : rT sΓ) (su : rtm sA)(sB : rT sΓ)(sx : rtm sB) :
        rl_C wΓ sΓ -> rl_T wΓ wA (mkpT sA) ->
        rl_t wΓ wA wu (mkpt su) ->  rl_T wΓ wB (mkpT sB) ->
        rl_V wΓ wB wx (mkpt sx) ->
        rl_V (Γ := ext Γ A u) (A := wkT B) (x := vwk x)
             (w_ext wΓ wA wu) wBe (w_vwk  wx wu)
             (mkpt
             (sΓ :=  r_rl_ext su)
             (r_wkt su sx))
    | rl_v1 (Γ : Con)  (A : Ty) (u : Tm)  
            (wΓ : WC Γ) (wA : Γ ⊢ A)
            (wu : Γ ⊢ u : A)
             (* redondant *)
               (wAe : ext Γ A u ⊢ wkT A )
             (sΓ : rC) (sA : rT sΓ) (su : rtm sA) :
             rl_C wΓ sΓ -> rl_T wΓ wA (mkpT sA) -> rl_t wΓ wA wu (mkpt su) -> 
             rl_V (Γ := ext Γ A u) (A := wkT A) (x := v1)
                  (w_ext wΓ wA wu)
                  wAe
                  (* (eq_refl _) *)
                  ((w_v1 wu ))
                  (mkpt (sA := r_wkT su sA) (r_rl_v1 su))
    | rl_v0 (Γ : Con)  (A : Ty) (u : Tm)  
             (wΓ : WC Γ) (wA : Γ ⊢ A)  (wu : Γ ⊢ u : A)
             (* redondant *)
               (wAe : ext Γ A u ⊢ wkT A )
               (wue :  ext Γ A u ⊢ wkt u : wkT A )
             (sΓ : rC) (sA : rT sΓ) (su : rtm sA) :
             rl_C wΓ sΓ -> rl_T wΓ wA (mkpT sA) -> rl_t wΓ wA wu (mkpt su) -> 
             rl_V (Γ := ext Γ A u) (A := ar (wkT A) (va v1) (wkt u))
                  (x := v0) (w_ext wΓ wA wu)
                  (w_ar (Γ := ext Γ A u) wAe (w_va (w_v1 wu)) wue)
                  (* erefl *)
                  (* (w_ar  *)
                  (* (eq_refl _) *)
                  ( (w_v0 wu ))
                  (mkpt (sA := (r_rl_ar (r_rl_v1 su) (r_wkt su su))) (r_rl_v0 su))
with rl_S : forall (Γ Δ : Con)  (σ : sub)
              (wΓ : WC Γ)(wΔ : WC Δ) (wσ : Γ ⊢ σ ⇒ Δ),
               pS -> Type :=
     | rl_to_star (Γ : Con) (t : Tm)
                  (wΓ : WC Γ) (wt : Γ ⊢ t : star)
                  (sΓ : rC) (st : rtm (Γ := sΓ) r_rl_star) :
         rl_C wΓ sΓ -> rl_t (A := star) wΓ (w_star wΓ) wt (mkpt st) ->
         rl_S (Δ := astar) (σ := to_star t)
              wΓ w_astar (w_to_star wt) (mkpS (sΓ := sΓ) (sΔ := r_rl_astar) 
              (r_rl_to_star st))

     | rl_to_ext (Γ Δ : Con)  (A : Ty) (u : Tm) (σ : sub) (a : Tm) (f : Tm)

                 (wΓ : WC Γ)(wΔ : WC Δ)
                 (wA : Δ ⊢ A) (wu : Δ ⊢ u : A)
                 (* redondant *)
                 (wAσ : Γ ⊢ A.[σ]T) (wuσ : Γ ⊢ u.[σ]t : A.[σ]T)
                    (wσ : Γ ⊢ σ ⇒ Δ) (wa : Γ ⊢ a : A .[ σ ]T)
                    (wf : Γ ⊢ f : ar (A .[σ]T) a (u.[σ]t))

                    (sΓ : rC) (sΔ : rC)(sA : rT sΔ) (su : rtm sA)
                    (sσ : rS sΓ sΔ) (sa : rtm (r_sbT sσ sA))
                    (sf :  rtm (r_rl_ar sa (r_sbt sσ su))) :
         rl_C wΓ sΓ -> rl_C wΔ sΔ -> rl_T wΔ wA (mkpT sA) -> rl_t wΔ wA wu (mkpt su) ->
         rl_S wΓ wΔ wσ (mkpS sσ) ->
         rl_t (A := A .[ σ ]T) wΓ wAσ wa (mkpt sa) ->
         rl_t (A := ar (A .[ σ ]T) a (u.[σ]t)) wΓ (w_ar wAσ wa wuσ) wf (mkpt sf) ->

         rl_S (Δ := ext Δ A u) (σ := to_ext σ a f)  wΓ (w_ext wΔ wA wu)
              (w_to_ext  wσ wA wu wa wf)
              (mkpS (sΓ := sΓ) (sΔ := r_rl_ext su)
              (r_rl_to_ext sf)).


Definition all_eq (A : Type) (P : A -> Type) (a : A) :=
  forall a' ,  P a' -> a = a'.

Open Scope wf_scope.
Open Scope subst_scope.



(* TODO peut être intuile avec pt_eq  ?? *)
Lemma π_eq_pT (a b : pT) (e : a = b) : pT_T a ≅ pT_T b.
by now destruct e.
Qed.
Lemma π_eq_pTη a b b' (c :=@mkpT a b) (c' := @mkpT a b')
      (e : c = c') : b = b'.
  by apply/JMeq_eq:(π_eq_pT e).
Qed.

(* celui ci est peut être plus utile que les 2 autres ?? *)
Lemma π_eq_pTη' a a' b b' (c :=@mkpT a b) (c' := @mkpT a' b')
      (e : c = c') : b ≅ b'.
  change (pT_T c ≅ pT_T c').
  now destruct e.
Qed.

Lemma π_eq_pTC (a b : pT) (e : a = b) : pT_C a = pT_C b.
by now destruct e.
Qed.
Lemma π_eq_pt (a b : pTm) (e : a = b) : pt_t a ≅ pt_t b.
by now destruct e.
Qed.

Lemma π_eq_ptη' a a' b b' c c' (d :=@mkpt a b c) (d' := @mkpt a' b' c')
      (e : d = d') : c ≅ c'.
  change (pt_t d ≅ pt_t d').
  now destruct e.
Qed.

Lemma π_eq_ptη a b c c' (d :=@mkpt a b c) (d' := @mkpt a b c')
      (e : d = d') : c = c'.
  by apply/JMeq_eq:(π_eq_pt e).
Qed.
Lemma π_eq_ptTη (Γ : rC) (A B : rT Γ)(a : rtm A) (b : rtm B) (e : mkpt a = mkpt b) : A = B.
  apply:JMeq_eq.
  change (pt_T (mkpt a) ≅ pt_T (mkpt b)).
  now rewrite e.
Qed.

Lemma π_eq_ptC (a b : pTm) (e : a = b) : pt_C a = pt_C b.
by now destruct e.
Qed.
Lemma π_eq_pS (a b : pS ) (e : a = b) : pS_S a ≅ pS_S b.
by now destruct e.
Qed.

Lemma π_eq_pSη a b c c' (d :=@mkpS a b c) (d' := @mkpS a b c')
      (e : d = d') : c = c'.
  by apply/JMeq_eq:(π_eq_pS e).
Qed.
Lemma π_eq_pSC (a b : pS) (e : a = b) : pS_C1 a = pS_C1 b.
by now destruct e.
Qed.
Lemma π_eq_pSC2 (a b : pS) (e : a = b) : pS_C2 a = pS_C2 b.
by now destruct e.
Qed.


Lemma rl_hp_va  (x : Var) (Γ : Con) (wΓ : WC Γ) (A : Ty) (wA : Γ ⊢ A) (wx : WVar Γ A x) (sΓ : rC) 
      (sA : rT sΓ) (sx : rtm sA) :
  all_eq (rl_V wΓ wA wx) {| pt_C := sΓ; pt_T := sA; pt_t := sx |} ->
  all_eq (rl_t wΓ wA (w_va wx)) {| pt_C := sΓ; pt_T := sA; pt_t := sx |}.
Proof.
    move => HIx.
    move => px'.
    inversion 1; repeat clear_hprop; repeat (clear_jmsigma; subst).
    now apply:HIx.
Qed.

Lemma rl_hp_coh (B : Ty) (σ : sub) (sΔ : rC) (sB : rT sΔ) (sΓ : rC) (sσ : rS sΓ sΔ) 
    (Δ : Con) (wΔ : WC Δ) (wB : Δ ⊢ B) (Γ : Con) (wΓ : WC Γ) (wBσ : Γ ⊢ B.[σ]T) 
    (wσ : Γ ⊢ σ ⇒ Δ) :
  all_eq (rl_S wΓ wΔ wσ) {| pS_C1 := sΓ; pS_C2 := sΔ; pS_S := sσ |} ->
  all_eq (rl_T wΔ wB) {| pT_C := sΔ; pT_T := sB |} ->
  all_eq (rl_C wΔ) sΔ ->
  all_eq (rl_C wΓ) sΓ ->
  all_eq (rl_t wΓ wBσ (w_coh wΔ wB wσ)) {| pt_C := sΓ; pt_T := r_sbT sσ sB; pt_t := r_rl_coh sB sσ |}.
Proof.

    move => IHσ IHB IHΔ IHΓ.
    move => px'.
    inversion 1; subst;repeat clear_hprop; repeat (clear_jmsigma; subst).
    have ? : sΓ = sΓ0 by apply:IHΓ.
    have ? : sΔ = sΔ0 by apply:IHΔ.
    subst.
    have ? : sB = sB0 by apply:π_eq_pTη; apply:IHB.
    have ? : sσ = sσ0 by apply:π_eq_pSη; apply: IHσ.
    now subst.
Qed.

Lemma rl_T_C (Γ : Con) (A : Ty) (wΓ : WC Γ) (wA : Γ ⊢ A)
            (pA : pT)
            (* (rlΓ : rl_C wΓ sΓ) *)
            (rlA : rl_T wΓ wA pA)
      : rl_C wΓ (pT_C pA).
Proof.
  now destruct rlA.
Qed.
Lemma rl_T_Cη (Γ : Con) (A : Ty) (wΓ : WC Γ) (wA : Γ ⊢ A)
      sΓ (sA : rT sΓ)
            (pA := mkpT sA)
            (* (rlΓ : rl_C wΓ sΓ) *)
            (rlA : rl_T wΓ wA pA)
      : rl_C wΓ sΓ.
Proof.
  by move/rl_T_C:rlA.
Qed.

Lemma rl_V_C  (Γ : Con)  (A : _) (x : Var)
              (wΓ : WC Γ)(wA : Γ ⊢ A) (wx : WVar Γ A x) 
              (* (sΓ : rC)(sA : rT sΓ) *)
              (px : pTm )
              (rlt : rl_V wΓ wA wx px)
     : rl_C wΓ (pt_C px).
  destruct rlt => //=; constructor => //=.
Qed.

Lemma rl_V_Cη  (Γ : Con)  (A : _) (x : Var)
              (wΓ : WC Γ)(wA : Γ ⊢ A) (wx : WVar Γ A x) 
              (sΓ : rC)(sA : rT sΓ) (sx: rtm sA)
              (px := mkpt sx)
              (rlt : rl_V wΓ wA wx px)
     : rl_C wΓ sΓ.
  by move/rl_V_C:rlt.
Qed.
Lemma rl_t_C  (Γ : Con)  (A : _) (t : Tm)
             (wΓ : WC Γ)(wA : Γ ⊢ A) (wt : Γ ⊢ t : A)
             (pt : pTm )
             (rlt : rl_t wΓ wA wt pt)
     : rl_C wΓ  ((pt_C pt)).
Proof.
  destruct rlt => //=.
  - move/rl_V_C:r.
    apply.
Qed.
(*TODO peut etre plus utile que l'autre ? *)
Lemma rl_t_Cη  (Γ : Con)  (A : _) (t : Tm)
             (wΓ : WC Γ)(wA : Γ ⊢ A) (wt : Γ ⊢ t : A)
             sΓ (sA : rT sΓ) (st : rtm sA)
             (rlt : rl_t wΓ wA wt (mkpt st))
     : rl_C wΓ   sΓ.
Proof.
  by move/rl_t_C:rlt.
Qed.

Lemma rl_S_C1 (Γ Δ : Con)  (σ : sub)
            (wΓ : WC Γ)(wΔ : WC Δ) (wσ : Γ ⊢ σ ⇒ Δ) 
            (pσ : pS)
                (rlσ : rl_S wΓ wΔ wσ pσ) :
          (rl_C wΓ (pS_C1 pσ)) .
  destruct rlσ => //.
Qed.
Lemma rl_S_C1η (Γ Δ : Con)  (σ : sub)
            (wΓ : WC Γ)(wΔ : WC Δ) (wσ : Γ ⊢ σ ⇒ Δ) 
            sΓ sΔ (sσ : rS sΓ sΔ)
            (pσ := mkpS sσ)
                (rlσ : rl_S wΓ wΔ wσ pσ) :
          (rl_C wΓ sΓ) .
  by move/rl_S_C1:rlσ.
Qed.

Lemma rl_S_C2 (Γ Δ : Con)  (σ : sub)
            (wΓ : WC Γ)(wΔ : WC Δ) (wσ : Γ ⊢ σ ⇒ Δ) 
            (pσ : pS)
                (rlσ : rl_S wΓ wΔ wσ pσ) :
          (rl_C wΔ (pS_C2 pσ)) .
  destruct rlσ => //; constructor => //.
Qed.

Lemma rl_S_C2η (Γ Δ : Con)  (σ : sub)
            (wΓ : WC Γ)(wΔ : WC Δ) (wσ : Γ ⊢ σ ⇒ Δ) 
            sΓ sΔ (sσ : rS sΓ sΔ)
            (pσ := mkpS sσ)
                (rlσ : rl_S wΓ wΔ wσ pσ) :
          (rl_C wΔ sΔ) .
  by move/rl_S_C2:rlσ.
Qed.

(* Par récurrence sur le premier r* trouvé *)
Fixpoint rl_hpC (Γ : Con) (wΓ : WC Γ) (sΓ : rC) (rlΓ : rl_C wΓ sΓ) {struct rlΓ}
  : all_eq (rl_C wΓ) sΓ
with rl_hpT (Γ : Con) (A : Ty) (wΓ : WC Γ) (wA : Γ ⊢ A)
            (pA : pT)
            (* (rlΓ : rl_C wΓ sΓ) *)
            (rlA : rl_T wΓ wA pA) {struct rlA}
      : all_eq (rl_T wΓ wA) pA
with rl_hpt  (Γ : Con)  (A : _) (t : Tm)
             (wΓ : WC Γ)(wA : Γ ⊢ A) (wt : Γ ⊢ t : A)
             (* (sΓ : rC)(sA : rT sΓ) *)
             (pt : pTm )
             (* (rlΓ : rl_C wΓ sΓ) (rlA : rl_T wΓ wA sA) *)
             (rlt : rl_t wΓ wA wt pt)
             {struct rlt}
     : all_eq (rl_t wΓ wA wt) pt
with rl_hpV  (Γ : Con)  (A : _) (x : Var)
              (wΓ : WC Γ)(wA : Γ ⊢ A) (wx : WVar Γ A x) 
              (* (sΓ : rC)(sA : rT sΓ) *)
              (px : pTm )
              (rlt : rl_V wΓ wA wx px)

     : all_eq (rl_V wΓ wA wx) px
with rl_hpS (Γ Δ : Con)  (σ : sub)
            (wΓ : WC Γ)(wΔ : WC Δ) (wσ : Γ ⊢ σ ⇒ Δ) 
            (pσ : pS)
                (rlσ : rl_S wΓ wΔ wσ pσ) :
         all_eq  (rl_S wΓ wΔ wσ) pσ.
  - move => sΓ'.
    destruct rlΓ.
  +  
    inversion 1; subst;repeat clear_hprop; repeat (clear_jmsigma; subst).
      reflexivity.
      
  + Guarded.
    move/rl_hpC : rlΓ => IHΓ.
    move/rl_hpT : r => IHA.
    move/rl_hpt : r0 => IHu.
    inversion 1; subst;repeat clear_hprop; repeat (clear_jmsigma; subst).
    have e : sΓ = sΓ0 by apply:IHΓ.
    subst.
    have e: sA = sA0 by  apply:π_eq_pTη; apply:IHA.
    subst.
    have e : su = su0 by apply :π_eq_ptη; apply IHu.
    now subst su0.
- destruct rlA.
    + move/rl_hpC:r => HIΓ.
      move => pA'.
      inversion 1; subst;repeat clear_hprop; repeat (clear_jmsigma; subst).
      have e : sΓ = sΓ0 by apply:HIΓ.
      subst.
      reflexivity.
  + move /rl_hpC:r => IHΓ.
    move /rl_hpT:rlA => IHA.
    move /rl_hpt:r0 => IHt.
    move /rl_hpt:r1 => IHu.
    move => pA'.
    inversion 1; repeat clear_hprop; repeat (clear_jmsigma; subst).
    have e : sΓ = sΓ0 by apply:IHΓ.
    subst.
    have ? :  sA = sA0 by apply:π_eq_pTη; apply:IHA.
    subst.
    have ? :  st = st0 by apply:π_eq_ptη; apply : IHt.
    have ? :  su = su0 by apply:π_eq_ptη; apply : IHu.
    now subst.
- 
  destruct rlt.
  + move/rl_hpV : r.
    apply:  rl_hp_va.
  + 
    move/rl_hpC : r .
    move/rl_hpC : r0.
    move/rl_hpT : r1.
    move/rl_hpS : r2.
    apply:rl_hp_coh.
- destruct rlt.
  + move => px'.
    now inversion 1; repeat clear_hprop; repeat (clear_jmsigma; subst).
  + move/rl_hpC:r => IHΓ.
    move/rl_hpT:r0 => IHA.
    move/rl_hpT:r2 => IHB.
    move/rl_hpt:r1 => IHu.
    move/rl_hpV:rlt => IHx.
    move => px'.
    inversion 1; repeat clear_hprop; repeat (clear_jmsigma; subst).
    have ? : sΓ = sΓ0 by apply:IHΓ.
    subst.
    have ? :  sA = sA0 by apply:π_eq_pTη; apply:IHA.
    subst sA0.
    have ? :  su = su0 by apply:π_eq_ptη; apply : IHu.
    have ? : sB = sB0 by apply:π_eq_pTη; apply:IHB.
    subst.
    have ? :  sx = sx0 by apply:π_eq_ptη; apply : IHx.
    subst.
    now repeat split.

  + move/rl_hpC:r => IHΓ.
    move/rl_hpT:r0 => IHA.
    move/rl_hpt:r1 => IHu.
    move => px'.
    inversion 1; repeat clear_hprop; repeat (clear_jmsigma; subst).
    have ? : sΓ = sΓ0 by apply:IHΓ.
    subst.
    have ? :  sA = sA0 by apply:π_eq_pTη; apply:IHA.
    subst.
    have ? :  su = su0 by apply:π_eq_ptη; apply : IHu.
    subst.
    now repeat split.
  + move/rl_hpC:r => IHΓ.
    move/rl_hpT:r0 => IHA.
    move/rl_hpt:r1 => IHu.
    move => px'.
    inversion 1; repeat clear_hprop; repeat (clear_jmsigma; subst).
    have ? : sΓ = sΓ0 by apply:IHΓ.
    subst.
    have ? :  sA = sA0 by apply:π_eq_pTη; apply:IHA.
    subst.
    have ? :  su = su0 by apply:π_eq_ptη; apply : IHu.
    subst.
    repeat split.
- destruct rlσ.
  + move/rl_hpC:r => IHΓ.
    move/rl_hpt:r0 => IHt.
    move => pσ'.
    inversion 1; repeat clear_hprop; repeat (clear_jmsigma; subst).
    have ? : sΓ = sΓ0 by apply:IHΓ.
    subst.
    have ? :  st = st0 by apply:π_eq_ptη; apply:IHt.
    subst.
    now repeat split.
  + move/rl_hpC:r => IHΓ.
    move/rl_hpC:r0 => IHΔ.
    move/rl_hpT:r1 => IHA.
    move/rl_hpt:r2 => IHu.
    move/rl_hpS:rlσ => IHσ.
    move/rl_hpt:r3 => IHa.
    move/rl_hpt:r4 => IHf.
    move => pσ'.
    inversion 1; repeat clear_hprop; repeat (clear_jmsigma; subst).
    have ? : sΓ = sΓ0 by apply:IHΓ.
    have ? : sΔ = sΔ0 by apply:IHΔ.
    subst.
    have ? :  sA = sA0 by apply:π_eq_pTη; apply:IHA.
    subst.
    have ? :  sσ = sσ0 by apply:π_eq_pSη; apply:IHσ.
    have ? :  su = su0 by apply:π_eq_ptη; apply : IHu.
    subst.
    have ? :  sa = sa0 by apply:π_eq_ptη; apply : IHa.
    subst.
    have ? :  sf = sf0  by apply:π_eq_ptη; apply : IHf.
    subst.
    reflexivity.
Qed.
Lemma
  compr_T Γ Δ E (sσ : rS Γ Δ) (sδ : rS Δ E) sB :
  r_sbT (r_sbS sσ sδ) sB = r_sbT sσ (r_sbT sδ sB).
Proof.
  apply:JMeq_eq.
  apply : rTeq => //=.
  - by move => γ γ' /(@JMeq_eq _ _ _) -> //.
  - move => a .
    apply:JMeq_trans;first by apply JMeq_eq_rect_r.
    apply:JMeq_sym.
    apply:JMeq_trans.
    {
    set w := (w in eq_rect_r _ _ w).
    apply : (JMeq_eq_rect_r  _ w).
    }
    set w := (w in eq_rect_r _ _ w).
    apply:  (JMeq_eq_rect_r _ w).
  -by move => γ γ' /(@JMeq_eq _ _ _) -> //.
Qed.
Lemma compr_Tm sΓ sΔ sE (sσ : rS sΓ sΔ) (sδ : rS sΔ sE)
      sA (su : rtm sA) :
  r_sbt sσ (r_sbt sδ su) ≅ r_sbt (r_sbS sσ sδ) su.
Proof.
  apply:rtmeq => //=.
  - now rewrite compr_T.
  -by move => γ γ' /(@JMeq_eq _ _ _) -> //.
Qed.
Lemma pt_eq (Γ Γ' : rC) (A  : rT Γ)(A'  : rT Γ') (x : rtm A) (x' : rtm A') 
 (* (e : A = A') : x ≅ x' -> mkpt x = mkpt x'. *)
 (e : Γ = Γ') : A ≅ A' -> x ≅ x' -> mkpt x = mkpt x'.
  subst.
  move => h1 h2.
  apply JMeq_eq in h1; subst.
  apply JMeq_eq in h2; subst.
  reflexivity.
Qed.
(* TODO : remplacer l'égalité JMeq par un transport *)
Lemma pt_eq1 (Γ : rC) (A A' : rT Γ) (x : rtm A) (x' : rtm A') 
 (* (e : A = A') : x ≅ x' -> mkpt x = mkpt x'. *)
      (* en fait inutile .. *)
 (e : A = A') : eq_rect _ _ x _ e = x' -> mkpt x = mkpt x'.
  move => ex.
  apply : pt_eq => //=.
  - by apply:JMeq_from_eq.
  - rewrite -ex.
    symmetry.
    apply:JMeq_eq_rect.
Qed.
Lemma pS_eq1 (Γ Δ Δ' : rC)  (x  : rS Γ Δ) (x'  : rS Γ Δ') 
  (e : Δ = Δ')  : eq_rect _ (rS Γ) x _ e = x' -> mkpS x = mkpS x'.
  destruct e => /= -> //=.
Qed.
Lemma pT_eq1 (Γ Γ' : rC) x x'   
 (* (e : A = A') : x ≅ x' -> mkpt x = mkpt x'. *)
 (e : Γ = Γ') : x = eq_rect_r rT x' e -> mkpT x = mkpT x'.
  destruct e => /= -> //=.
Qed.

      
Lemma tp_rTm1 Γ B B' t (wΓ : WC Γ) (wB : Γ ⊢ B)(wB' : Γ ⊢ B')
      (wt : Γ ⊢ t : B)(wt' : Γ ⊢ t : B') pt pt'
  :
  B = B' -> pt = pt' -> rl_t wΓ wB' wt' pt' -> rl_t wΓ wB wt pt .
Proof.
  move => eB et.
  destruct eB, et.
  have eB : wB = wB' by apply:WTy_hp.
  have et : wt = wt' by apply:WTm_hp.
  destruct eB, et.
  exact.
Qed.
Lemma tp_rV1 Γ B B' x (wΓ : WC Γ) (wB : Γ ⊢ B)(wB' : Γ ⊢ B')
      (wx : WVar Γ B x)(wx' : WVar Γ B' x) px px'
  :
  B = B' -> px = px' -> rl_V wΓ wB' wx' px' -> rl_V wΓ wB wx px .
Proof.
  move => eB et.
  destruct eB, et.
  have eB : wB = wB' by apply:WTy_hp.
  have et : wx = wx' by apply:WVar_hp.
  destruct eB, et.
  exact.
Qed.

Lemma tp_rT1 Γ A A'  (wΓ : WC Γ) (wA : Γ ⊢ A)(wA' : Γ ⊢ A')
       pA pA'
  :
  A = A' -> pA = pA' -> rl_T wΓ wA'  pA' -> rl_T wΓ wA pA .
Proof.
  move => eB et.
  destruct eB, et.
  have eB : wA = wA' by apply:WTy_hp.
  by rewrite eB.
Qed.
(* Lemma tp_rS2 Γ Δ σ (wΓ : WC Γ)(wΔ wΔ' : WC Δ) (wσ' wσ : Γ ⊢ σ ⇒ Δ) *)
(*       pσ pσ' *)
(*   : *)
(*    pσ = pσ' -> Drl_S wΓ wΔ wσ' pσ' -> rl_S wΓ wΔ' wσ pσ . *)
(* Proof. *)
(*   move => ->. *)
(*   by have -> // : wσ = wσ' by apply:WS_hp. *)
(* Qed. *)
Lemma tp_rS1 Γ Δ σ (wΓ : WC Γ)(wΔ : WC Δ) (wσ' wσ : Γ ⊢ σ ⇒ Δ)
      pσ pσ'
  :
   pσ = pσ' -> rl_S wΓ wΔ wσ' pσ' -> rl_S wΓ wΔ wσ pσ .
Proof.
  move => ->.
  by have -> // : wσ = wσ' by apply:WS_hp.
Qed.

Lemma r_sb_wkT (sΓ sΔ : rC) (sA sB : rT sΔ) (su : rtm sA) (sσ : rS sΓ sΔ)
      (sa : rtm (r_sbT sσ sA)) (sf : rtm (r_rl_ar sa (r_sbt sσ su)) ):
  r_sbT (r_rl_to_ext sf) (r_wkT su sB) = r_sbT sσ sB.
Proof.
  apply:JMeq_eq.
  apply:rTeq => //.
  * move => γ γ' /(@JMeq_eq _ _ _) -> //.
  * move => b.
    simpl.
    apply:JMeq_trans.
    {
      set e := (e in eq_rect_r _ _ e).
               apply:(JMeq_eq_rect_r _ e).
    }
    symmetry.
    apply:(JMeq_eq_rect_r _ ).
  * by move => γ γ' /(@JMeq_eq _ _ _) -> //.
Qed.

Lemma r_sb_wkTm (sΓ sΔ : rC) (sA sB : rT sΔ) (su : rtm sA) (sσ : rS sΓ sΔ)
      (sa : rtm (r_sbT sσ sA)) (sf : rtm (r_rl_ar sa (r_sbt sσ su)) ) (sx : rtm sB):
  r_sbt (r_rl_to_ext sf) (r_wkt su sx) ≅ r_sbt sσ sx.
Proof.
  apply:rtmeq => //.
  + now rewrite r_sb_wkT.
  + by move => γ γ' /(@JMeq_eq _ _ _) -> //.
Qed.

Lemma  r_sb_star sΓ sΔ (sσ : rS sΔ sΓ) : r_sbT sσ r_rl_star = r_rl_star.
Proof.
  apply JMeq_eq.
  apply :rTeq => //.
  intro a.
  clear.
  cbn.
  apply:JMeq_eq_rect_r.
Qed.

Lemma r_sb_to_star sΓ sΔ (st :rtm r_rl_star) (sσ : rS sΔ sΓ)
  : r_sbS sσ (r_rl_to_star (sΓ := sΓ) st) ≅ r_rl_to_star
          (eq_rect _ _ (r_sbt sσ st) _ (r_sb_star sσ)).
Proof.
  apply:rSeq => //=.
  move => γ γ' /(@JMeq_eq _ _ _) -> //.
  set e := r_sb_star  _.
  move:st.
  change (( fun A w =>
            forall
 (st : rtm A),
              t_t st (S sσ γ') ≅ t_t (eq_rect _ rtm (r_sbt sσ st) _ w) γ')
            (r_rl_star) e).
  now destruct e.
Qed.

Lemma r_sb_ar sΓ sΔ  (sσ : rS sΔ sΓ)
      sA (st su : rtm sA)
  :
  r_sbT sσ (r_rl_ar st su) = r_rl_ar (r_sbt sσ st) (r_sbt sσ su).
Proof.
  apply:JMeq_eq.
  apply:rTeq => //=.
  - by move => γ γ' /(@JMeq_eq _ _ _) -> //.
  - move => a.
    cbn.
    clear.
    apply:JMeq_trans; first by apply:JMeq_eq_rect_r.
    apply:JMeq_trans; first by apply:JMeq_eq_rect_r.
    apply:JMeq_trans; first by apply:JMeq_eq_rect_r.
    symmetry.
    apply:JMeq_trans; first by apply:JMeq_eq_rect_r.
    apply:JMeq_trans; first by apply:JMeq_eq_rect_r.
    apply:JMeq_reflh_eq_rect_r.
  - move => γ γ' /(@JMeq_eq _ _ _) => -> //=.
Qed.



Lemma JMeq_Σ (A : Type) (P : A -> Type) (x x': A) (y : P x) (y' : P x') :
  x = x' -> y ≅ y' -> x ,Σ y = (x' ,Σ y').
destruct 1.
move/(@JMeq_eq _ _ _).
now destruct 1.
Qed.

Lemma JMeq_t_t Γ (A A' : rT Γ) (t : rtm A) (t' : rtm A') γ  :
  A = A' -> t ≅ t' ->  t_t t γ ≅ t_t t' γ.
destruct 1.
move/(@JMeq_eq _ _ _).
now destruct 1.
Qed.
(* Lemma JMeq_congr_r_rl_ar :  *)
(*   r_rl_ar a b *)
  (* par récurrence sur le type ou la substitution ??
   *)
Fixpoint rl_sbT (Γ Δ : Con) (A : Ty) (σ : sub)
         (wΓ : WC Γ) (wΔ : WC Δ)
         (wA : Δ ⊢ A) (wσ : Γ ⊢ σ ⇒ Δ)
         (* redondant *)
         (* (wAσ := Γ ⊢ A.[σ]T) *)
         (* (wAσ := WTy_sb wΓ wΔ wσ wA) *)
         (sΓ : rC)
         (pA : pT)
         (sσ : rS sΓ (pT_C pA))
         (* (sΔ : rC)(sA : rT sΔ) *)
         (* (rlΔ : rl_C wΔ sΔ) *)
         (rlA : rl_T wΔ wA pA)
         (rlσ : rl_S wΓ wΔ wσ (mkpS sσ)) {struct rlA} :
  rl_T wΓ (WTy_sb wΓ wΔ wσ wA) (mkpT (r_sbT sσ (pT_T pA))) 

with rl_sbt (Γ Δ : Con) (A : Ty) (t : Tm) (σ : sub)
         (wΓ : WC Γ) (wΔ : WC Δ)
         (wA : Δ ⊢ A)(wt : Δ ⊢ t : A) (wσ : Γ ⊢ σ ⇒ Δ)
         (* redondant *)
         (* (wAσ := Γ ⊢ A.[σ]T) *)
         (* (wAσ := WTy_sb wΓ wΔ wσ wA) *)
         (sΓ : rC)
         (pt : pTm)
           (sσ : rS sΓ (pt_C pt))
         (* (rlΔ : rl_C wΔ sΔ) *)
         (* (rlA : rl_T wΔ wA (mkpT ())) *)
         (rlt : rl_t wΔ wA wt pt)
         (rlσ : rl_S wΓ wΔ wσ (mkpS sσ)) {struct rlt}
     : rl_t wΓ (WTy_sb wΓ wΔ wσ wA)
                                         (Wtm_sb wΓ wΔ wσ wt)
                                         (mkpt (r_sbt sσ (pt_t pt)))
with rl_sbV (Γ Δ : Con) (A : Ty) (x : Var) (σ : sub)
         (wΓ : WC Γ) (wΔ : WC Δ)
         (wA : Δ ⊢ A)(wx : WVar Δ A x) (wσ : Γ ⊢ σ ⇒ Δ)
         (* redondant *)
         (* (wAσ := Γ ⊢ A.[σ]T) *)
         (* (wAσ := WTy_sb wΓ wΔ wσ wA) *)
         (sΓ : rC)
         (px : pTm)
           (sσ : rS sΓ (pt_C px))
         (* (rlΔ : rl_C wΔ sΔ) *)
         (* (rlA : rl_T wΔ wA (mkpT ())) *)
         (rlx : rl_V wΔ wA wx px)
         (rlσ : rl_S wΓ wΔ wσ (mkpS sσ)) {struct rlx} :
       rl_t wΓ (WTy_sb wΓ wΔ wσ wA)
                                         (Wtm_sb wΓ wΔ wσ (w_va wx))
                                         (mkpt (r_sbt sσ (pt_t px)))
with rl_sbS (Γ Δ E : Con)   (σ δ : sub)
         (wΓ : WC Γ) (wΔ : WC Δ)
         (wE : WC E)(wδ : Δ ⊢ δ ⇒ E) (wσ : Γ ⊢ σ ⇒ Δ)
         (* redondant *)
         (* (wAσ := Γ ⊢ A.[σ]T) *)
         (* (wAσ := WTy_sb wΓ wΔ wσ wA) *)
         (sΓ : rC)
         (pδ : pS)
           (sσ : rS sΓ (pS_C1 pδ))
         (* (rlΔ : rl_C wΔ sΔ) *)
         (* (rlA : rl_T wΔ wA (mkpT ())) *)
         (rlδ : rl_S wΔ wE wδ pδ)
         (rlσ : rl_S wΓ wΔ wσ (mkpS sσ)) {struct rlδ} :
       rl_S wΓ wE (WS_sb wΓ wΔ wσ wδ)
            (mkpS (r_sbS sσ (pS_S pδ))).

- destruct rlA.
  + cbn.
    move/rl_star:(rl_S_C1 rlσ) => /=.
    have -> // : r_sbT sσ r_rl_star = r_rl_star by apply:r_sb_star.
    
  +  simpl.

     move/rl_sbT:(rlA) => IHA; move/IHA:(rlσ) => {IHA} IHA.
     move/rl_sbt:(r0) => IHt; move/IHt:(rlσ) => {IHt} IHt.
     move/rl_sbt:(r1) => IHu; move/IHu:(rlσ) => {IHu} IHu.
     
     apply:tp_rT1; last first.
     * eapply rl_ar.
       -- apply:(rl_S_C1 rlσ).
       -- apply:IHA.
       -- apply:IHt.
       -- apply:IHu.
     * f_equal.
       apply:r_sb_ar.
     * reflexivity.
     
-  destruct rlt.
   + move/rl_sbV:r.
     apply.
     apply:rlσ.
   + 
     move/rl_sbS:(r2) => IHS; move/IHS:(rlσ) => {IHS} IHS.
     move/rl_sbT:(r1) => IHB.
     move/IHB:(IHS) =>  IHB'.
     move/IHB:(r2) =>  IHB''.

     simpl.
     set e := sbTcomp _ _ _.
     eapply(tp_rTm1 _ (wB' := WTy_sb wΓ wΔ (WS_sb wΓ wΓ0 wσ wσ0) wB)) ; last first.
     * {
         apply:rl_coh; last first.
         - exact:IHS.
         - apply:r1.
         - assumption.
         - apply:(rl_S_C1 rlσ).
       }
     *
       (* move => [:eqT]. *)
       apply:pt_eq1.
       --
         (* abstract :eqT. *)
          symmetry.
          apply:compr_T.
       -- simpl.
          move => eqT.
          (* TODO abstraire comme compr_T *)
          apply:JM_eq_eq_rect.
         apply : rtmeq.
         ++ reflexivity.
         ++ by rewrite eqT.
         ++ by move => γ γ' /(@JMeq_eq _ _ _) -> //.
     * apply:e.
- destruct rlx.
  + 
    inversion rlσ; repeat clear_hprop; repeat (clear_jmsigma; subst).
    repeat (clear_jmsigma; subst).
    simpl.
    apply:tp_rTm1; last first.
    * apply:X0.
    *
      (* move => [: eqT]. *)
      apply:pt_eq1.
      --
        (* abstract:eqT. *)
         (* TODO extraire ce lemme : substitution de star *)
          symmetry.
          {
            apply:JMeq_eq.
            apply:rTeq.
            - reflexivity.
            - by move => γ γ' /(@JMeq_eq _ _ _) -> //.
            - move => a //=.
              apply:JMeq_sym.
              apply:JMeq_eq_rect_r.
            - by move => γ γ' /(@JMeq_eq _ _ _) -> //.
          }
      -- (* TODO abstraire *)
         (* substitution d'un vstar *)
        {
          move => eqT.
          apply:JM_eq_eq_rect.
         apply : rtmeq.
         - reflexivity.
         - now rewrite eqT.
         - by move => γ γ' /(@JMeq_eq _ _ _) -> //.
        }
    * reflexivity.
  + (* vwk *)
    move:(WTy_sb _ _ _ _) => wBσ.
    move:(Wtm_sb _ _ _ _) => wtσ.
    simpl in rlσ.
    move:rlσ.
    (* il faut abstraire sur le pS *)
    remember {| pS_C1 := sΓ; pS_C2 := r_rl_ext su; pS_S := sσ |} as pσ eqn:epσ.
    inversion 1 ; repeat clear_hprop; repeat (clear_jmsigma; subst).
    simpl.
    move/rl_sbV : rlx => IHx.
    simpl in IHx.
      (* sΓ0 = sΔ *)
    have e : sΓ0 = sΔ by apply:rl_hpC; eassumption.
    subst.
    have e : sΓ1 = sΓ by move/(π_eq_pSC):H4.
    subst.
    have e : sA0 = sA by apply:π_eq_pTη; apply:rl_hpT; eassumption.
    subst.
    have e : su0 = su by apply:π_eq_ptη; apply:rl_hpt; eassumption.
    subst.
    have e : sσ = r_rl_to_ext sf  by apply:π_eq_pSη.
    subst.
    simpl.
    (*
    (* TODO extraire ce lemme : substitution d'un weakening au niveau des types *)

*)
    (* have eqT :   r_sbT (r_rl_to_ext sf) (r_wkT su sB) = r_sbT sσ0 sB by apply:r_sb_wkT. *)


    apply:tp_rTm1; last first.
    * apply:IHx.
      apply:X3.
    *
      {
        (* TODO abstraire : substitution d'un weakening *)
        apply:pt_eq1.
        - apply:r_sb_wkT.
        - move => h.
          apply:JM_eq_eq_rect.
          apply:r_sb_wkTm.
      }
    * apply:wkT_ext.

  + move:(WTy_sb _ _ _ _) => wBσ.
    move:(Wtm_sb _ _ _ _) => wtσ.
    move:rlσ.
    simpl.
    (* il faut abstraire sur le pS *)
    remember {| pS_C1 := sΓ; pS_C2 := r_rl_ext su; pS_S := sσ |} as pσ eqn:epσ.
    inversion 1 ; repeat clear_hprop; repeat (clear_jmsigma; subst).
    have e : sΓ0 = sΔ by apply:rl_hpC; eassumption.
    subst.
    have e : sΓ1 = sΓ by move/(π_eq_pSC):H4.
    subst.
    have e : sA0 = sA by apply:π_eq_pTη; apply:rl_hpT; eassumption.
    subst.
    have e : su0 = su by apply:π_eq_ptη; apply:rl_hpt; eassumption.
    subst.
    have e : sσ = r_rl_to_ext sf  by apply:π_eq_pSη.
    subst.
    apply:tp_rTm1; last first.
    * apply:X4.
    * {
        apply:pt_eq1.
        - apply:r_sb_wkT.
        - simpl.
          move => eqT.
          apply:JM_eq_eq_rect.
          apply:rtmeq => //.
          * now rewrite eqT.
          * by move => γ γ' /(@JMeq_eq _ _ _) -> //.
      }
    * apply:wkT_ext.
  + move:(WTy_sb _ _ _ _) => wBσ.
    move:(Wtm_sb _ _ _ _) => wtσ.
    move:rlσ.
    simpl.
    (* il faut abstraire sur le pS *)
    remember {| pS_C1 := sΓ; pS_C2 := r_rl_ext su; pS_S := sσ |} as pσ eqn:epσ.
    inversion 1 ; repeat clear_hprop; repeat (clear_jmsigma; subst).
    have e : sΓ0 = sΔ by apply:rl_hpC; eassumption.
    subst.
    have e : sΓ1 = sΓ by move/(π_eq_pSC):H4.
    subst.
    have e : sA0 = sA by apply:π_eq_pTη; apply:rl_hpT; eassumption.
    subst.
    have e : su0 = su by apply:π_eq_ptη; apply:rl_hpt; eassumption.
    subst.
    have e : sσ = r_rl_to_ext sf  by apply:π_eq_pSη.
    subst.
    apply:tp_rTm1; last first.
    * apply:X5.
    * {
        (* TODO extraire ce lemme *)
        have eT :   r_sbT (r_rl_to_ext sf) (r_rl_ar (r_rl_v1 su) (r_wkt su su))
                    = r_rl_ar sa (r_sbt sσ0 su).
        {
          apply:JMeq_eq.
          apply:rTeq => //.
          * move => γ γ' /(@JMeq_eq _ _ _) -> //.
          * move => b.
            simpl.
            apply:JMeq_trans.
            {
              set e := (e in eq_rect_r _ _ e).
                       apply:(JMeq_eq_rect_r _ e).
            }
            apply:JMeq_trans; first by apply:(JMeq_eq_rect_r _ ).
            apply:JMeq_trans; first by apply:(JMeq_eq_rect_r _ ).
            symmetry.
            apply:JMeq_trans; first by apply:(JMeq_eq_rect_r _ ).
            apply:JMeq_trans; first by apply:(JMeq_eq_rect_r _ ).
            now apply:JMeq_trans; first by apply:(JMeq_reflh_eq_rect_r).
          * by move => γ γ' /(@JMeq_eq _ _ _) -> //.
          }

        apply:pt_eq1.
        (* TODO extraire ce lemme *)
        (* - apply:JM_eq_eq_rect. *)
        (*   exact: eT. *)
        -  apply:JM_eq_eq_rect.
          apply:rtmeq => //.
          * now rewrite eT.
          * by move => γ γ' /(@JMeq_eq _ _ _) -> //.
      }
    * simpl.
      by rewrite wkT_ext wkt_ext.
- destruct rlδ.
  + simpl.
    simpl in rlσ.
    move/rl_sbt:r0 => IHt; move/IHt : rlσ => {IHt} IHt.
    simpl in IHt.
    apply:tp_rS1; last first.
    * apply :(rl_to_star ).
      -- apply:rl_t_C.
         apply:IHt.
      -- 
          apply:tp_rTm1; last by apply:IHt.
         ++ reflexivity.
         ++ unshelve eapply pt_eq1.
            ** symmetry; apply:r_sb_star.
            ** apply:eq_rect_inv.
    * cbn.
      f_equal.
      clear.
      apply:JMeq_eq.
      apply:rSeq => //=.
      move => γ γ' /(@JMeq_eq _ _ _) -> //.
      cbn.
      (* TODO factoriser avec r_sb_to_star *)
      cbn in sσ.
      set e := r_sb_star  _.
      move:st.
      change (( fun A w =>
                  forall
                    (st : rtm A),
                    t_t st (S sσ γ') ≅ t_t (eq_rect _ rtm (r_sbt sσ st) _ w) γ')
                (r_rl_star) (esym (esym e))).
      now destruct e.
  + move/rl_sbS:(rlδ) => IHS; move/IHS:(rlσ) => {IHS} IHS.
    move/rl_sbt:(r3) => IHa; move/IHa:(rlσ) => {IHa} IHa.
    move/rl_sbt:(r4) => IHf; move/IHf:(rlσ) => {IHf} IHf.
    have eqT :
      r_rl_ar (eq_rect_r rtm (r_sbt sσ sa) (compr_T sσ sσ0 sA)) (r_sbt (r_sbS sσ sσ0) su) =
      r_sbT sσ (r_rl_ar sa (r_sbt sσ0 su)).
    {
      symmetry.
      etrans.
      apply:r_sb_ar.
      { apply: (@JMeq_congr4 _ _ _ _ (@r_rl_ar _  )).
        - symmetry.
          apply:compr_T.
        - symmetry.
          apply:JMeq_eq_rect_r.
        - apply:compr_Tm.
      }
    }
    apply:tp_rS1; last first.
    * econstructor.
      -- apply:rl_S_C1.
         apply:IHS.
      -- apply:rl_S_C2.
         apply:IHS.
      -- simpl.
         eassumption.
      -- simpl.
         eassumption.
      -- exact:IHS.
      -- simpl.
         simpl in IHa.
         apply:tp_rTm1 ; last by apply:IHa.
         ++ symmetry. apply:sbTcomp; eassumption.
         ++ unshelve eapply pt_eq1.
            ** apply:compr_T.
            ** apply:eq_rect_inv.
      -- simpl in IHf.
         apply:tp_rTm1; last by apply:IHf.
         ++ symmetry.
            (* TODO factoriser : j'ai déjà fait cette preuve *)
            f_equal.
            ** apply:sbTcomp; eassumption.
            ** apply:sbTmcomp; eassumption.
         ++ apply:pt_eq1.
            (* **  apply:eqT. *)
            ** apply eq_rect_inv.
    * simpl.
      f_equal.
      clear.
      apply:JMeq_eq.
      apply:rSeq => //=.
      move => γ γ' /(@JMeq_eq _ _ _) -> //=.
      move:eqT.
      set (e :=  (compr_T _ _ _)) => eqT.
      simpl in *.
      apply:JMeq_from_eq.
      apply:JMeq_Σ.

      {
        f_equal.
        symmetry.
        apply:JMeq_eq.
        apply:JMeq_trans.
        {
          set z := eq_rect _ _ _ _ _.
          apply:(JMeq_t_t (t:=z) γ'); last first.
        - apply:JMeq_eq_rect.
        - apply:compr_T.
        }
        constructor.
      }
      {
        apply:JMeq_trans; last first.
        {
          set z := (eq_rect (r_sbT sσ (r_rl_ar sa (r_sbt sσ0 su))) rtm (r_sbt sσ sf)
                            (r_rl_ar
                               (eq_rect (r_sbT sσ (r_sbT sσ0 sA)) rtm (r_sbt sσ sa) (r_sbT (r_sbS sσ sσ0) sA) (esym e))
                               (r_sbt (r_sbS sσ sσ0) su)) (esym eqT)).
          symmetry.
          apply:(JMeq_t_t (t := z) γ'); last first.
          - apply:JMeq_eq_rect.
          - exact:eqT.
        }
        by constructor.
      }
      (* d'ou viennent tous ces trucs ?? *)
      Unshelve.
       apply:(Wtm_sb (A := star)) => //=.
       exact:wΓ0.
       assumption.
       assumption.
       {
         erewrite <- sbTcomp.
         by apply:Wtm_sb;[ | exact :wΓ0 | | ] ; eassumption.
         all:eassumption.
       }
       {
         erewrite <- sbTcomp.
         erewrite <- sbTmcomp.
         by apply:(Wtm_sb (A := ar A.[σ0]T a u.[σ0]t));[ | exact :wΓ0 | | ] ; eassumption.
           all:eassumption.
       }      
       {
         erewrite <- sbTcomp.
         by apply:WTy_sb;[ | exact :wΓ0 | | ] ; eassumption.
           all:eassumption.
       }
       {
         apply:Wtm_sb; cycle 2.
         (* on aruait ptet pu faire comme ça pour les preuves précédentes ? *)
         apply:WS_sb ;[ |  |eassumption | ] ; eassumption.
         all:eassumption.
       }
Qed.

Lemma r_wk_star sΓ (sA : rT sΓ) (su : rtm sA) :  r_wkT su r_rl_star = r_rl_star.
Proof.
  reflexivity.
Qed.
(* Lemma r_wk_ar sΓ (sA sB : rT sΓ) (su : rtm sA) (sx sy : rtm sB) : *)
(*   r_wkT su (r_rl_ar sx sy) = r_rl_ar (r_wkt su sy) (r_wkt su sy). *)
(* Proof. *)
(*     reflexivity. *)
(*   {| pT_C := r_rl_ext su; pT_T := r_wkT su (r_rl_ar st su0) |} = *)
(*   {| pT_C := r_rl_ext su; pT_T := r_rl_ar (r_wkt su st) (r_wkt su su0) |} *)

(* Record rl_wkC_ind sΓ (sA : rT sΓ) (su : rtm sA) : Type := *)
(*   { r_wk_star :   r_wkT su sA = r_rl_star }. *)


(*
Fixpoint rl_wkC  (Γ  : Con) (A : Ty) (u : Tm)
         (wΓ : WC Γ) (wA : Γ ⊢ A)(wu : Γ ⊢ u : A)
         sΓ (sA : rT sΓ) (su : rtm sA)
         (rA : rl_T wΓ wA (mkpT sA))
         (ru : rl_t wΓ wA wu (mkpt su)) 
         (rΓ : rl_C wΓ sΓ) {struct rΓ} : rl_wkC_ind su

with
*)
Fixpoint rl_wkT
         (Γ  : Con) (A : Ty) (u : Tm)
         (B : Ty)
         (wΓ : WC Γ) (wA : Γ ⊢ A)(wu : Γ ⊢ u : A)
         (wB : Γ ⊢ B) 
         (wBe : ext Γ A u ⊢ wkT B)
         
         sΓ (sA : rT sΓ) (su : rtm sA)
         (sB : rT sΓ)

         (rA : rl_T wΓ wA (mkpT sA))
         (ru : rl_t wΓ wA wu (mkpt su))
         (rB : rl_T wΓ wB (mkpT sB))

          {struct rB} :
  rl_T (w_ext wΓ wA wu) wBe  (mkpT (r_wkT su sB)) 

with rl_wkt
       (Γ  : Con) (A : Ty) (u : Tm)
         (B : Ty) (t  : Tm)

         (wΓ : WC Γ) (wA : Γ ⊢ A)(wu : Γ ⊢ u : A)
         (wB : Γ ⊢ B) (wt : Γ ⊢ t : B)
         (wBe : ext Γ A u ⊢ wkT B) (wte : ext Γ A u ⊢ wkt t : wkT B)

         sΓ (sA : rT sΓ) (su : rtm sA)
         (sB : rT sΓ)(st : rtm sB)

         (rA : rl_T wΓ wA (mkpT sA))
         (ru : rl_t wΓ wA wu (mkpt su))
         (rB : rl_T wΓ wB (mkpT sB))
         (rt : rl_t wΓ wB wt (mkpt st))
         
          {struct rt}
     : rl_t (w_ext wΓ wA wu) wBe wte (mkpt (r_wkt su st))
with rl_wkV 
       (Γ  : Con) (A : Ty) (u : Tm)
         (B : Ty) (x  : Var)

         (wΓ : WC Γ) (wA : Γ ⊢ A)(wu : Γ ⊢ u : A)
         (wB : Γ ⊢ B) (wx : WVar Γ B x)
         (wBe : ext Γ A u ⊢ wkT B) (wxe : WVar (ext Γ A u) (wkT B) (vwk x) )

         sΓ (sA : rT sΓ) (su : rtm sA)
         (sB : rT sΓ)(sx : rtm sB)

         (rA : rl_T wΓ wA (mkpT sA))
         (ru : rl_t wΓ wA wu (mkpt su))
         (rB : rl_T wΓ wB (mkpT sB))
         (rx : rl_V wΓ wB wx (mkpt sx))
          {struct rx}
     : rl_V (w_ext wΓ wA wu) wBe wxe (mkpt (r_wkt su sx))
with rl_wkS
       (Γ  : Con) (A : Ty) (u : Tm)
         (Δ : Con) (σ  : sub)

         (wΓ : WC Γ) (wA : Γ ⊢ A)(wu : Γ ⊢ u : A)
         (wΔ : WC Δ) (wσ : Γ ⊢ σ ⇒ Δ)
         (wσe : ext Γ A u ⊢ wkS σ ⇒ Δ)

         sΓ (sA : rT sΓ) (su : rtm sA)
         sΔ (sσ : rS sΓ sΔ)

         (rA : rl_T wΓ wA (mkpT sA))
         (ru : rl_t wΓ wA wu (mkpt su))
         (rσ : rl_S wΓ wΔ wσ (mkpS sσ))
     : rl_S  (w_ext wΓ wA wu) wΔ wσe (mkpS (r_wkS su sσ)).


  (* - admit. *)
  (*   destruct rΓ. *)
  (* + constructor. *)
  (*   apply:JMeq_eq. *)
  (*   apply :rTeq => //. *)
  (*   * move => γ γ' /(@JMeq_eq _ _ _) -> //. *)
  (*     cbn. *)
- have rΓ := rl_t_C ru.
  have rCe : rl_C (w_ext wΓ wA wu) (r_rl_ext su) by constructor; assumption.
  (* TODO faire ça dans la preuve de rl_sb* *)
  
  move:rB.
  remember {| pT_C := sΓ; pT_T := sB |} as pB eqn:eB.
  destruct 1.
  + move/π_eq_pTC:(eB) => /= e.
  
    subst sΓ0.
    move/π_eq_pTη:(eB) => /= e.
    subst sB.
    simpl in wBe.
    apply:tp_rT1; last by apply:rl_star; eassumption.
    all:reflexivity.

  + 
    move/rl_wkT:(rA) => I ; move/I:(ru)=> {I rl_wkT} rl_wkT.
    (* move/rl_wkt:(rA) => I ; move/I:(ru)=> {I rl_wkt} rl_wkt. *)
    move/rl_wkt:(ru)=> { rl_wkt} rl_wkt.
    move/π_eq_pTC:(eB) => /= e.
    subst sΓ0.
    move/π_eq_pTη:(eB) => /= e.
    subst sB.
    simpl in wBe.
    inversion wBe; subst.
    rename H3 into wA0e.
    rename H4 into wte.
    rename H5 into wue.
    have e : wBe = w_ar wA0e wte wue by apply:WTy_hp.
    subst.
    move/rl_wkT:(rB) ;  move/(_ wA0e) =>  IHB.     
    move/rl_wkt:(r0) ;move /(_ wA0e wte )=>  IHt.
    move/rl_wkt:(r1);move/(_ wA0e wue )=>  IHu. 
    (* move/rl_wkt:(r0);move /(_ wA0e wte rB)=>  IHt. *)
    (* move/rl_wkt:(r1);move/(_ wA0e wue rB)=>  IHu.  *)
    apply:tp_rT1; last first.
    -- apply:rl_ar.
       ++ eassumption.
       ++ eassumption.
       ++ exact:IHt.
       ++ exact:IHu.
    -- cbn.
       
       (* ??? pourquoi ça fait réflexivity marche alors que le lemme abstrait
r_wk_ar ne marche pas en reflexivity ????? *)
       reflexivity.
    -- reflexivity.
- have rΓ := rl_t_C ru.
  (* have rCe : rl_C (w_ext wΓ wA wu) (r_rl_ext su). *)
    (* by constructor; assumption. *)
  (* TODO faire ça dans la preuve de rl_sb* *)
  
  move:rt.
  remember {| pt_C := sΓ; pt_T := sB; pt_t := st |} as pB eqn:et.
  destruct 1.
  +
    (* move/rl_wkT:(ru)=> {rl_wkT} rl_wkT. *)
    (* move/rl_wkt:(ru)=> {rl_wkt} rl_wkt. *)
    (* move/rl_wkV:(ru)=> {rl_wkV} rl_wkV. *)
    move/rl_wkT:(rA) => I ; move/I:(ru)=> {I rl_wkT} rl_wkT.
    move/rl_wkt:(rA) => I ; move/I:(ru)=> {I rl_wkt} rl_wkt.
    move/rl_wkV:(rA) => I ; move/I:(ru)=> {I rl_wkV} rl_wkV.
    have e : sΓ0 = sΓ by move/π_eq_ptC:(et).
    subst.
    have e:   sA0 = sB by move/π_eq_ptTη:(et) .
    subst.
    have e:   sx = st by move/π_eq_ptη:(et) .
    subst.
    move/rl_wkV:(wx) => IHx.
    apply:tp_rTm1; last first.
    * apply:rl_va.
      apply:IHx; last by apply:r.
      assumption.
    * reflexivity.
    * reflexivity.
  + move/rl_wkT:(ru)=> {rl_wkT} rl_wkT.
    move/rl_wkS:(ru)=> {rl_wkS} rl_wkS.
    (* move/rl_wkV:(ru)=> {rl_wkV} rl_wkV. *)
    have e : sΓ0 = sΓ by move/π_eq_ptC:(et).
    subst.
    have e:   sB = r_sbT sσ sB0 by move/π_eq_ptTη:(et) .
    subst.
    rename sB0 into sB.
    have e:   st = r_rl_coh sB sσ by move/π_eq_ptη:(et) .
    subst.
    apply:tp_rTm1; last first.
    * apply:rl_coh; last first; last by constructor; eassumption.
      -- apply:rl_wkS; eassumption.
      -- eassumption.
      -- assumption.
    * reflexivity.
    * apply:wkT_wkS; eassumption.
      (* TODO : wkT B.[σ]T = B.[wkS σ]T *)
- have rΓ := rl_t_C ru.
  move:rx.
  remember {| pt_C := sΓ; pt_T := sB; pt_t := sx |} as px eqn:ex.
  destruct 1.
  +  move/π_eq_ptC:(ex)=> /= ?; subst sΓ.
     move/π_eq_ptTη:(ex)=> /= ?; subst sB.
     move/π_eq_ptη:(ex)=> /= ?; subst sx.
     apply:tp_rV1; last first.
     * apply:rl_vwk; last first.
       -- constructor.
       -- assumption.
       -- eassumption.
       -- assumption.
       -- assumption.
     * reflexivity.
     * reflexivity.
  + move/π_eq_ptC:(ex)=> /= ?; subst sΓ.
    move/π_eq_ptTη:(ex)=> /= ?; subst sB.
    move/π_eq_ptη:(ex)=> /= ?; subst sx.
     apply:tp_rV1; last first.
     {
      apply:rl_vwk; last first.
      {
       apply:rl_wkV; last by apply:rx.
          all:eassumption.
      }
      all:eassumption.
     }
     all:reflexivity.
  + move/π_eq_ptC:(ex)=> /= ?; subst sΓ.
    move/π_eq_ptTη:(ex)=> /= ?; subst sB.
    move/π_eq_ptη:(ex)=> /= ?; subst sx.
     apply:tp_rV1; last first.
     {
      apply:rl_vwk; last first.
       constructor.
       all:eassumption.
     }
     all:reflexivity.
  + move/π_eq_ptC:(ex)=> /= ?; subst sΓ.
    move/π_eq_ptTη:(ex)=> /= ?; subst sB.
    move/π_eq_ptη:(ex)=> /= ?; subst sx.
     apply:tp_rV1; last first.
     {
      apply:rl_vwk; last first.
       constructor.
       all:eassumption.
     }
     all:reflexivity.
- have rΓ := rl_t_C ru.
  move:rσ.
  remember {| pS_C1 := sΓ; pS_C2 := sΔ; pS_S := sσ |} as pσ eqn:eσ.
  destruct 1.
  + move/π_eq_pSC:(eσ) => /= ?; subst sΓ0.
    move/π_eq_pSC2:(eσ) => /= ?; subst sΔ.
    move/π_eq_pS:(eσ) => /= ?; subst sσ.
    apply:tp_rS1; last first.
    * apply:rl_to_star.
      -- constructor; eassumption.
      -- apply: tp_rTm1; last first.
         ++ apply:rl_wkt; last first.
            ** apply:r0.
            ** constructor => //.
            ** eassumption.
            ** assumption.
         ++ reflexivity.
         ++ reflexivity.
    * reflexivity.
  + move/π_eq_pSC:(eσ) => /= ?; subst sΓ0.
    move/π_eq_pSC2:(eσ) => /= ?; subst sΔ.      
    move/π_eq_pS:(eσ) => /= ?; subst sσ.          
    rename A0 into B.
    have rTbiz :   rl_T wΓ wAσ {| pT_C := sΓ; pT_T := r_sbT sσ0 sA0 |}.
    {
      apply:tp_rT1; last by apply:(rl_sbT (pA := mkpT sA0)); eassumption.
      reflexivity.
      reflexivity.
    }


    apply:tp_rS1; last first.                   
    * apply:rl_to_ext.
      -- constructor; eassumption.
      -- eassumption.
      -- eassumption.
      -- eassumption.
      -- apply:rl_wkS; last first.
         ++ apply:rσ.
         ++ assumption.
         ++ assumption.
      -- apply:tp_rTm1; last first.
         ++ apply:rl_wkt; last first.
            ** exact:r3.
            ** assumption.
            ** eassumption.
            ** assumption.
         ++ reflexivity.
         ++ symmetry; apply:wkT_wkS ; eassumption.
      --  apply:tp_rTm1; last first.
         ++ apply:rl_wkt; last first.
            ** exact:r4.
            ** constructor => //.
               apply:tp_rTm1; last by apply:(rl_sbt (pt := mkpt su0)); eassumption.
               all:reflexivity.
            ** eassumption.
            ** assumption.
         ++ reflexivity.
         ++ cbn.
            erewrite wkT_wkS.
            erewrite wkt_wkS.
            reflexivity.
            all:eassumption.
    * reflexivity.
      
(* aucune idée d'ou viennent ces preuves *)
Unshelve.

all:try assumption.
all: try repeat constructor => //.
all: try (erewrite <- wkt_wkS; try eassumption).
all: try (erewrite <- wkT_wkS; try eassumption).
all: try by apply:WTm_wk.
all: try by apply:WTy_wk.
all: try by apply:WS_wk.
by apply:(WTm_wk _ (B := star)).
by apply:(WTm_wk _ (B := ar B.[σ]T a u0.[σ]t)).
Qed.





Record rfC (Γ : Con) (wΓ : WC Γ) :=
  { fC_C : rC ;
    fC_r : rl_C wΓ fC_C
  }.

Record rfT (Γ : Con) (A : Ty) (wΓ : WC Γ) (wA : (Γ ⊢ A)) :=
  { fT_C : rC;
    fT_T : rT fT_C;
    fT_r : rl_T wΓ wA (mkpT fT_T)
  }.

Record rft (Γ : Con) (A : Ty) (t : Tm) (wΓ : WC Γ) (wA : (Γ ⊢ A)) (wt : Γ ⊢ t : A) :=
  { ft_C : rC;
    ft_T : rT ft_C;
    ft_t : rtm ft_T;
    ft_r :  rl_t wΓ wA wt (mkpt ft_t );
    ft_rT :  rl_T wΓ wA (mkpT ft_T) 
  }.
Record rfV (Γ : Con) (A : Ty) (x : Var) (wΓ : WC Γ) (wA : (Γ ⊢ A)) (wx : WVar Γ A x) :=
  { fV_C : rC;
    fV_T : rT fV_C;
    fV_t : rtm fV_T;
    fV_r :  rl_V wΓ wA wx (mkpt fV_t );
    fV_rT :  rl_T wΓ wA (mkpT fV_T) ;
    fV_rC :  rl_C wΓ fV_C 
  }.

Record rfS (Γ Δ : Con) (σ : sub) (wΓ : WC Γ) (wΔ : WC Δ) (wσ : Γ ⊢ σ ⇒ Δ) :=
  { fS_Γ : rC;
    fS_Δ : rC;
    fS_S : rS fS_Γ fS_Δ;
    fS_r : rl_S wΓ wΔ wσ (mkpS fS_S)}.

Fixpoint WVar_Ty Γ A x (wΓ : WC Γ) (wx : WVar Γ A x):  Γ ⊢ A
with WTm_Ty Γ A t (wΓ:WC Γ)  (wt : Γ ⊢ t : A) : Γ ⊢ A.
-  destruct wx.
  + repeat constructor.
  + apply:WTy_wk => //.
    * apply:WTm_Ty.
      -- now inversion wΓ.
      -- eassumption.
    * apply:WVar_Ty.
      -- now inversion wΓ.
      -- eassumption.
  + have wA : Γ ⊢ A.
    {
     apply:WTm_Ty.
      -- now inversion wΓ.
      -- eassumption.
    }

    apply:WTy_wk => //.
  + have wA : Γ ⊢ A.
    {
     apply:WTm_Ty.
      -- now inversion wΓ.
      -- eassumption.
    }

    constructor.
    * apply:WTy_wk => //.
    * repeat constructor => //.
    * apply:WTm_wk => //.
- destruct wt.
  + apply:WVar_Ty; eassumption.
  + apply:WTy_sb; last first; eassumption.
Qed.

  Lemma eqf_CC_TC (Γ : Con) (A : Ty) (wΓ : WC Γ) (wA : Γ ⊢ A)
        (fΓ : rfC wΓ) (fA : rfT wΓ wA) : fC_C fΓ = fT_C fA.
  Proof.
    apply:rl_hpC.
    + apply:fC_r.
    + apply:rl_T_Cη.
      apply:fT_r.
  Qed.
  Lemma eqf_tC_TC (Γ : Con) (A : Ty) t (wΓ : WC Γ) (wA : Γ ⊢ A) (wt : Γ ⊢ t : A)
         (fA : rfT wΓ wA)(ft : rft wΓ wA wt) : ft_C ft = fT_C fA .
  Proof.
    apply:rl_hpC.
    + apply:rl_t_Cη. 
      apply:ft_r.
    + apply:rl_T_Cη.
      apply:fT_r.
  Qed.
  
  Lemma eqf_tC_tC (Γ : Con) (A : Ty) t u (wΓ : WC Γ) (wA : Γ ⊢ A) (wt : Γ ⊢ t : A)
        (wu : Γ ⊢ u : A)
         (ft : rft wΓ wA wt)(fu : rft wΓ wA wu) : ft_C ft = ft_C fu .
  Proof.
    apply:rl_hpC.
    + apply:(rl_t_Cη).
      apply:ft_r.
    + apply:(rl_t_Cη).
      apply:ft_r.
  Qed.
  Lemma eqf_tT_tT (Γ : Con) (A : Ty) t u (wΓ : WC Γ) (wA : Γ ⊢ A) (wt : Γ ⊢ t : A)
        (wu : Γ ⊢ u : A)
         (ft : rft wΓ wA wt)(fu : rft wΓ wA wu) : ft_T ft ≅ ft_T fu .
  Proof.
    apply:π_eq_pTη'.
    apply:rl_hpT.
    + apply:ft_rT.
    + apply:ft_rT.
  Qed.
  Lemma eqf_tT_TT (Γ : Con) (A : Ty) t (wΓ : WC Γ) (wA : Γ ⊢ A) (wt : Γ ⊢ t : A)
         (fA : rfT wΓ wA)(ft : rft wΓ wA wt) : ft_T ft ≅ fT_T fA .
  Proof.
    apply:π_eq_pTη'.
    apply:rl_hpT.
    + apply:ft_rT.
    + apply:fT_r.
  Qed.

Fixpoint semC (Γ : Con) (wΓ : WC Γ) {struct wΓ} : rfC wΓ
with semT (Γ : Con) (A : Ty) (wΓ : WC Γ) (wA : Γ ⊢ A) : rfT wΓ wA
with semt  (Γ : Con)  (A : _) (t : Tm)
             (wΓ : WC Γ)(wA : Γ ⊢ A) (wt : Γ ⊢ t : A) : rft wΓ wA wt
with semV  (Γ : Con)  (A : _) (x : Var)
           (wΓ : WC Γ)
           (wA : Γ ⊢ A)
           (wx : WVar Γ A x) : rfV wΓ wA wx
with semS (Γ Δ : Con)  (σ : sub)
            (wΓ : WC Γ)(wΔ : WC Δ) (wσ : Γ ⊢ σ ⇒ Δ) : rfS wΓ wΔ wσ .
- destruct wΓ.
  + unshelve econstructor.
    * apply :r_rl_astar.
    * constructor.
  + specialize (semt _ _ _ wΓ w w0).
    unshelve econstructor.
    * apply:r_rl_ext.
      apply:(ft_t semt).
    * constructor => //.
      -- apply:(rl_t_C (ft_r semt)).
      -- apply:ft_rT.
      -- apply:ft_r.
- destruct wA.
  + specialize (semC _ w).
    clear_hprop.
    unshelve econstructor.
    * exact (fC_C semC).
    * apply:r_rl_star.
    * by move/rl_star:(fC_r semC).
  + specialize (semT _ _ wΓ wA).
    have st := (semt _ _ _ wΓ wA w).
    have su := (semt _ _ _ wΓ wA w0).
    unshelve econstructor.
    * apply:ft_C.
      exact:st.
    * apply:r_rl_ar.
      -- apply:ft_t.
      -- move: (ft_t su).
         apply:transport2.
         ** apply:eqf_tC_tC.
         ** apply:eqf_tT_tT.
    * constructor.
      -- apply:(rl_t_C (ft_r st)).
      -- apply:ft_rT.
      -- apply:ft_r.
      -- cbn .
         move:(ft_r su).
         apply:transport.
         ++ apply:pt_eq.
            ** apply:eqf_tC_tC.
            ** apply:eqf_tT_tT.
            ** apply:JMeq_sym.
               apply:JMeq_transport2.
- destruct wt.
  + specialize (semV _ _ _ wΓ wA w).
    econstructor.
    * constructor.
      exact:(fV_r semV).
    * apply:fV_rT.
  + specialize (semS _ _ _ wΓ w w1).
    move/semT:(w0).
    move/(_ w) => IHA.
    assert ( e : fT_C IHA = fS_Δ semS).
    {
      apply:rl_hpC.
      - apply:(rl_T_C (fT_r IHA)).
      - apply:(rl_S_C2 (fS_r semS)).
    }
    econstructor.
    * constructor; revgoals.
      -- apply:(fS_r semS).
      -- 
         assert (h' : rl_T w w0 (mkpT (eq_rect _ rT (fT_T IHA) _ e))).
         { move: (fT_r IHA).
           apply:transport.
           move:(fT_T IHA).
           pattern (fT_C IHA),e.
           by apply:J.
         }
         exact:h'.
      -- apply:(rl_S_C2 (fS_r semS)).
      -- apply:(rl_S_C1 (fS_r semS)).
    * move:(fT_r IHA).
      move/rl_sbT => IHA'.
      simpl in IHA'.
      have ewA : wA = WTy_sb  wΓ w w1 w0 by apply:WTy_hp.
      subst wA.
      (* J'ai besoin du truc suivant :
Si le but est :
  f x y z
alors on le remplace par f ?x' ?y' ?z'
avec une preuve que x = x'
puis en ayant détruit cette égalité, que y = y'
*)
      apply:tp_rT1; last first.
      -- apply:IHA'.
         apply:tp_rS1; last by exact:(fS_r semS).
         apply: pS_eq1.
         apply:eq_rect_inv.
      -- f_equal.
         abstract (destruct IHA,semS; simpl in *; now destruct e).
      -- reflexivity.
- destruct wx.
  +
    have e : wΓ = w_astar by   apply:WC_hp.
    subst.
    have e : wA = w_star w_astar by   apply:WTy_hp.
    subst.
    repeat econstructor.
  + (* weakening *)
    rename w into wu.
    move/semt:(wu) => IHu.
    move/semV:(wx) => IHx.
    rename wA into wB.
    assert ( wA : Γ ⊢ A).
    { abstract (by inversion wΓ).  }
    assert ( wΓ' :WC Γ).
    { abstract (by inversion wΓ).  }
    have e : wΓ = w_ext wΓ' wA wu by apply:WC_hp.
    subst.
    specialize (IHx wΓ' (WVar_Ty wΓ' wx)).
    specialize (IHu wΓ' wA).
    have rx := fV_r IHx.
    have rA := fV_rT IHx.
    have ru := ft_r IHu.
    have eΓ : fV_C IHx = ft_C IHu.
    {
      apply:rl_hpC.
      -  exact:(rl_V_C rx).
      -  exact:(rl_t_C ru).
    }
    have rAu : rl_T wΓ' wA {| pT_C := fV_C IHx; pT_T := eq_rect_r rT (ft_T IHu) eΓ |}.
    {
      move:(ft_rT IHu).
      apply:transport.
      move:(ft_T IHu).
      pattern (ft_C IHu),eΓ.
        by apply:J_r.
    }
    have ru' :
      rl_t wΓ' wA wu
           {|
             pt_C := fV_C IHx;
             pt_T := eq_rect_r rT (ft_T IHu) eΓ;
             pt_t := transport2 (Logic.eq_sym eΓ)
                                (JMeq_sym (JMeq_eq_rect_r (ft_T IHu) eΓ)) (ft_t IHu) |}.
    {
      move:(ft_r IHu).
      apply:transport.
      move:(ft_t IHu).
      move:(ft_T IHu).
      pattern (ft_C IHu),eΓ.
      apply:J_r.
      cbn.
      intros.
      rewrite JMeq_eq_refl.
      reflexivity.
    }


    (* destruct IHx,IHu; subst; simpl in *. *)
    (* subst. *)
    econstructor.
    * apply:rl_vwk; last by apply:rx.
      -- rewrite eΓ. exact:(rl_t_C ru).
      -- exact:rAu.
      -- move:ru.
         apply:transport.
         symmetry.
         apply:pt_eq => //.
         ++ apply:JMeq_eq_rect_r.
         ++ apply:JMeq_transport2 => //.
            apply:JMeq_sym.
            apply:JMeq_eq_rect_r.

      -- assumption.
    * apply:rl_wkT => //.
      ++ apply:fV_rT.
    * constructor => //=.
      ++ apply:rl_V_Cη.
         exact:rx.
  + rename w into wu.
    assert ( wA' : Γ ⊢ A).
    { abstract (by inversion wΓ).  }
    assert ( wΓ' :WC Γ).
    { abstract (by inversion wΓ).  }
    move/semt:(wu).
    move/(_ wΓ' wA') => IHu.
    have e : wΓ = w_ext wΓ' wA' wu by apply:WC_hp.
    subst.
    have ru := ft_r IHu.
    (* have r :  rl_C wΓ' (ft_C IHu) *)

    econstructor.
    * constructor; last by apply:ru.
      -- exact:(rl_t_C ru).
      -- exact:(ft_rT IHu).
    * have h :=(ft_rT IHu).
      apply:rl_wkT; eassumption.
    * constructor.
      -- exact:(rl_t_C ru).
      -- exact:(ft_rT IHu).
      -- assumption.
  + rename w into wu.
    inversion wΓ; subst.
    rename H3 into wA'.
    rename H2 into wΓ'.
    clear H4.
    move/semt:(wu).
    move/(_ wΓ' wA') => IHu.
    have e : wΓ = w_ext wΓ' wA' wu by apply:WC_hp.
    subst.
    have ru := ft_r IHu.

    inversion wA; subst.
    rename H3 into wAe.
    rename H5 into wue.
    have e : wA = w_ar wAe (w_va (w_v1 wu)) wue by apply:WTy_hp.
    subst.
    (* have r :  rl_C wΓ' (ft_C IHu) *)

    econstructor.
    * apply:rl_v0 ; last by apply:ru.
      -- exact:(rl_t_C ru).
      -- exact:(ft_rT IHu).
    * have h :=(ft_rT IHu).
      constructor.
      -- constructor.
         ++ exact: (rl_t_C ru).
         ++ assumption.
         ++ assumption.
      -- apply: rl_wkT; eassumption.
      -- constructor.
         constructor.
         ++ exact: (rl_t_C ru).
         ++ assumption.
         ++ assumption.
      -- apply:rl_wkt; eassumption.
    * constructor.
      -- exact:(rl_t_C ru).
      -- exact:(ft_rT IHu).
      -- assumption.

  
- destruct wσ.
  + move/semt:(w) => /(_ wΓ (w_star wΓ)) IHt.
    have e : wΔ = w_astar by apply:WC_hp.
    have rt := (ft_r IHt).

    subst wΔ.
    econstructor.
    constructor.
    * exact:(rl_t_C rt).
    * simpl.
      apply:tp_rTm1; last by exact:rt.
      -- reflexivity.
      -- unshelve eapply pt_eq1.
         ++   apply:π_eq_pTη.  
              apply:rl_hpT.
              ** constructor.
                 exact:(rl_t_C rt).
              ** apply :(ft_rT IHt).
         ++  apply eq_rect_inv.
  + 
    have wΔ' : WC Δ by inversion wΔ.
    move/semS:(wσ) => /(_ wΓ wΔ') IHσ.
    move/semT:(w) => /(_  wΔ') IHA.
    move/semt:(w0) => /(_  wΔ' w) IHu.
    have wAσ := WTy_sb wΓ wΔ' wσ w.
    have wuσ := Wtm_sb wΓ wΔ' wσ w0.
    move/semt:(w2) => /(_  wΓ (w_ar wAσ w1 wuσ)) IHf.
    move/semt:(w1) => /(_  wΓ wAσ) IHt.
    have e : wΔ = w_ext wΔ' w w0 by apply:WC_hp.
    subst.
    have rσ := fS_r IHσ.
    have rA := fT_r IHA.
    have ru := ft_r IHu.
    have rt := ft_r IHt.
    have rf := ft_r IHf.
    have esΔ : fT_C IHA = fS_Δ IHσ.
    {
      apply:rl_hpC.
      - exact:(rl_T_C rA).
      - exact:(rl_S_C2 rσ).
    }
  
    have esΔ' : fS_Δ IHσ = ft_C IHu.
    {
      apply:rl_hpC.
      - exact:(rl_S_C2 rσ).
      - exact:(rl_t_C ru).
    }
    have e :   fS_Γ IHσ  = ft_C IHt.
    {
      apply:rl_hpC.
      - exact:(rl_S_C1 rσ).
      - apply:(rl_t_C rt).
    }


    destruct IHσ,IHu,IHA,IHf,IHt; simpl in *; subst.
    have e :   fT_T0  = ft_T0 by apply:π_eq_pTη; apply:rl_hpT; eassumption.
    subst.
    have e :   ft_C1  = ft_C2.
    {
      apply:rl_hpC.
      - exact:(rl_t_C rf).
      - exact:(rl_t_C rt).
    }
    subst.
    have e : ft_T2 = r_sbT fS_S0 ft_T0.
    {
      apply:π_eq_pTη.
      apply:rl_hpT; last first.
      + apply:(rl_sbT (pA := mkpT ft_T0)); eassumption.
      + apply:tp_rT1; last by exact:ft_rT2.
        * reflexivity.
        * reflexivity.
    }
    subst.

  (* {| pt_C := fS_Γ0; pt_T := r_sbT fS_S0 (eq_rect_r rT ft_T0 (erefl ft_C0)); pt_t := ?Goal2 |} = *)
  (* {| pt_C := ft_C2; pt_T := ft_T2; pt_t := ft_t2 |} *)

    econstructor.
    apply:rl_to_ext.
    * apply:(rl_S_C1 rσ).
    * apply:(rl_S_C2 rσ).
    * simpl.
      apply:tp_rT1; last by exact:rA.
      -- reflexivity.
      -- unshelve eapply pT_eq1.
         ++ now symmetry.
         ++ reflexivity.
    * simpl.

      apply:tp_rTm1; last by exact:ru.
      -- reflexivity.
      -- reflexivity.
    * simpl. exact:rσ.
    * simpl.
      apply:tp_rTm1; last by exact:ft_r2.
      -- reflexivity.
      -- unshelve eapply pt_eq1.
         ++ reflexivity.
         ++  reflexivity.
            (* apply:eq_rect_inv. *)
    * simpl.
      apply:tp_rTm1; last by exact:rf.
      -- reflexivity.
      -- unshelve eapply pt_eq1.
         ++ cbn.
            apply:π_eq_pTη.
            apply:rl_hpT; last first.
            ** eassumption.
            ** cbn.
               apply:rl_ar.
               --- apply :(rl_T_C ft_rT1).
               --- assumption.
               --- exact:rt. 
               --- apply:tp_rTm1; last first.
                   +++ apply: (rl_sbt (pt := mkpt ft_t0)); eassumption.
                   +++ reflexivity.
                   +++ reflexivity.
         ++ cbn.
            apply:eq_rect_inv.
    Unshelve.
    assumption.
    apply:(WTy_sb _ _ wσ) => //.
    apply:(Wtm_sb _ _ wσ) => //.
Defined.

End OmegaGroupoid.