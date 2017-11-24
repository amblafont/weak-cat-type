(* -*- coq-prog-name: "coqtop"; -*- *)

(* Ici on a le droit à tous les contextes *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import EqdepFacts.
Require Import Coq.Logic.JMeq.
Require Import ssreflect ssrfun ssrbool .
From Modules Require Import lib libhomot defsyntax.

Set Bullet Behavior "Strict Subproofs".


Module Syn := defsyntax.

Inductive Tm : Type :=
  | va (x:Var)
          (* Coh Γ A σ  *)
  | coh : Con -> Ty -> sub -> Tm
with Ty : Type :=
  | star
  | ar : Ty -> Tm -> Tm -> Ty
with  Con : Type :=
      | empty
          (* Γ A, u tq Γ ⊢ u : A *)
      | ext : Con -> Ty -> Con
with sub : Type :=
       | to_empty : sub
       | to_ext : sub -> Tm -> sub
with Var : Type :=
  | v0
  | vwk (v : Var).

Instance preSyntax : PreSyntax := {| Syn.Con := Con ;  Syn.Ty := Ty ; Syn.Tm := Tm ; Syn.sub := sub |}.



Fixpoint sub_Var (σ : sub) (x : Var) : Tm :=
   match σ,x with
   | to_ext σ a , vwk x => x .[ σ ]V
   | to_ext σ a , v0 => a
   | _,_ => va v0 (* dummy *)
   end
where "s .[ sigma ]V" := (sub_Var sigma s) : subst_scope.

(* Reserved Notation "sigma ∘ delta" := (compS sigma delta)(at level 40, left associativity) : subst_scope. *)
(* Reserved Notation "sigma ∘ delta"  (at level 40, left associativity). *)

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
         | to_empty  => to_empty
         (* Γ ⊢ σ' : Δ' *)
         (* E ⊢ σ ∘ δ : Δ *)
         (* E ⊢ (σ ∘ δ)' : Δ' *)
         | to_ext σ a  => to_ext (σ ∘ δ) (a .[ δ ]t) 
       end
where "s .[ sigma ]t" := (sub_Tm sigma s) : subst_scope
  and "sigma ∘ delta" := (compS sigma delta) :subst_scope.




Fixpoint wkt (t : Tm) : Tm :=
  match t with
    va x => va (vwk x)
  | coh Γ A σ => coh Γ A (wkS σ)
  end
with wkS (σ : sub) : sub :=
  match σ with
  | to_empty => to_empty
  | to_ext σ a => to_ext (wkS σ) (wkt a)
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



  
(*
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

*)
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
| w_vwk Γ A B x : WVar Γ B x ->
                 (* Je dois aussi mettre les hypothèses suivantes *)
                    WVar (ext Γ A) (wkT B) (vwk x)
| w_v0 Γ A  :  WVar (ext Γ A) ((wkT A) ) v0


with isContr : Con -> Type :=
| c_astar : isContr (ext empty star)
                    (* Je suis un peu paranoique dans cette définition car j'ai la flemme de montrer
les lemmes adéquats *)
| c_ext Γ A u : isContr Γ -> WTy Γ A -> Wtm Γ A u ->
                WTy (ext Γ A) (wkT A) -> Wtm (ext Γ A) (wkT A) (wkt u) ->
                isContr (ext (ext Γ A) (ar ((wkT A)) (va v0) ((wkt u))))

with WC : Con -> Type :=
  w_empty : WC empty
| w_ext Γ A  : WC Γ -> WTy Γ A ->   WC (ext Γ A )
with WTy : Con -> Ty -> Type :=
       | w_star Γ : WC Γ -> WTy Γ star
       | w_ar Γ A t u : WTy Γ A -> Wtm Γ A t -> Wtm Γ A u ->
                        WTy Γ (ar A t u)
with Wtm : Con -> Ty -> Tm -> Type :=
       | w_va Γ A x : WVar Γ A x -> Wtm Γ A (va x)
       | w_coh Γ Δ A σ : isContr Δ
                                 (* inutile car redondant avec isContr *)
                         -> WC Δ
                         -> WTy Δ A -> WS Γ Δ σ ->
                         (* en principe inutile, mais je le rajoute pour avoir la bonne hypothèse
                           de récurrence *)
                         (* WTy Γ A.[σ]T  -> *)
                         Wtm Γ A.[σ]T (coh Δ A σ) 
with WS : Con -> Con -> sub -> Type :=
     | w_to_empty Γ  : WS Γ empty (to_empty)
     | w_to_ext Γ A Δ σ t : WS Γ Δ σ ->
                                WTy Δ A ->
                                Wtm Γ A.[σ]T t ->
                                WS Γ (ext Δ A) (to_ext σ t ).


Lemma isContr_ext_inv Γ A u  (P : forall  : isContr (ext Γ A u)
(*
Record r_isContr Γ A u :=
  { isC_u : Tm;
    isC_eu : u = wkt isC_u ;
    isC_rec : isContr Γ;


Fixpoint isContr_fix (Γ : Con) : Type :=
  match Γ with
| ext empty star => True
| ext (ext Γ A) (ar _ (va v0) u) => { u' : Tm & u = wkt u' } * isContr Γ * 
| _ => False
  end.
*)
Instance syntax : Syntax := Build_Syntax WC WTy Wtm WS.

(*
Lemma isContr_WC Γ (isC : isContr Γ) : WC Γ.
  induction isC.
  - repeat constructor.
  - repeat constructor => //.
Qed.
*)


(*
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

(* Ici j'utilise JMeq_eq général mais j'aurai pu le montrer en particulier en
montrant UIP spécifiquement sur la syntaxe *)
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

(* Notation "Gamma ⊢ A" := (WTy Gamma A)  . *)
(* Notation "Gamma ⊢ s : A" := (Wtm Gamma A s). *)
(* Notation "Gamma ⊢  s  ⇒ Delta" := (WS Gamma Delta s). *)

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
  + assert ( wA : (Γ ⊢ A)).
    {
     apply:WTm_Ty.
      -- now inversion wΓ.
      -- eassumption.
    }

    apply:WTy_wk => //.
  + assert ( wA : Γ ⊢ A).
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

*)