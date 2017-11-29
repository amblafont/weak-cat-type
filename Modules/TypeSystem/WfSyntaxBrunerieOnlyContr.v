(* -*- coq-prog-name: "coqtop"; -*- *)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import EqdepFacts.
Require Import Coq.Logic.JMeq.
Require Import ssreflect ssrfun ssrbool .
From Modules Require Import lib libhomot PreSyntaxOnlyContr Syntax.

Set Bullet Behavior "Strict Subproofs".








(* La version inductive *)
Inductive WVar : Con -> Ty -> Var -> Type :=
  w_vstar : WVar x:⋆ ⋆ vstar
| w_vwk Γ A u B x : WVar Γ B x ->
                 (* Je dois aussi mettre les hypothèses suivantes *)
                    Wtm Γ A u ->
                    WVar (Γ ,C A , #0 → u) (wkT B) (vwk x)
| w_v1 Γ A u : Wtm Γ A u -> WVar (Γ ,C A , #0 → u) (wkT A) v1
| w_v0 Γ A u : Wtm Γ A u -> WVar (Γ ,C A , #0 → u)
                                ((va v1) →⟨ wkT A ⟩ (wkt u)) v0

with WC : Con -> Type :=
  w_astar : WC x:⋆
| w_ext Γ A u : WC Γ -> WTy Γ A ->  Wtm Γ A u -> WC (Γ ,C A , #0 → u)
with WTy : Con -> Ty -> Type :=
       | w_star Γ : WC Γ -> WTy Γ ⋆
       | w_ar Γ A t u : WTy Γ A -> Wtm Γ A t -> Wtm Γ A u -> WTy Γ (t →⟨A⟩ u)
with Wtm : Con -> Ty -> Tm -> Type :=
       | w_va Γ A x : WVar Γ A x -> Wtm Γ A (va x)
       | w_coh Γ Δ A σ : WC Δ -> WTy Δ A -> WS Γ Δ σ ->  
                         (* en principe inutile, mais je le rajoute pour avoir la bonne hypothèse
                           de récurrence *)
                         (* WTy Γ A.[σ]T  -> *)
                         Wtm Γ A.[σ]T (coh Δ A σ) 
with WS : Con -> Con -> sub -> Type :=
     | w_to_star Γ t : Wtm Γ ⋆ t -> WS Γ x:⋆ ❪ t ❫
     | w_to_ext Γ A u Δ σ t f : WS Γ Δ σ ->
                                WTy Δ A ->
                                Wtm Δ A u ->
                                Wtm Γ A.[σ]T t ->
                                Wtm Γ (t →⟨ A.[ σ ]T ⟩  u.[σ]t) f ->
                                WS Γ (Δ ,C A , #0 → u) (σ ,S t , f).


Instance syntax : Syntax preSyntax := Build_Syntax WC WTy Wtm WS.

Notation "Gamma ⊢_v s : A" := (WVar Gamma A s) : wf_scope.

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
