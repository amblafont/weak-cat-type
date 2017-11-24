(* -*- coq-prog-name: "coqtop"; -*- *)


(*
Dans Eric et Sam, le fait que les termes ne changent pas quand on fait un weakening
est crucial pour la première règle de cohérence pour les omega cat : Γ ⊢ t →_A u
et ∂+Γ ⊢ t : A

A ton vraiment besoin de FV(∂+Γ)=FV(t) ? Une simple inclusion ne suffit pas ?
 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import EqdepFacts.
Require Import Coq.Logic.JMeq.
Require Import ssreflect ssrfun ssrbool .
From Modules Require Import lib libhomot gensyntax.


Require Import Coq.MSets.MSetList.
Set Bullet Behavior "Strict Subproofs".

(* We give a structure of ordered type on Var *)
(*
Module VarMod : OrderedTypeWithLeibniz.

Definition t := Var.
Definition eq := @eq t.
Instance eq_equiv : Equivalence eq := eq_equivalence.

Inductive ltI : t -> t -> Prop :=
   lt_v01 : ltI v0 v1
 | lt_v1wk x : ltI v1 (vwk x)
 | lt_v0wk x : ltI v0 (vwk x)
 | lt_vwkwk x y : ltI x y -> ltI (vwk x) (vwk y)
 (* cette branche ne devrait pas exister si tout est bien typé *)
 | lt_vstar x : (if x is vstar then False else True) -> ltI vstar x.

Definition lt := ltI.

Instance lt_strorder : StrictOrder lt.
Proof.
  constructor.
  - move => x.
    move.
    induction x; inversion 1.
    + assumption.
    + by apply:IHx.
  - move => x y z Rxy Ryz.
    move:  z Ryz.
    induction Rxy; inversion 1 => //=; constructor => //.
    apply:IHRxy.
    by subst.
    (* + constructor. *)
    (* + constructor => //. *)
    (* + constructor => //. *)
    (* + constructor => //. *)
    (* + constructor => //. *)
Qed.
Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
Proof.
now unfold eq; split; subst.
Qed.
Fixpoint compare (x y : Var) : comparison :=
  match x,y with
  | v0, v0 | v1, v1 | vstar,vstar => Eq
  | vwk x, vwk y => compare x y
  | v0, v1 => Lt
  | v0, vwk x | v1, vwk x  => Lt
  | vstar,_ => Lt
  | _,_ => Gt
  end.
Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
Proof.
  induction x.
  - destruct y => //=; repeat constructor.
  - destruct y => //=; repeat constructor.
    case:(IHx y) => ?.
    + constructor.
      by apply:f_equal.
    + repeat constructor => //.
    + repeat constructor => //.
  - destruct y => //; repeat constructor.
  - destruct y => //; repeat constructor.
Qed.
(* TODO généraliser ce lemme. C'est bizarre que ça ne soit pas déjà défini dans la lib standard *)
Definition eq_dec (x y : t) : {eq x y} + {~ eq x y}.
case_eq (compare x y) => h.
- left.
   case:(compare_spec x y) h => //=.
- right.
  case:(compare_spec x y) h => //=.
  intros.
  rewrite /eq => h'.
  subst.
  apply:(irreflexivity (R := lt) ).
  eassumption.
- right.
  case:(compare_spec x y) h => //=.
  intros.
  rewrite /eq => h'.
  subst.
  apply:(irreflexivity (R := lt) ).
  eassumption.
Defined.
Definition eq_leibniz a b (H:eq a b) := H.

End VarMod.

Module VarSet  := MSetList.MakeWithLeibniz VarMod.
*)
(* On ne peut pas faire de map !! VarSet.map n'existe pas !! *)

(* je ne peux pas faire écrire la fonction récursive correspondant à
ce type inductif avec VarSet *)
Inductive fvC : Con -> Var -> Type :=
| fv_vstar : fvC astar vstar
| fv_vwk Γ A u x : fvC Γ x -> fvC (ext Γ A u) (vwk x)
| fv_v0 Γ A u  :   fvC (ext Γ A u) v0
| fv_v1 Γ A u  :   fvC (ext Γ A u) v1.

Inductive fvTm : Tm -> Var -> Prop :=
  | fv_va x : fvTm (va x) x
  | fv_coh Γ A σ x : fvS σ x -> fvTm (coh Γ A σ) x
with fvS : sub -> Var -> Type :=
     | fv_to_star t x : fvTm t x -> fvS (to_star t) x
     | fv_to_ext_σ σ a f x : fvS σ x -> fvS (to_ext σ a f) (vwk x)
     | fv_to_ext_a σ a f x : fvTm a x -> fvS (to_ext σ a f) (vwk x)
     | fv_to_ext_f σ a f x : fvTm f x -> fvS (to_ext σ a f) (vwk x).

Inductive fvTy : Ty -> Var -> Type :=
  | fv_ar_A A t u x : fvTy A x -> fvTy (ar A t u) x
  | fv_ar_t A t u x : fvTm t x -> fvTy (ar A t u) x
  | fv_ar_u A t u x : fvTm u x -> fvTy (ar A t u) x.

Fixpoint dimT A : nat :=
  match A with
    star => 0
  | ar A _ _ => S (dimT A)
  end.

Inductive dimC : Con -> nat -> Type :=
| dim_astar : dimC astar 0
| dim_ext_le Γ A u n : dimC Γ n -> dimT A <= n -> dimC (ext Γ A u) n
| dim_ext Γ A u n : dimC Γ n -> dimT A > n -> dimC (ext Γ A u) (dimT A).

(* FV(∂n+ Γ) *)
Inductive fvC_pos (n : nat) : Con  -> Var -> Prop :=
| fv_vstar_pos  : fvC_pos n astar  vstar
| fv_vwk_pos Γ A u  x : n <> dimT A -> fvC_pos n Γ x -> fvC_pos n (ext Γ A u) (vwk x)
(* The last element of Γ removed *)
| fv_vwk_pos_dim Γ A u  x : n = dimT A -> fvC_pos n Γ x ->
                            match x with v0 | vstar => False | _ => True end ->
                            fvC_pos n (ext Γ A u) (vwk x)
| fv_v1_pos Γ A u  : n = dimT A -> fvC_pos n (ext Γ A u) v1.

Inductive fvC_neg (n : nat) : Con  -> Var -> Prop :=
| fv_vstar_neg  : fvC_neg n astar  vstar
| fv_vwk_neg Γ A u  x : fvC_pos n Γ x -> fvC_neg n (ext Γ A u) (vwk x)
| fv_v0_neg Γ A u  : dimT A < n -> fvC_neg n (ext Γ A u) v0
| fv_v1_neg Γ A u  : dimT A < n -> fvC_neg n (ext Γ A u) v1.

(*
En fait si on a FV(t) = FV(∂Γ+) (et FV(A) ⊂ FV(∂Γ+) ? non, inutile ) alors ∂Γ+ ⊢ t : A
Donc pas besoin de définir ∂Γ+
????
TODO vérifier su rpapirer:
*)

(* On veut que Ty contient toutes les variables libres de Con *)

(*
Fixpoint fvC (Γ : Con) : VarSet.t :=

  match Γ with
    astar => VarMod.singleton vstar
  | ext Γ A u => 

with fvT (A : Ty) : VarSet.t
with fvTm (t : Tm) : VarSet.t
with fvS (σ : sub) : VarSet.t
VarSet.add
*)

Definition eqFV_CT ( Γ : Con) (A : Ty) : Type := forall x, fvC Γ x -> fvTy A x.


Definition eqFV_Ct_pos ( Γ : Con) (t : Tm) : Type :=
  forall x n, dimC Γ (S n) -> (fvC_pos n Γ x <-> fvTm t x).

Definition eqFV_Ct_neg ( Γ : Con) (t : Tm) : Type :=
  forall x n, dimC Γ (S n) -> (fvC_neg n Γ x <-> fvTm t x).

Notation "[ 'FVC' A  ~ 'FVT' B ]" := (eqFV_CT A B) : freevar_scope.
Notation "[  'FV' ∂+  A  ~ 'FVt' B ]" := (eqFV_Ct_pos A B) : freevar_scope.
Notation "[  'FV' ∂- A  ~ 'FVt' B ]" := (eqFV_Ct_neg A B) : freevar_scope.
Delimit Scope freevar_scope with fv.

(* La version inductive *)

(* Inductive Wtm_ps : Con -> Ty -> Var -> Type := *)
(*   w_vstar_ps : Wtm_ps astar star vstar *)
(* | w_ext_ps Γ A u : Wtm_ps *)

Inductive Wtm_ps : Con -> Ty -> Var -> Type :=
     | w_vstar_ps : Wtm_ps astar star vstar
     | w_ext_ps Γ A u :
         (* WVar Γ A u -> *)
                        Wtm_ps Γ A u ->
                        Wtm_ps (ext Γ A (va u)) (ar (wkT A) (va v1) (va (vwk u))) v0
                               (* Je ne suis pas obligé de signaler que Γ est un contexte étendu mais
c'est plus simple *)
     | w_right_ps Γ B w A t u f : Wtm_ps (ext Γ B w) (ar A t (va u)) f -> Wtm_ps (ext Γ B w) A u.

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
| w_ext Γ A u : WC Γ -> WTy Γ A ->  WVar Γ A u -> Wtm_ps Γ A u -> WC (ext Γ A (va u))
with WTy : Con -> Ty -> Type :=
       | w_star Γ : WC Γ -> WTy Γ star
       | w_ar Γ A t u : WTy Γ A -> Wtm Γ A t -> Wtm Γ A u -> WTy Γ (ar A t u)
with Wtm : Con -> Ty -> Tm -> Type :=
       | w_va Γ A x : WVar Γ A x -> Wtm Γ A (va x)
       | w_coh_full Γ Δ A σ : WC Δ -> WTy Δ A -> WS Γ Δ σ ->  
                         ([ FVC Δ ~ FVT A ])%fv ->
                         Wtm Γ A.[σ]T (coh Δ A σ) 
       | w_coh_ar Γ Δ A t u σ : WC Δ -> WTy Δ A -> WS Γ Δ σ ->  
                                Wtm Δ A t -> Wtm Δ A u ->
                         ([ FV ∂+ Δ ~ FVt t ])%fv ->
                         ([ FV ∂- Δ ~ FVt u ])%fv ->
                         Wtm Γ (ar A.[σ]T t.[σ]t u.[σ]t) (coh Δ (ar A t u) σ) 
with WS : Con -> Con -> sub -> Type :=
     | w_to_star Γ t : Wtm Γ star t -> WS Γ astar (to_star t)
     | w_to_ext Γ A u Δ σ t f : WS Γ Δ σ ->
                                WTy Δ A ->
                                Wtm Δ A u ->
                                Wtm Γ A.[σ]T t ->
                                Wtm Γ (ar (A.[ σ ]T) t (u.[σ]t)) f ->
                                WS Γ (ext Δ A u) (to_ext σ t f).


Instance syntax : Syntax := Build_Syntax WC WTy Wtm WS.
Reserved Notation "Gamma ⊢_ps A : B"
  (at level 68, A at level 99, no associativity,
   format "Gamma  ⊢_ps  A  :  B").
Notation "Gamma ⊢_ps s : A" := (Wtm_ps Gamma A s) : wf_scope.
Notation "Gamma ⊢_v s : A" := (WVar Gamma A s) : wf_scope.
(*
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
Notation "Gamma ⊢  s  ⇒ Delta" := (WS Gamma Delta s) : wf_scope.

Open Scope wf_scope.
*)

Fixpoint wkTm_inj (a b: Tm) (e : wkt a = wkt b) {struct a}: a = b
with wkS_inj (x y : sub)(e : wkS x = wkS y) {struct x} : x = y.
  - destruct a,b => //=.
    +  by case:e => ->.
    + case:e .
      move => ?? /wkS_inj .
      intros; subst.
      f_equal.
    (* + case:e . *)
    (*   move => ???? /wkS_inj . *)
    (*   intros; subst. *)
    (*   f_equal. *)
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

(* Ici j'utilise JMeq_eq (UIP) mais j'aurai pu m'en passer en le montrant pour la syntaxe *)
Fixpoint Wtm_ps_hp Γ A x (wx : Γ ⊢_ps x : A) : is_center wx.
  destruct wx.
  - move => wx.
    apply:JMeq_eq.
    match goal with [ H : ?C ⊢_ps ?B : ?C2 |- ?a ≅ ?b] =>
                      set (CC := C) in H;
                      set (CS := B) in H;
                      set (CC2 := C2) in H;
                      change (a ≅ b)
    end.
    move:(erefl CC) (erefl CS) (erefl CC2).
    rewrite {2}/CC {2}/CS {2}/CC2.
    case:wx => //=.
  - move => wx'.
    apply:JMeq_eq.
    match goal with [ H : ?C ⊢_ps ?B : ?C2 |- ?a ≅ ?b] =>
                      set (CC := C) in H;
                      set (CS := B) in H;
                      set (CC2 := C2) in H;
                      change (a ≅ b)
    end.
    move:(erefl CC) (erefl CS) (erefl CC2).
    rewrite {2}/CC {2}/CS {2}/CC2.
    case:wx => //=.
    intros; subst.
Abort.


(*
(* Ici j'utilise JMeq_eq mais j'aurai pu m'en passer *)
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

*)