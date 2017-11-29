Require Import ssreflect ssrfun ssrbool .

From Modules Require Import libhomot   lib gensyntax brunerietype gtypeext.
Require Import Coq.Logic.JMeq.
Set Bullet Behavior "Strict Subproofs".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Local Notation "⟦ X ⟧V" := (dTm (w_va X)).

Local Notation "x:⋆" := astar : context_scope.
Local Notation " Gamma , B , #0 → u " := (ext Gamma B u) (at level 68, B at level 58)  : context_scope.

Local Notation "⋆" := star : Ty_scope.
Local Notation "x →⟨ B ⟩ y" := (ar B x y)  (at level 68, B at level 58) : Ty_scope.

Local Notation "❪ t ❫" := (to_star t)   : subst_scope.
Local Notation " Gamma ,S a  , f" := (to_ext Gamma a f) (at level 68, a at level 58)  : subst_scope.


(* TODO : utiliser sigT2 au lieu de extΣ *)
Local Notation "{{ x : A  ,  P  , #0 → Q }}"
  :=
      {δ : {x : A & ∣ P ∣} & ∣ hom δ ..2 ((fun x => Q) δ..1) ∣}
      (at level 68, x at level 58, A at level 58, P at level 58) : ext_scope.

Delimit Scope ext_scope with ext.
Local Open Scope ext_scope.

Delimit Scope ext_scope with ext.
Local Open Scope ext_scope.

Delimit Scope context_scope with C.
Delimit Scope star_scope with T.
Delimit Scope subst_scope with S.


Local Open Scope context_scope.
Local Open Scope Ty_scope.
Local Open Scope subst_scope.


(* TODO : factoriser avec isOmegaCategory *)
(* TODO : imposer l'existence d'un ⟦coh⟧ dans un contexte, comme dans Thorsten et Nuo,
et imposer que ⟦ coh [σ] ⟧ = ⟦ coh ⟧ ∘ ⟦σ⟧, ce qui permet d'éliminer sb_dTm *)

(* Ce record indique que d: Decl permet d'interpréter la syntaxe de Brunerie
compatiblement avec le type globulaire G *)
Record isOmegaGroupoid (G : GType) (d : Decl) :=
  {
    dC_astar : ⟦ (w_astar :  x:⋆ ⊢) ⟧C = ∣ G ∣     ;
    dC_ext : forall Γ A u (wΓ : Γ ⊢) (wA : Γ ⊢ A) (wu : Γ ⊢ u : A),
        (* TODO: définir un type inductif particulier pour cette extension *)
        ⟦ w_ext wΓ wA wu :  Γ , A , #0 → u ⊢ ⟧C =
        {{ γ : ⟦ wΓ ⟧C ,  ⟦ wA ⟧T γ , #0 → ⟦ wu ⟧t wA γ }} ;
        (* @extΣ_G ⟦ wΓ ⟧C ⟦ wA ⟧T (⟦ wu ⟧t wA); *)
    dT_star : forall Γ (wΓ : Γ ⊢)(γ : ⟦ wΓ ⟧C), ⟦ w_star wΓ : Γ ⊢ ⋆ ⟧T γ = G;
    dT_ar : forall Γ A t u (wΓ : Γ ⊢) (wA : Γ ⊢ A) (wt : Γ ⊢ t : A)(wu : Γ ⊢ u : A)
        (γ : ⟦ wΓ ⟧C),
        ⟦ w_ar  wA wt wu : Γ ⊢ t →⟨ A ⟩ u   ⟧T γ = hom (⟦ wt ⟧t wA γ)(⟦ wu ⟧t wA γ);

    (* inutile car déjà compris dans la syntaxe non ? *)
    (*
    sb_dT : forall Γ Δ σ A (wΓ : Γ ⊢)(wΔ : Δ ⊢)(wσ: Γ ⊢ σ ⇒ Δ)(wA : Δ ⊢ A)
              (γ : dC wΓ),
        ⟦ WTy_sb wΓ wΔ wσ wA ⟧T γ = ⟦ wA ⟧T (⟦ wσ ⟧S wΓ wΔ γ);
    (* inutile car déjà compris dans la syntaxe non ? *)
    sb_dS : forall Γ Δ E σ δ  (wΓ : Γ ⊢)(wΔ : Δ ⊢)(wE : E ⊢)(wσ: Γ ⊢ σ ⇒ Δ)(wδ: Δ ⊢ δ ⇒ E)
              (γ : dC wΓ),
        ⟦ WS_sb wΓ wΔ wσ wδ ⟧S wΓ wE γ = ⟦ wδ ⟧S _ wE (⟦ wσ ⟧S wΓ wΔ γ);
*)
    (* inutile car déjà compris dans la syntaxe non ? il suffit de l'imposer pour coh en fait *)
    sb_dTm : forall Γ Δ σ A t (wΓ : Γ ⊢)(wΔ : Δ ⊢)(wσ: Γ ⊢ σ ⇒ Δ)(wA : Δ ⊢ A)
               (wt : Δ ⊢ t : A)
              (γ : ⟦ wΓ ⟧C),
        ⟦ Wtm_sb wΓ wΔ wσ wt : Γ ⊢ t.[σ]t : A.[σ]T ⟧t
                                        (WTy_sb wΓ wΔ wσ wA : Γ ⊢ A.[σ]T) γ
        ≅ ⟦ wt ⟧t wA (⟦ wσ ⟧S wΓ wΔ γ);

    dTm_vstar : forall (γ : ⟦ w_astar : x:⋆ ⊢  ⟧C),
        ⟦ w_vstar : x:⋆ ⊢_v vstar : ⋆ ⟧V (w_star w_astar : x:⋆ ⊢ ⋆) γ ≅ γ;
    dTm_v1 : forall Γ A u (wΓ : Γ ⊢) (wA : Γ ⊢ A) (wu : Γ ⊢ u : A)
               (wAe : Γ , A, #0 → u ⊢ wkT A)
               (γ : ⟦ w_ext wΓ wA wu : Γ ,  A , #0 → u ⊢ ⟧C)
               (γ2 : ⟦ wΓ ⟧C) (sa : ∣ ⟦ wA ⟧T γ2 ∣ )
               (sf : ∣ hom sa (⟦ wu ⟧t wA γ2) ∣ ),
        γ ≅ (((γ2 ,Σ sa) ,Σ sf) :
               {{ x : ⟦ wΓ⟧C ,  ⟦ wA ⟧T x , #0 → (⟦ wu ⟧t wA x) }})
        ->

               (* @extΣ_G ⟦wΓ⟧C ⟦wA⟧T (⟦wu⟧t wA)) *)
               (* { y : ⟦ wΓ⟧C & ⟦wA⟧T y & (⟦ wu ⟧t wA y) }) *)

        ⟦ w_v1 wu : Γ ,  A , #0 → u ⊢_v v1 : _⟧V wAe γ ≅ sa;
    dTm_v0 : forall Γ A u (wΓ : Γ ⊢) (wA : Γ ⊢ A) (wu : Γ ⊢ u : A)
               (wAe : Γ ,  A , #0 → u ⊢ wkT A)
               (wue : Γ ,  A , #0 → u ⊢ wkt u : wkT A)
               (γ : ⟦ w_ext wΓ wA wu : Γ ,  A , #0 → u ⊢  ⟧C)
               (γ2 : ⟦ wΓ ⟧C) (sa : ∣ ⟦ wA ⟧T γ2 ∣)
               (sf : ∣ hom sa (⟦ wu ⟧t wA γ2) ∣),
        γ ≅ (((γ2 ,Σ sa) ,Σ sf) :
               {{ x : ⟦ wΓ⟧C ,  ⟦ wA ⟧T x , #0 → (⟦ wu ⟧t wA x) }})
          
          ->
        ⟦ w_v0 wu : Γ ,  A , #0 → u ⊢_v v0 : _ ⟧V
                   (w_ar wAe (w_va (w_v1 wu)) wue :
                         Γ ,  A , #0 → u ⊢ (va v1) →⟨ wkT A ⟩ (wkt u) 
                     )
                   γ ≅ sf;
    dTm_vwk : forall Γ A u B x (wΓ : Γ ⊢) (wA : Γ ⊢ A) (wu : Γ ⊢ u : A)
                (wB : Γ ⊢ B)
                (wBe : Γ ,  A , #0 → u ⊢ wkT B)
                (wx : Γ ⊢_v x :  B )
               (γ : ⟦ w_ext wΓ wA wu : Γ ,  A , #0 → u ⊢  ⟧C)
               (γ2 : ⟦ wΓ ⟧C) (sa : ∣ ⟦ wA ⟧T γ2 ∣)
               (sf : ∣ hom sa (⟦ wu ⟧t wA γ2) ∣),
        γ ≅ (((γ2 ,Σ sa) ,Σ sf) :
               {{ x : ⟦ wΓ⟧C ,  ⟦ wA ⟧T x , #0 → (⟦ wu ⟧t wA x) }})

          ->
        ⟦ w_vwk wx wu : Γ ,  A , #0 → u ⊢_v vwk x : wkT B ⟧V wBe γ ≅ ⟦ wx ⟧V wB γ2;

    dS_to_star : forall Γ t (wΓ : Γ ⊢) (wt : Γ ⊢ t : star) (γ : ⟦ wΓ ⟧C),
        ⟦ w_to_star wt : Γ ⊢ ❪ t ❫ ⇒ x:⋆  ⟧S _ (w_astar : x:⋆ ⊢) γ
                                           ≅ ⟦ wt ⟧t (w_star wΓ : Γ ⊢ ⋆) γ;

    dS_to_ext :forall Δ Γ A u σ a f (wΓ : Γ ⊢) (wA : Γ ⊢ A) (wu : Γ ⊢ u : A)
                 (wAσ : Δ ⊢ A.[σ]T) (wuσ : Δ ⊢ u.[σ]t : A.[σ]T)
                 (wΔ : Δ ⊢) (wσ  : Δ ⊢ σ ⇒ Γ)
                 (wa : Δ ⊢ a : A.[σ]T)
                 (* (wf : Δ ⊢ f.[σ]t : (a →⟨ A.[σ]T ⟩ u.[σ]t)) *)
                 (wf : Δ ⊢ f : (a →⟨ A.[σ]T ⟩ u.[σ]t))
                 (γ : ⟦ wΔ ⟧C)
                 (sa : ∣ ⟦ wA ⟧T (⟦ wσ ⟧S wΔ wΓ γ ) ∣)
                 (suσ : forall γ, ∣ ⟦ wA ⟧T (⟦ wσ ⟧S wΔ wΓ γ ) ∣)
                 (sf : ∣ hom sa _ ∣)
                 (* TODO réfléchir : cette définition est potentiellement fausse *)
      , sa ≅ ⟦ wa ⟧t wAσ γ ->
        suσ γ ≅ ⟦ wu ⟧t wA (⟦ wσ ⟧S wΔ wΓ γ ) ->
        sf ≅ ⟦ wf ⟧t (w_ar  wAσ wa wuσ : Δ ⊢ a →⟨ A.[σ]T ⟩ u.[σ]t ) γ ->
        ⟦ w_to_ext wσ wA wu wa wf : Δ ⊢ (σ ,S a , f) ⇒ (Γ ,  A , #0 → u) ⟧S wΔ
                                   (w_ext wΓ wA wu : Γ ,  A , #0 → u ⊢) γ ≅
                                   (* (( *)
                                   ((((⟦ wσ ⟧S wΔ wΓ γ ,Σ sa) :
                                        sigT (fun γ => ∣ ⟦ wA ⟧T γ ∣))
                                        ,Σ sf) : 
          { x : sigT (fun γ => ∣ ⟦wA⟧T γ ∣) & ∣ hom x..2 (⟦ wu ⟧t wA x..1) ∣ })

                                
    }.



(* Lemma   sb_dT (G: GType) (d  : decl)   Γ Δ σ A (wΓ : Γ ⊢)(wΔ : Δ ⊢)(wσ: Γ ⊢ σ ⇒ Δ)(wA : Δ ⊢ A) *)
(*               (γ : dC wΓ) : *)
(*         ⟦ WTy_sb wΓ wΔ wσ wA ⟧T γ = ⟦ wA ⟧T (⟦ wσ ⟧S wΓ wΔ γ); *)



