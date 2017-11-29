Require Import ssreflect ssrfun ssrbool .
(* Definition selon Brunerie : on a tous les contextes.
Selon moi, c'est plus éloigné de la définition mathématique de Maltsioniotis mais bon.. *)

From Modules Require Import libhomot untypeduippackrl buildrlhp lib Syntax WfSyntaxBrunerieAllCtx gtypeext.
Require Import Coq.Logic.JMeq.
Set Bullet Behavior "Strict Subproofs".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Local Notation "⟦ X ⟧V" := (dTm (w_va X)).




(* TODO : factoriser avec isOmegaCategory *)

Record isFullOmegaGroupoid (G : GType) (d : Decl) :=
  {
    dC_astar : ⟦ w_empty ⟧C = unit    ;
    dC_ext : forall Γ A  (wΓ : WC Γ) (wA : Γ ⊢ A) ,
        (* TODO: définir un type inductif particulier pour cette extension *)
        ⟦ w_ext wΓ wA  ⟧C = { γ :  ⟦ wΓ ⟧C & ⟦ wA ⟧T γ};
        (* { δ : { γ : ⟦ wΓ ⟧C & ⟦ wA ⟧T γ} & hom (δ..2) (⟦ wu ⟧t wA δ..1)}; *)
    dT_star : forall Γ (wΓ : WC Γ)(γ : dC wΓ), ⟦ w_star wΓ ⟧T γ = G;
    dT_ar : forall Γ A t u (wΓ : WC Γ) (wA : Γ ⊢ A) (wt : Γ ⊢ t : A)(wu : Γ ⊢ u : A)
        (γ : dC wΓ),
        ⟦ w_ar  wA wt wu ⟧T γ = hom (⟦ wt ⟧t wA γ)(⟦ wu ⟧t wA γ);

    (* En fait, il faut l'imposer seulement pour le coh *)
    sb_dTm : forall Γ Δ σ A t (wΓ : WC Γ)(wΔ : WC Δ)(wσ: Γ ⊢ σ ⇒ Δ)(wA : Δ ⊢ A)
               (wAσ : Γ ⊢ A.[σ]T)
               (wt : Δ ⊢ t : A)(wtσ : Γ ⊢ t.[σ]t : A.[σ]T)
              (γ : dC wΓ),
        ⟦ wtσ ⟧t wAσ γ
        ≅ ⟦ wt ⟧t wA (⟦ wσ ⟧S wΓ wΔ γ);

    (* dTm_vstar : forall (γ : ⟦ w_astar ⟧C), ⟦ w_vstar ⟧V (w_star w_astar) γ ≅ γ; *)
    dTm_v0 : forall Γ A  (wΓ : WC Γ) (wA : Γ ⊢ A) 
               (wAe : ext Γ A ⊢ wkT A)
               (γ : ⟦ w_ext wΓ wA  ⟧C)
               (γ2 : ⟦ wΓ ⟧C) (sa : ⟦ wA ⟧T γ2),
        γ ≅ ((γ2 ,Σ sa) :sigT ⟦wA⟧T ) ->
        ⟦ w_v0 Γ A ⟧V (wAe) γ ≅ sa;
    dTm_vwk : forall Γ A B x (wΓ : WC Γ) (wA : Γ ⊢ A) 
                (wB : Γ ⊢ B)
                (wBe : ext Γ A  ⊢ wkT B)
                (wx : WVar Γ B x)
               (γ : ⟦ w_ext wΓ wA  ⟧C)
               (γ2 : ⟦ wΓ ⟧C) (sa : ⟦ wA ⟧T γ2),
        γ ≅ (((γ2 ,Σ sa) :sigT ⟦ wA⟧T) ) ->
        ⟦ w_vwk A wx  ⟧V wBe γ ≅ ⟦ wx ⟧V wB γ2;


    dS_to_ext :forall Δ Γ A  σ a  (wΓ : WC Γ) (wA : Γ ⊢ A) 
                 (wAσ : Δ ⊢ A.[σ]T) 
                 (wΔ : WC Δ) (wσ  : Δ ⊢ σ ⇒ Γ)
                 (wa : Δ ⊢ a : A.[σ]T)
                 (γ : ⟦ wΔ ⟧C)
                 (sa : ⟦ wA ⟧T (⟦ wσ ⟧S wΔ wΓ γ ))
      , sa ≅ ⟦ wa ⟧t wAσ γ ->
        ⟦ w_to_ext wσ wA wa ⟧S wΔ (w_ext wΓ wA ) γ ≅
                                   (* (( *)
                                       ((((⟦ wσ ⟧S wΔ wΓ γ ,Σ sa) : sigT ⟦ wA ⟧T) 
                                        ) )

                                
    }.



