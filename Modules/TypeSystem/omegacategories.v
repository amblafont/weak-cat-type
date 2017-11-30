Require Import ssreflect ssrfun ssrbool .

From Modules Require Import HomotopicalEquality  lib PreSyntaxOnlyContr WfSyntaxEricSamOnlyPs gtype decl.
Set Bullet Behavior "Strict Subproofs".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Local Notation "⟦ X ⟧V" := (dTm (w_va X)).



(* TODO : factoriser avec la definition d'omega groupoid. C'est la même !! *)
Record isOmegaCategory (G : GType) (d : Decl) :=
  {
    dC_astar : ⟦ w_astar ⟧C = ∣ G ∣   ;
    dC_ext : forall Γ A u (wΓ : WC Γ) (wA : Γ ⊢ A) (wu : Γ ⊢_v u : A) wu_ps,
        (* TODO: définir un type inductif particulier pour cette extension *)
        ⟦ w_ext wΓ wA wu wu_ps ⟧C = @extΣ_G ⟦ wΓ ⟧C ⟦ wA ⟧T (⟦ w_va wu ⟧t wA);
        (* { δ : { γ : ⟦ wΓ ⟧C & ⟦ wA ⟧T γ} & hom (δ..2) (⟦ wu ⟧t wA δ..1)}; *)
    dT_star : forall Γ (wΓ : WC Γ)(γ : dC wΓ), ⟦ w_star wΓ ⟧T γ = G;
    dT_ar : forall Γ A t u (wΓ : WC Γ) (wA : Γ ⊢ A) (wt : Γ ⊢ t : A)(wu : Γ ⊢ u : A)
        (γ : dC wΓ),
        ⟦ w_ar  wA wt wu ⟧T γ = hom (⟦ wt ⟧t wA γ)(⟦ wu ⟧t wA γ);

    (* inutile car déjà compris dans la syntaxe non ? *)
    (*
    sb_dT : forall Γ Δ σ A (wΓ : WC Γ)(wΔ : WC Δ)(wσ: Γ ⊢ σ ⇒ Δ)(wA : Δ ⊢ A)
              (γ : dC wΓ),
        ⟦ WTy_sb wΓ wΔ wσ wA ⟧T γ = ⟦ wA ⟧T (⟦ wσ ⟧S wΓ wΔ γ);
    (* inutile car déjà compris dans la syntaxe non ? *)
    sb_dS : forall Γ Δ E σ δ  (wΓ : WC Γ)(wΔ : WC Δ)(wE : WC E)(wσ: Γ ⊢ σ ⇒ Δ)(wδ: Δ ⊢ δ ⇒ E)
              (γ : dC wΓ),
        ⟦ WS_sb wΓ wΔ wσ wδ ⟧S wΓ wE γ = ⟦ wδ ⟧S _ wE (⟦ wσ ⟧S wΓ wΔ γ);
*)
    (* inutile car déjà compris dans la syntaxe non ? il suffit de l'imposer pour coh en fait *)
    sb_dTm : forall Γ Δ σ A t (wΓ : WC Γ)(wΔ : WC Δ)(wσ: Γ ⊢ σ ⇒ Δ)(wA : Δ ⊢ A)
               (wAσ : Γ ⊢ A.[σ]T)
               (wt : Δ ⊢ t : A)(wtσ : Γ ⊢ t.[σ]t : A.[σ]T)
              (γ : dC wΓ),
        ⟦ wtσ ⟧t wAσ γ
        ≅ ⟦ wt ⟧t wA (⟦ wσ ⟧S wΓ wΔ γ);

    dTm_vstar : forall (γ : ⟦ w_astar ⟧C), ⟦ w_vstar ⟧V (w_star w_astar) γ ≅ γ;
    dTm_v1 : forall Γ A u (wΓ : WC Γ) (wA : Γ ⊢ A) (wu : Γ ⊢_v u : A)(wu_ps : Γ ⊢_ps u : A)
               (wAe : ext Γ A (va u) ⊢ wkT A)
               (γ : ⟦ w_ext wΓ wA wu wu_ps ⟧C)
               (γ2 : ⟦ wΓ ⟧C) (sa : ∣ ⟦ wA ⟧T γ2 ∣)
               (sf : ∣ hom sa (⟦ wu ⟧V wA γ2) ∣),
        γ ≅ (((γ2 ,Σ sa) ,Σ sf) : extΣ_G  _) ->
        ⟦ w_v1 (w_va wu) ⟧V wAe γ ≅ sa;
    dTm_v0 : forall Γ A u (wΓ : WC Γ) (wA : Γ ⊢ A) (wu : Γ ⊢_v u : A)(wu_ps : Γ ⊢_ps u : A)
               (wAe : ext Γ A (va u) ⊢ wkT A)(wue : ext Γ A (va u) ⊢_v vwk u : wkT A)
               (γ : ⟦ w_ext wΓ wA wu wu_ps ⟧C)
               (γ2 : ⟦ wΓ ⟧C) (sa : ∣ ⟦ wA ⟧T γ2 ∣)
               (sf : ∣ hom sa (⟦ wu ⟧V wA γ2) ∣),
        γ ≅ (((γ2 ,Σ sa) ,Σ sf) : extΣ_G  _) ->
        ⟦ w_v0 (w_va wu) ⟧V (w_ar wAe (w_va (w_v1 (w_va wu))) (w_va wue)) γ ≅ sf;
    dTm_vwk : forall Γ A u B x (wΓ : WC Γ) (wA : Γ ⊢ A) (wu : Γ ⊢_v u : A)
                (wu_ps : Γ ⊢_ps u : A)
                (wB : Γ ⊢ B)
                (wBe : ext Γ A (va u) ⊢ wkT B)
                (wx : WVar Γ B x)
               (γ : ⟦ w_ext wΓ wA wu wu_ps ⟧C)
               (γ2 : ⟦ wΓ ⟧C) (sa : ∣ ⟦ wA ⟧T γ2 ∣)
               (sf : ∣ hom sa (⟦ wu ⟧V wA γ2) ∣),
        γ ≅ (((γ2 ,Σ sa) ,Σ sf) : extΣ_G  _) ->
        ⟦ w_vwk wx (w_va wu) ⟧V wBe γ ≅ ⟦ wx ⟧V wB γ2;

    dS_to_star : forall Γ t (wΓ : WC Γ) (wt : Γ ⊢ t : star) (γ : ⟦ wΓ ⟧C),
                   ⟦ w_to_star wt ⟧S _ w_astar γ ≅ ⟦ wt ⟧t (w_star wΓ) γ;

    dS_to_ext :forall Δ Γ A u σ a f (wΓ : WC Γ) (wA : Γ ⊢ A) (wu : Γ ⊢_v u : A)
                 (wu_ps : Γ ⊢_ps u : A)
                 (wAσ : Δ ⊢ A.[σ]T) (wuσ : Δ ⊢ u.[σ]V : A.[σ]T)
                 (wΔ : WC Δ) (wσ  : Δ ⊢ σ ⇒ Γ)
                 (wa : Δ ⊢ a : A.[σ]T)
                 (wf : Δ ⊢ f.[σ]t : ar A.[σ]T a (u.[σ]V))
                 (γ : ⟦ wΔ ⟧C)
                 (sa : ∣ ⟦ wA ⟧T (⟦ wσ ⟧S wΔ wΓ γ ) ∣)
                 (suσ : forall γ, ∣ ⟦ wA ⟧T (⟦ wσ ⟧S wΔ wΓ γ ) ∣)
                 (sf : ∣ hom sa _ ∣)
      , sa ≅ ⟦ wa ⟧t wAσ γ ->
        suσ γ ≅ ⟦ wu ⟧V wA (⟦ wσ ⟧S wΔ wΓ γ ) ->
        sf ≅ ⟦ wf ⟧t (w_ar  wAσ wa wuσ) γ ->
        ⟦ w_to_ext wσ wA (w_va wu) wa wf ⟧S wΔ (w_ext wΓ wA wu wu_ps) γ ≅
                                   (* (( *)
                                          ((((⟦ wσ ⟧S wΔ wΓ γ ,Σ sa)
                                        : sigT (fun γ => ∣ ⟦ wA ⟧T γ ∣))
                                        ,Σ sf) : 
          (* { x : sigT ⟦wA⟧T &  hom x..2 (⟦ wu ⟧V wA x..1) }) *)
          { x : sigT (fun γ => ∣ ⟦wA⟧T γ ∣) & ∣ hom x..2 (⟦ wu ⟧V wA x..1) ∣ })

                                
    }.





