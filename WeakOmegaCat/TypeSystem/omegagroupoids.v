(* -*- coq-prog-name: "coqtop"; -*- *)
(* From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq. *)
Require Import ssreflect ssrfun ssrbool .

Require Import Coq.Logic.JMeq.
Require Import libhomot.
Require Import untypeduippackrl.
Require Import buildrlhp lib brunerietype.
Require Import Coq.Logic.JMeq.
Set Bullet Behavior "Strict Subproofs".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

CoInductive GType :=
  Gtyp { ob :> Type ;
         hom :> ob -> ob -> GType }.

CoFixpoint G_of_T (T : Type) : GType.
  unshelve econstructor.
  - exact:T.
  - move => a b.
    apply:G_of_T.
    exact: (a =h b).
Defined.
(* Notation "∣ X ∣" := (ob X). *)

Class Decl :=
  { dC : forall Γ, WC Γ -> Type;
    dTy : forall Γ A (wΓ : WC Γ)(wA: Γ ⊢ A), dC wΓ -> GType ;
    dTm : forall Γ A t (wΓ : WC Γ)(wt : Γ ⊢ t : A)(wA: Γ ⊢ A)(γ : dC wΓ) ,
            dTy wA γ;
    dS : forall Γ Δ σ (wσ: Γ ⊢ σ ⇒ Δ)(wΓ : WC Γ)(wΔ : WC Δ) (γ : dC wΓ),
            dC wΔ
  }.


Section TypeDecl.
  Variable (T: Type).
  Variable (fibT: Fib T).
(* TODO  déplacer ces lemmas dans untyp et les utiliser dans la def de sem* *)
  Definition typDecl   : Decl.
 unshelve econstructor.
 - move => Γ wΓ.
   apply:C_TY.
   apply:fC_C.
   apply: (semC fibT wΓ).
 - move => Γ A wΓ wA γ.
   apply:G_of_T.
   apply:T_TY.
   + apply:fT_T.
     apply: (semT fibT wΓ wA).
   + simpl.
     simpl in γ.
     apply:transport γ.
     apply:eqf_CC_TC.
     
 - move => Γ A t wΓ wt wA /= γ.
   move/semt:(wt).
   move/(_ _ fibT wΓ wA) => st.
   apply:t_t.
   move/ft_t:(st).
   (* set sT := semT _ _ _. *)
   (* move =>[:eqT]. *)
   apply:transport2.
   + apply:eqf_tC_TC.
   + apply:eqf_tT_TT.
 - move => Γ Δ σ wσ wΓ wΔ /= γ.
   apply:S; last by exact:γ.
   set sσ := (semS fibT wΓ wΔ wσ).
   apply:(transport2 _ _ (fS_S sσ)).
   + apply:eqf_SC1_CC.
   + apply:JMeq_from_eq.
     apply:eqf_SC2_CC.
Defined.

End TypeDecl.


Notation "⟦ X ⟧C" := (dC X).
Notation "⟦ X ⟧T" := (dTy X).
Notation "⟦ X ⟧t" := (dTm X).
Notation "⟦ X ⟧V" := (dTm (w_va X)).
Notation "⟦ X ⟧S" := (dS X).

(* Record isGType (d : Decl) := *)

(* inspiré de nuo et thorsten *)

(* Notation "x ..1" := (projT1 x) (at level 2). *)
(* Notation "x ..2" := (projT2 x) (at level 2). *)
(* Notation "x ,Σ y" := (existT _ x y)  (at level 70). *)
(* Notation "x ≅ y" := (JMeq  x  y) (at level 70, y at next level, no associativity). *)

Definition extΣ (Γ : Type) (A : Γ -> Type) (B : forall γ (a : A γ), Type) :=
  { δ : { γ : Γ & A γ} & B (δ..1) δ..2}.

Definition extΣ_G (Γ : Type) (A : Γ -> GType) (u : forall γ, A γ) :=
  { δ : { γ : Γ & A γ} & hom δ..2 (u δ..1) }.

Record isOmegaGroupoid (G : GType) (d : Decl) :=
  {
    dC_astar : ⟦ w_astar ⟧C = G    ;
    dC_ext : forall Γ A u (wΓ : WC Γ) (wA : Γ ⊢ A) (wu : Γ ⊢ u : A),
        (* TODO: définir un type inductif particulier pour cette extension *)
        ⟦ w_ext wΓ wA wu ⟧C = @extΣ_G ⟦ wΓ ⟧C ⟦ wA ⟧T (⟦ wu ⟧t wA);
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
               (wt : Δ ⊢ t : A)
              (γ : dC wΓ),
        ⟦ Wtm_sb wΓ wΔ wσ wt ⟧t (WTy_sb wΓ wΔ wσ wA ) γ
        ≅ ⟦ wt ⟧t wA (⟦ wσ ⟧S wΓ wΔ γ);

    dTm_vstar : forall (γ : ⟦ w_astar ⟧C), ⟦ w_vstar ⟧V (w_star w_astar) γ ≅ γ;
    dTm_v1 : forall Γ A u (wΓ : WC Γ) (wA : Γ ⊢ A) (wu : Γ ⊢ u : A)
               (wAe : ext Γ A u ⊢ wkT A)
               (γ : ⟦ w_ext wΓ wA wu ⟧C)
               (γ2 : ⟦ wΓ ⟧C) (sa : ⟦ wA ⟧T γ2)
               (sf : hom sa (⟦ wu ⟧t wA γ2)),
        γ ≅ (((γ2 ,Σ sa) ,Σ sf) : extΣ_G  _) ->
        ⟦ w_v1 wu ⟧V wAe γ ≅ sa;
    dTm_v0 : forall Γ A u (wΓ : WC Γ) (wA : Γ ⊢ A) (wu : Γ ⊢ u : A)
               (wAe : ext Γ A u ⊢ wkT A)(wue : ext Γ A u ⊢ wkt u : wkT A)
               (γ : ⟦ w_ext wΓ wA wu ⟧C)
               (γ2 : ⟦ wΓ ⟧C) (sa : ⟦ wA ⟧T γ2)
               (sf : hom sa (⟦ wu ⟧t wA γ2)),
        γ ≅ (((γ2 ,Σ sa) ,Σ sf) : extΣ_G  _) ->
        ⟦ w_v0 wu ⟧V (w_ar wAe (w_va (w_v1 wu)) wue) γ ≅ sf;
    dTm_vwk : forall Γ A u B x (wΓ : WC Γ) (wA : Γ ⊢ A) (wu : Γ ⊢ u : A)
                (wB : Γ ⊢ B)
                (wBe : ext Γ A u ⊢ wkT B)
                (wx : WVar Γ B x)
               (γ : ⟦ w_ext wΓ wA wu ⟧C)
               (γ2 : ⟦ wΓ ⟧C) (sa : ⟦ wA ⟧T γ2)
               (sf : hom sa (⟦ wu ⟧t wA γ2)),
        γ ≅ (((γ2 ,Σ sa) ,Σ sf) : extΣ_G  _) ->
        ⟦ w_vwk wx wu ⟧V wBe γ ≅ ⟦ wx ⟧V wB γ2;

    dS_to_star : forall Γ t (wΓ : WC Γ) (wt : Γ ⊢ t : star) (γ : ⟦ wΓ ⟧C),
                   ⟦ w_to_star wt ⟧S _ w_astar γ ≅ ⟦ wt ⟧t (w_star wΓ) γ;

    dS_to_ext :forall Δ Γ A u σ a f (wΓ : WC Γ) (wA : Γ ⊢ A) (wu : Γ ⊢ u : A)
                 (wAσ : Δ ⊢ A.[σ]T) (wuσ : Δ ⊢ u.[σ]t : A.[σ]T)
                 (wΔ : WC Δ) (wσ  : Δ ⊢ σ ⇒ Γ)
                 (wa : Δ ⊢ a : A.[σ]T)
                 (wf : Δ ⊢ f.[σ]t : ar A.[σ]T a u.[σ]t)
                 (γ : ⟦ wΔ ⟧C)
                 (sa : ⟦ wA ⟧T (⟦ wσ ⟧S wΔ wΓ γ ))
                 (suσ : forall γ, ⟦ wA ⟧T (⟦ wσ ⟧S wΔ wΓ γ ))
                 (sf : hom sa _)
      , sa ≅ ⟦ wa ⟧t wAσ γ ->
        suσ γ ≅ ⟦ wu ⟧t wA (⟦ wσ ⟧S wΔ wΓ γ ) ->
        sf ≅ ⟦ wf ⟧t (w_ar  wAσ wa wuσ) γ ->
        ⟦ w_to_ext wσ wA wu wa wf ⟧S wΔ (w_ext wΓ wA wu) γ ≅
                                   (* (( *)
                                       ((((⟦ wσ ⟧S wΔ wΓ γ ,Σ sa) : sigT ⟦ wA ⟧T) 
                                        ,Σ sf) : 
          { x : sigT ⟦wA⟧T &  hom x..2 (⟦ wu ⟧t wA x..1) })

                                
    }.

(*
    


-- needed

-- définitionnel
    ⟦_⟧S-β1  : ∀{Γ}{γ : ⟦ Γ ⟧C} 
             → ⟦ • ⟧S γ ≡ coerce ⟦_⟧C-β1 tt

    ⟦_⟧S-β2  : ∀{Γ Δ}{A : Ty Δ}{δ : Γ ⇒ Δ}{γ : ⟦ Γ ⟧C}
             {a : Tm (A [ δ ]T)} → ((⟦ δ , a ⟧S )γ )
             ≡ coerce (⟦_⟧C-β2) ((⟦ δ ⟧S γ) ,,
             subst ∣_∣ (semSb-T A δ γ) (⟦ a ⟧tm γ))
             -- needed
(* inutile car déjà compris dans sb non ? *)
    semWk-T  : ∀ {Γ A B}(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)
             → ⟦ A +T B ⟧T (coerce ⟦_⟧C-β2 (γ ,, v)) ≡ 
             ⟦ A ⟧T γ
  

    semWk-S  : ∀ {Γ Δ B}{γ : ⟦ Γ ⟧C}{v : ∣ ⟦ B ⟧T γ ∣}
             → (δ : Γ ⇒ Δ) → ⟦ δ +S B ⟧S 
             (coerce ⟦_⟧C-β2 (γ ,, v)) ≡ ⟦ δ ⟧S γ

-- needed
    semWk-tm : ∀ {Γ A B}(γ : ⟦ Γ ⟧C)(v : ∣ ⟦ B ⟧T γ ∣)
             → (a : Tm A) → subst ∣_∣ (semWk-T γ v) 
               (⟦ a +tm B ⟧tm (coerce ⟦_⟧C-β2 (γ ,, v))) 
                 ≡ (⟦ a ⟧tm γ)
(* intuile *)
    ⟦coh⟧  : ∀{Θ} → isContr Θ → (A : Ty Θ) 
→ (θ : ⟦ Θ ⟧C) → ∣ ⟦ A ⟧T θ ∣
*)

(*
Lemma ar_aux T (fibT : Fib T) Γ A t u (wΓ : WC Γ) (wA : Γ ⊢ A) (wt :Γ⊢ t : A) (wu :Γ⊢ u : A)
     (semt : rft fibT wΓ wA wt) (semt0 : rft fibT wΓ wA wu) (semT : rfT fibT wΓ wA)
    (semC : rfC fibT wΓ) :
  (t_t (ft_t semt)
     (transport
        (eqf_CC_TC semC
           {|
           fT_C := ft_C semt;
           fT_T := r_rl_ar (ft_t semt)
                     (transport2 (eqf_tC_tC semt0 semt) (eqf_tT_tT semt0 semt) (ft_t semt0));
           fT_r := rl_ar (rl_t_C (ft_r semt)) (ft_rT semt) (ft_r semt)
                     (transport
                        (pt_eq (eqf_tC_tC semt0 semt) (eqf_tT_tT semt0 semt)
                           (untypeduippackrl.JMeq_sym
                              (JMeq_transport2 (eqf_tC_tC semt0 semt) (eqf_tT_tT semt0 semt)
                                 (ft_t semt0)))) (ft_r semt0)) |}) γ) =h
   t_t (transport2 (eqf_tC_tC semt0 semt) (eqf_tT_tT semt0 semt) (ft_t semt0))
     (transport
        (eqf_CC_TC semC
           {|
           fT_C := ft_C semt;
           fT_T := r_rl_ar (ft_t semt)
                     (transport2 (eqf_tC_tC semt0 semt) (eqf_tT_tT semt0 semt) (ft_t semt0));
           fT_r := rl_ar (rl_t_C (ft_r semt)) (ft_rT semt) (ft_r semt)
                     (transport
                        (pt_eq (eqf_tC_tC semt0 semt) (eqf_tT_tT semt0 semt)
                           (untypeduippackrl.JMeq_sym
                              (JMeq_transport2 (eqf_tC_tC semt0 semt) (eqf_tT_tT semt0 semt)
                                 (ft_t semt0)))) (ft_r semt0)) |}) γ)) =
  (t_t (transport2 (eqf_tC_TC semT semt) (eqf_tT_TT semT semt) (ft_t semt))
     (transport (eqf_CC_TC semC semT) γ) =h
   t_t (transport2 (eqf_tC_TC semT semt0) (eqf_tT_TT semT semt0) (ft_t semt0))
     (transport (eqf_CC_TC semC semT) γ)).
*)

    Ltac clear_rc :=
      match goal with
        | x : rC ?U, x' : rC ?U |- _  =>
          have e : x = x' by apply:rl_hpC;
          (eassumption || (apply:rl_t_Cη;eassumption) ||(apply:rl_T_Cη; eassumption))
        | x : rT ?U, x' : rT ?U |- _  =>
          have e : x = x' by apply:π_eq_pTη;apply:rl_hpT; 
          (eassumption || (apply:rl_t_Tη;eassumption) ||(apply:rl_V_Tη; eassumption))
        | x : rtm ?U, x' : rtm ?U |- _  =>
          have e : x = x' by apply:π_eq_ptη;apply:rl_hpt; eassumption
        | x : rS ?U ?V, x' : rS ?U ?V |- _  =>
          have e : x = x' by apply:π_eq_pSη;apply:rl_hpS; eassumption
      end.
      (* destruct H. *)
      (* clear. *)
        (* move: x  y e. *)
        (* move:(sigT _). *)
        (* move:(sigT _). *)
        (* move:(sigT _). *)
        (* move:(sigT _). *)
        (* destruct 1. *)
    (*
      have e' : {a : {x : A & P x} & Q a} = {a : {x : A' & P' x} & Q' a}.
      {
        move: x  y e.
        move:(sigT _).
        move:(sigT _).
        by destruct 1.

        }
      have h : y..1..2 ≅ (eq_rect _ (fun _ => _) y _ e')..1..2.
      {
        clear e.
        move:e' y.
        move:(sigT _).
        move:(sigT _).
        move:(sigT _).
        intros.
        destruct e'.
        move:sigT.
        move:sigT.
        move:sigT.
        }
      apply:JMeq_trans; last first.
      apply:JMeq_congr.
      apply:JMeq
      destruct e.
    Qed.
*)
Ltac clear_jmsigma' :=
  match goal with
  | x : (?C ,Σ ?D) = (_ ,Σ ?E) |- _ =>
     (apply JM_projT2,JMeq_eq in x; simpl in x)
    (* have {x} x : D = E by apply : JMeq_eq;apply:(JM_projT2  x) *)
  | x : ?C = ?C |- _ => clear x
  end.
Lemma type_is_omega (T : Type) (fibT : Fib T) : isOmegaGroupoid (G_of_T T) (typDecl fibT).
  constructor.
  - reflexivity.
  - move => Γ A u wΓ wA wu.
    cbn -[semt semT semC].
    move:(semC _ _) => fΓe.
    move:(semC _ _) => fΓ.
    move:(semT _ _ _) => fA.
    move:(semt _ _ _ _) => fu.
    move/fC_r:(fΓe).
    inversion 1.
    subst.
    repeat clear_hprop; repeat (clear_jmsigma; subst).
    
    rewrite /extΣ_G /=.
    destruct fu,fΓ,fA => /=.
    repeat (clear_rc; subst).
    repeat (erewrite (uip _ erefl);cbn).
    reflexivity.
  - move => Γ wΓ .
    cbn -[semt semT semC].
    move:(semC _ _ ) => fΓ.
    move:(semT _ _ _) => fstar.
    move/fT_r:(fstar).
    inversion 1; subst; repeat clear_hprop; repeat (clear_jmsigma; subst).
    move => γ.
    destruct fΓ,fstar; simpl in *.
    repeat (clear_rc; subst).
    reflexivity.
  - move => Γ A t u wΓ wA wt wu .
    cbn -[semt semT semC].
    move:(semC _ _) => fΓ.
    move:(semT _ _ _) => far.
    move:(semT _ _ _) => fA.
    move:(semt _ _ _ _) => ft.
    move:(semt _ _ _ _) => fu.
    move => γ.
    move/fT_r:(far).
    inversion 1; subst; repeat clear_hprop; repeat (clear_jmsigma; subst).
    destruct fΓ,far,fA,ft,fu; simpl in *; repeat (clear_rc; subst).
    repeat (erewrite (uip _ erefl);cbn).
    reflexivity.
  - intros.
    move:γ .
    cbn -[semt semT semC].
    move:(semC _ _) => fΓ.
    move:(semC _ _) => fΔ.
    move:(semT _ _ _) => fAσ.
    move:(semT _ _ _) => fA.
    move:(semt _ _ _ _) => ftσ.
    move:(semt _ _ _ _) => ft.
    move:(semS _ _ _ _) => fσ.
    destruct fAσ,fA,ftσ,ft,fσ ; simpl in *.
    repeat (move:(e in transport e) => /= e; (destruct e || subst) => /=).
    repeat (move:(e in transport2 e) => /= e; (destruct e || subst) => /=).
    repeat (
      move:(e in JMeq_eq e) => /= e; have e' := JMeq_eq e ; destruct e';
      repeat (erewrite (uip _ erefl);cbn);
      clear e).

    have h:ft_T = r_sbT fS_S ft_T0.
    {
      apply:π_eq_pTη.
      apply:rl_hpT; try eassumption.
      (apply:tp_rT1; first by reflexivity); last first.
      apply:rl_sbT.
      eassumption.
      eassumption.
      reflexivity.
      }
    subst.
    have h:ft_t = r_sbt fS_S ft_t0.
    {
      apply:π_eq_ptη.
      apply:rl_hpt; try eassumption.
      (apply:tp_rTm1; first by reflexivity); last first.
      apply:rl_sbt.
      exact:ft_r0.
      eassumption.
      reflexivity.
      }
    now subst.
  - cbn -[semt semT semC].
    move:(semC _ _) => fastar.
    move:(semT _ _ _) => fstar.
    move:(semt _ _ _ _) => fvstar.
    move/(ft_r):(fvstar).
    inversion 1; subst; repeat clear_hprop; repeat (clear_jmsigma; subst).
    inversion X; subst; repeat clear_hprop; repeat (clear_jmsigma; subst).
    destruct fstar,fastar,fvstar; simpl in *.
    move => γ.
     repeat (clear_rc; subst).
    simpl in *.
    (* TODO : adapter clear_jmsigma avec ça*)
    repeat (apply JM_projT2,JMeq_eq in H0; simpl in H0).
    subst.
    repeat (apply JM_projT2,JMeq_eq in H1; simpl in H1).
    subst.
    repeat (erewrite (uip _ erefl);cbn).
    set e := (e in transport e).
    exact (JMeq_transport γ e).
  - move => Γ A u wΓ wA wu wAe.
    cbn -[semT semC semt] in *.
    move:(semC _ _) => fΓe.
    move:(semC _ _) => fΓ.
    move:(semT _ _ _) => fA.
    move:(semT _ _ _) => fAe.
    move:(semt _ _ _ _) => fu.
    move:(semt _ _ _ _) => fv1.
    move/(ft_r):(fv1) => I.
    inversion I; subst; repeat clear_hprop; repeat (clear_jmsigma; subst).
    inversion X; subst; repeat clear_hprop; repeat (clear_jmsigma; subst).
    destruct fΓe,fΓ,fA,fAe,fv1,fu; simpl in *.
    repeat (clear_rc; subst).
    cbn.
    intros.
    cbn.
    repeat (erewrite (uip _ erefl);cbn).
    move:(eqf_tC_TC _ _) => /= e.
    move:(eqf_tT_TT _ _) => /= e'.
    destruct e.
    cbn.
    move:(JMeq_eq _).
    have e'' := JMeq_eq e'.
    subst.
    move => h.
    move:sa sf H.
    repeat (erewrite (uip _ erefl);cbn).
    intros.
    have H' := JMeq_eq H.
    cbn.
    subst.
    clear H'.
     repeat (apply JM_projT2,JMeq_eq in H10; simpl in H10).
     repeat clear_hprop; repeat (clear_jmsigma; subst).
     constructor.
  - move => Γ A u wΓ wA wu wAe wue.
    cbn -[semT semC semt semS].
    move :(semC _ _) => fΓe.
    move :(semC _ _) => fΓ.
    move :(semT _ _ _) => fA.
    move :(semT _ _ _) => fAe.
    move :(semt _ _ _ _) => fu.
    move :(semt _ _ _ _) => fv0.
    move/(ft_r):(fv0) => I.
    inversion I; subst; repeat clear_hprop; repeat (clear_jmsigma; subst).
    inversion X; subst; repeat clear_hprop; repeat (clear_jmsigma; subst).
    destruct fΓe,fΓ,fA,fAe,fv0,fu; simpl in *.
    repeat (clear_rc; subst).
    cbn.
    intros.
    cbn.
    repeat (erewrite (uip _ erefl);cbn).
    move:(eqf_tC_TC _ _) => /= e.
    move:(eqf_tT_TT _ _) => /= e'.
    destruct e.
    cbn.
    move:(JMeq_eq _).
    have e'' := JMeq_eq e'.
    subst.
    move => h.
    move:sa sf H.
    repeat (erewrite (uip _ erefl);cbn).
    intros.
    have H' := JMeq_eq H.
    cbn.
    subst.
    clear H'.
     repeat (apply JM_projT2,JMeq_eq in H10; simpl in H10).
     repeat clear_hprop; repeat (clear_jmsigma; subst).
     constructor.
  - move =>  Γ A u B x wΓ wA wu wB wBe wx.
    cbn -[semT semC semt semS].
    move :(semC _ _) => fΓe.
    move :(semC _ _) => fΓ.
    move :(semT _ _ _) => fA.
    move :(semT _ _ _) => fBe.
    move :(semT _ _ _) => fB.
    move :(semt _ _ _ _) => fu.
    move :(semt _ _ _ _) => fvwk.
    move :(semt _ _ _ _) => fx.
    move/(ft_r):(fvwk) => I.
    inversion I; subst; repeat clear_hprop; repeat (clear_jmsigma; subst).
    inversion X; subst; repeat clear_hprop; repeat (clear_jmsigma; subst).
    destruct fΓe,fΓ,fA,fBe,fB, fx,fvwk,fu; simpl in *.
    subst.
    repeat (clear_jmsigma'; subst).
    repeat (clear_rc; subst).
    repeat (erewrite (uip _ erefl);cbn).
    move:(eqf_tC_TC _ _) => /= e.
    destruct e => /=.
    move:(eqf_tT_TT _ _) => /= e.
    have e' := JMeq_eq e.
    destruct e'.
    repeat (erewrite (uip _ erefl);cbn).
    intros.
    have e' := JMeq_eq H.
    rewrite e' /=.
    apply:JMeq_from_eq.
    f_equal.
    apply:π_eq_ptη.
    apply:rl_hpt; try eassumption.
    constructor.
    assumption.
  - move => Γ t wΓ wt.
    cbn -[semT semC semt semS].
    move :(semC _ _) => fΓ.
    move :(semC _ _) => fast.
    move :(semT _ _ _) => fst.
    move :(semt _ _ _ _) => ft.
    move :(semS _ _ _ _) => ftost.
    move/(fS_r):(ftost) => I.
    inversion I; subst; repeat clear_hprop; repeat (clear_jmsigma'; subst).
    destruct fΓ,fast,fst,ft,ftost;  simpl in *.
    subst.
    repeat (clear_jmsigma'; subst).
    repeat (clear_rc; subst).
    repeat (erewrite (uip _ erefl);cbn).
    move:( eqf_SC2_CC _ _) => /= e.
    subst.
    repeat (erewrite (uip _ erefl);cbn).
    move => γ.
    have e : ft_T = r_rl_star fibT .
    {
      apply:π_eq_pTη.
    apply:rl_hpT; try eassumption.
    by constructor.
      }
    subst.
    apply:JMeq_from_eq.
    f_equal.
    apply:π_eq_ptη.
    apply:rl_hpt; try eassumption.
  - move => Δ Γ A u σ a f 
             wΓ wA wu wAσ wuσ wΔ wσ wa wf .
    cbn -[semT semC semt semS].
    move :(semC _ _) => fΔ.
    move :(semC _ _) => fΓ.
    move :(semC _ _) => fΓe.
    move :(semT _ _ _) => fA.
    move :(semT _ _ _) => fAσ.
    move :(semT _ _ _) => far.
    move :(semt _ _ _ _) => fu.
    move :(semt _ _ _ _) => fa.
    move :(semt _ _ _ _) => ff.
    move :(semS _ _ _  _) => fσ.
    move :(semS _ _ _  _) => fσe.
    move/(fS_r):(fσe) => I.
    (* why sσ is not rl ? *)
    remember (mkpS (fS_S fσe)) as fσe' eqn:efσ'.
    inversion I; subst; repeat clear_hprop; repeat (clear_jmsigma'; subst).
    destruct fΔ,fΓ,fΓe, fA,fAσ,far,fu,fa,ff,fσ,fσe;  simpl in *.
    (* c'es tplus propre de faire comme ça que de bourriner 
        avec clear_rc et et d'utiliser uip ensuite
     *)
    repeat (move:(e in transport e) => /= ?; subst => /=;
    repeat (clear_jmsigma'; subst)).
    repeat (move:(e in transport2 e) => /= ?; subst => /=;
    repeat (clear_jmsigma'; subst)).
    repeat (move:(e in JMeq_from_eq e) => /= ?;
    subst => /=; repeat (erewrite (uip _ erefl);cbn)).
    repeat (
    move:(e in JMeq_eq e) => /= e; have e' := JMeq_eq e ; destruct e';
    repeat (erewrite (uip _ erefl);cbn);
    clear e).
    case:H0 => ? ?;subst.
    intro h.
    repeat (clear_jmsigma'; subst).
    move => γ sa' suσ sf'.
    repeat (clear_rc; subst).
    (* ft_T1 *)
    inversion fT_r1.
    subst; repeat clear_hprop; repeat (clear_jmsigma'; subst).
    repeat (clear_rc; subst).
    (* move => ee; have ee' := JMeq_eq ee. *)
    (* h *)
    (* move/(@JMeq_eq _ _ _) => e. *)
    have h:sA0 = r_sbT sσ ft_T.
    {
      apply:π_eq_pTη.
      apply:rl_hpT; try eassumption.
      (apply:tp_rT1; first by reflexivity); last first.
      apply:rl_sbT.
      exact:X1.
      eassumption.
      reflexivity.
      }
    subst.
    have h:su0 = r_sbt sσ ft_t.
    {
      apply:π_eq_ptη.
      apply:rl_hpt; try eassumption.
      (apply:tp_rTm1; first by reflexivity); last first.
      apply:rl_sbt.
      exact:X2.
      eassumption.
      reflexivity.
      }
    subst.
    move/(@JMeq_eq _ _ _) => e.
    subst.
    move/(@JMeq_eq _ _ _) => e.
    move/(@JMeq_eq _ _ _) => ee.
    subst.
    cbn.
    simpl in *.
      try (match goal with
        | x : rtm ?U, x' : rtm ?U |- _  => 
          have e : x = x' by apply:π_eq_ptη;apply:rl_hpt; eassumption
      end).
      (* TODO : comprendre pourquoi clear_rc ne marche pas *)
      have ea : sa = ft_t0 by apply:π_eq_ptη; apply:rl_hpt; eassumption.
      subst.
      (* TODO : comprendre pourquoi clear_rc ne marche pas *)
      apply:JMeq_from_eq.
      f_equal.
      f_equal.
      apply:π_eq_ptη.
      apply:rl_hpt;eassumption.
Qed.
