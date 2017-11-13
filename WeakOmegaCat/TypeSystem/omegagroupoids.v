(* -*- coq-prog-name: "coqtop"; -*- *)
(* From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq. *)
Require Import ssreflect ssrfun ssrbool .

Require Import libhomot.
Require Import untypeduippackrl.
Set Bullet Behavior "Strict Subproofs".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Coq.Logic.JMeq.

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
  Lemma eqf_SC1_CC (Γ : Con)  (wΓ : WC Γ) 
        (Δ : Con) (wΔ : WC Δ) (σ : sub) (wσ : Γ ⊢ σ ⇒ Δ)
        (fΓ : rfC fibT wΓ)(fσ : rfS fibT wΓ wΔ wσ) :
    fS_Γ fσ = fC_C fΓ.
  Proof.
    apply:rl_hpC.
    + apply:(rl_S_C1 (pσ := mkpS (fS_S fσ))).
      apply:fS_r.
    + apply:fC_r.
  Qed.
  Lemma eqf_SC2_CC (Γ : Con)  (wΓ : WC Γ) 
        (Δ : Con) (wΔ : WC Δ) (σ : sub) (wσ : Γ ⊢ σ ⇒ Δ)
        (fΔ : rfC fibT wΔ)(fσ : rfS fibT wΓ wΔ wσ) :
    fS_Δ fσ = fC_C fΔ.
  Proof.
    apply:rl_hpC.
    + apply:(rl_S_C2 (pσ := mkpS (fS_S fσ))).
      apply:fS_r.
    + apply:fC_r.
  Qed.
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

Require Import Coq.Logic.JMeq.
Notation "x ..1" := (projT1 x) (at level 2).
Notation "x ..2" := (projT2 x) (at level 2).
Notation "x ,Σ y" := (existT _ x y)  (at level 70).
Notation "x ≅ y" := (JMeq  x  y) (at level 70, y at next level, no associativity).

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

Lemma JMeq_eqh (A B : Type) (x y : A) (x' y':B) (e : A = B) (ex : x ≅ x')
      (ey: y ≅ y') : (x =h y) = (x' =h y').
  destruct e.
  apply JMeq_eq in ex.
  apply JMeq_eq in ey.
  by destruct ex, ey.
Qed.
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
          have e : x = x' by apply:π_eq_pTη;apply:rl_hpT; eassumption
      end.
Lemma type_is_omega (T : Type) (fibT : Fib T) : isOmegaGroupoid (G_of_T T) (typDecl fibT).
  constructor.
  - reflexivity.
  - move => Γ A u wΓ wA wu.
    cbn -[semt semT semC].
    unfold semC; exfalso.
    cbn iota.
    (* rewrite -/(@semt T fibT Γ A u wΓ wA wu). *)
    (* cbn et simpl font n'importe quoi, je suis obligé de replier semt après *)
    change (
  {γ : {a : C_TY (ft_C (semt fibT wΓ wA wu)) & T_TY (ft_T (semt fibT wΓ wA wu)) a} &
  γ ..2 =h t_t (ft_t (semt fibT wΓ wA wu)) γ ..1} =
  {δ
  : {γ : C_TY (fC_C (semC fibT wΓ)) &
    T_TY (fT_T (semT fibT wΓ wA)) (transport (eqf_CC_TC (semC fibT wΓ) (semT fibT wΓ wA)) γ)} &
  δ ..2 =h
  t_t
    (transport2 (eqf_tC_TC (semT fibT wΓ wA) (semt fibT wΓ wA wu))
       (eqf_tT_TT (semT fibT wΓ wA) (semt fibT wΓ wA wu)) (ft_t (semt fibT wΓ wA wu)))
    (transport (eqf_CC_TC (semC fibT wΓ) (semT fibT wΓ wA)) δ ..1)}
        ).
    set st := semt _ _ _ _.
    set sC := semC _ _.
    set sA := semT _ _ _.
    clearbody st  sC sA.
    destruct st,sC,sA => /=.
    have e :   ft_C = fC_C.
    {
      apply:rl_hpC.
      * apply:rl_t_Cη; eassumption.
      * apply:fC_r.
    }
    subst.
    have e :   fT_C = fC_C.
    {
      apply:rl_hpC.
      * apply:rl_T_Cη; eassumption.
      * apply:fC_r.
    }
    subst.
    have eqT : ft_T = fT_T.
    {
      apply:π_eq_pTη.
      apply:rl_hpT.
      - eassumption.
      - eassumption.
    }
    subst.
    simpl.
    set e := eqf_CC_TC _ _.
    have ->  : e = erefl by apply uip.
    clear e.
    cbn.
    f_equal.
    set e := eqf_tC_TC _ _.
    have -> : e = erefl by apply uip.
    clear e.
    simpl.
    set e := JMeq_eq _.
    have -> : e = erefl by apply:uip.
    reflexivity.
  - move => Γ wΓ γ.
    simpl.
    f_equal.
    change (
  T_TY
    (fT_T
       (match WC_hp wΓ wΓ in (_ = y) return (rfC fibT y -> rfT fibT wΓ (w_star y)) with
        | erefl  =>
            fun semC : rfC fibT wΓ =>
            {| fT_C := fC_C semC; fT_T := r_rl_star fibT; fT_r := rl_star (fC_r semC) |}
        end (semC fibT wΓ)))
    (transport
       (eqf_CC_TC (semC fibT wΓ)
          (match WC_hp wΓ wΓ in (_ = y) return (rfC fibT y -> rfT fibT wΓ (w_star y)) with
           | erefl  =>
               fun semC : rfC fibT wΓ =>
               {| fT_C := fC_C semC; fT_T := r_rl_star fibT; fT_r := rl_star (fC_r semC) |}
           end (semC fibT wΓ))) γ) = T
        ).
    (* simpl. *)
    (* rewrite/semT. *)
    (* simpl. *)
    (* rewrite -/(semC _ _). *)
    rewrite (uip (WC_hp _ _) erefl).
    set e := (e in transport e).
    simpl in e.
    rewrite (uip e erefl) //=.
  - move => Γ A t u wΓ wA wt wu γ.
    f_equal.
    change (
  G_of_T
    (t_t (ft_t (semt fibT wΓ wA wt))
       (transport (eqf_CC_TC (semC fibT wΓ) (semT fibT wΓ (w_ar wA wt wu))) γ) =h
     t_t
       (transport2 (eqf_tC_tC (semt fibT wΓ wA wu) (semt fibT wΓ wA wt))
          (eqf_tT_tT (semt fibT wΓ wA wu) (semt fibT wΓ wA wt)) (ft_t (semt fibT wΓ wA wu)))
       (transport (eqf_CC_TC (semC fibT wΓ) (semT fibT wΓ (w_ar wA wt wu))) γ)) =
  G_of_T
    (t_t
       (transport2 (eqf_tC_TC (semT fibT wΓ wA) (semt fibT wΓ wA wt))
          (eqf_tT_TT (semT fibT wΓ wA) (semt fibT wΓ wA wt)) (ft_t (semt fibT wΓ wA wt)))
       (transport (eqf_CC_TC (semC fibT wΓ) (semT fibT wΓ wA)) γ) =h
     t_t
       (transport2 (eqf_tC_TC (semT fibT wΓ wA) (semt fibT wΓ wA wu))
          (eqf_tT_TT (semT fibT wΓ wA) (semt fibT wΓ wA wu)) (ft_t (semt fibT wΓ wA wu)))
       (transport (eqf_CC_TC (semC fibT wΓ) (semT fibT wΓ wA)) γ))
        ).
    (* simpl déplie tro p !!! *)
    (*
    simpl.
    rewrite -/(@semt _ fibT  Γ A u wΓ wA wu).
    rewrite -/(@semt _ fibT  Γ A t wΓ wA wt).
*)
   change (G_of_T (
  (t_t (ft_t (semt fibT wΓ wA wt))
     (transport
        (eqf_CC_TC (semC fibT wΓ)
           {|
           fT_C := ft_C (semt fibT wΓ wA wt);
           fT_T := r_rl_ar (ft_t (semt fibT wΓ wA wt))
                     (transport2 (eqf_tC_tC (semt fibT wΓ wA wu) (semt fibT wΓ wA wt))
                        (eqf_tT_tT (semt fibT wΓ wA wu) (semt fibT wΓ wA wt))
                        (ft_t (semt fibT wΓ wA wu)));
           fT_r := rl_ar (rl_t_C (ft_r (semt fibT wΓ wA wt))) (ft_rT (semt fibT wΓ wA wt))
                     (ft_r (semt fibT wΓ wA wt))
                     (transport
                        (pt_eq (eqf_tC_tC (semt fibT wΓ wA wu) (semt fibT wΓ wA wt))
                           (eqf_tT_tT (semt fibT wΓ wA wu) (semt fibT wΓ wA wt))
                           (untypeduippackrl.JMeq_sym
                              (JMeq_transport2 (eqf_tC_tC (semt fibT wΓ wA wu) (semt fibT wΓ wA wt))
                                 (eqf_tT_tT (semt fibT wΓ wA wu) (semt fibT wΓ wA wt))
                                 (ft_t (semt fibT wΓ wA wu))))) (ft_r (semt fibT wΓ wA wu))) |}) γ) =h
   t_t
     (transport2 (eqf_tC_tC (semt fibT wΓ wA wu) (semt fibT wΓ wA wt))
        (eqf_tT_tT (semt fibT wΓ wA wu) (semt fibT wΓ wA wt)) (ft_t (semt fibT wΓ wA wu)))
     (transport
        (eqf_CC_TC (semC fibT wΓ)
           {|
           fT_C := ft_C (semt fibT wΓ wA wt);
           fT_T := r_rl_ar (ft_t (semt fibT wΓ wA wt))
                     (transport2 (eqf_tC_tC (semt fibT wΓ wA wu) (semt fibT wΓ wA wt))
                        (eqf_tT_tT (semt fibT wΓ wA wu) (semt fibT wΓ wA wt))
                        (ft_t (semt fibT wΓ wA wu)));
           fT_r := rl_ar (rl_t_C (ft_r (semt fibT wΓ wA wt))) (ft_rT (semt fibT wΓ wA wt))
                     (ft_r (semt fibT wΓ wA wt))
                     (transport
                        (pt_eq (eqf_tC_tC (semt fibT wΓ wA wu) (semt fibT wΓ wA wt))
                           (eqf_tT_tT (semt fibT wΓ wA wu) (semt fibT wΓ wA wt))
                           (untypeduippackrl.JMeq_sym
                              (JMeq_transport2 (eqf_tC_tC (semt fibT wΓ wA wu) (semt fibT wΓ wA wt))
                                 (eqf_tT_tT (semt fibT wΓ wA wu) (semt fibT wΓ wA wt))
                                 (ft_t (semt fibT wΓ wA wu))))) (ft_r (semt fibT wΓ wA wu))) |}) γ)))
           =
           G_of_T (
  (t_t
     (transport2 (eqf_tC_TC (semT fibT wΓ wA) (semt fibT wΓ wA wt))
        (eqf_tT_TT (semT fibT wΓ wA) (semt fibT wΓ wA wt)) (ft_t (semt fibT wΓ wA wt)))
     (transport (eqf_CC_TC (semC fibT wΓ) (semT fibT wΓ wA)) γ) =h
   t_t
     (transport2 (eqf_tC_TC (semT fibT wΓ wA) (semt fibT wΓ wA wu))
        (eqf_tT_TT (semT fibT wΓ wA) (semt fibT wΓ wA wu)) (ft_t (semt fibT wΓ wA wu)))
     (transport (eqf_CC_TC (semC fibT wΓ) (semT fibT wΓ wA)) γ))
        )).
   
    (* set (sar := (semT fibT wΓ (w_ar wA wt wu))). *)
    f_equal.
    f_equal.
    move:γ.
    simpl.
    move:(semC _ _)(semT _ _  wA)(semt _ _ _ wt) (semt _ _ _ wu) => sΓ sA st su γ.
    destruct sΓ,sA,su,st => //=.
    simpl in *.
    repeat (clear_rc; subst).
    simpl.
    rewrite [e in transport e](uip _ erefl) /=.
    repeat rewrite [e in transport2 e](uip _ erefl) /= [JMeq_eq _](uip _ erefl) /=.
    rewrite [e in transport e](uip _ erefl) /=.
    reflexivity.
  - intros.
    move:γ .
    simpl.
    move:(semC _ wΓ)(semC _ wΔ)(semT _ _ _) (semS _ _ _ _)(semt _ _ _ _).
    admit.
  - 
    simpl => γ.
    cbn.
    rewrite /ssr_have /=.
    rewrite (uip (WC_hp _ _) erefl) /=.
    rewrite (uip (WTy_hp _ _) erefl) /=.
    repeat rewrite [e in transport2 e](uip _ erefl) /= [JMeq_eq _](uip _ erefl) /=.
    rewrite [e in transport e](uip _ erefl) /=.
    reflexivity.
  - move => Γ A u wΓ wA wu wAe.
    cbn -[semT semC semt semS].
    rewrite [forall x, _]lock.
    case :(semC _ _) ; intros.
    case :(semC _ _) ; intro.
    case :(semT _ _ _);intros.
    case :(semT _ _ _);intros.
    case :(semt _ _ _ _);intros.
    case :(semt _ _ _ _);intros.
    simpl.
    repeat (clear_rc; subst).
    inversion fC_r => //=; subst.
    repeat clear_hprop; repeat (clear_jmsigma; subst).
    remember (mkpt ft_t0)  as ptt  eqn:eptt in ft_r0.
    inversion ft_r0.
    clear fC_r.
    move:ft_r.
    (* essayons d'exploiter la relation *)

Fixpoint monadd n m :=
  match n with
  | 0 => m
  | p.+1 =>  (monadd p m).+1
  end.
    lazy delta beta iota.
    have :monadd (monadd 4 _)  _=6.
    cbn delta beta iota.
    Nat.add
    cbn iota.
    Fixpoint predn n
    cbn.
    rewrite -/(semt _ _ _ _ ).
    reflexivity.
