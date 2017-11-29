Require Import ssreflect ssrfun ssrbool .

From Modules Require Import libhomot untypeduippackrl buildrlhp lib PreSyntaxOnlyContr WfSyntaxBrunerieOnlyContr gtypeext omegagroupoids.
Require Import Coq.Logic.JMeq.
Set Bullet Behavior "Strict Subproofs".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Local Notation "⟦ X ⟧V" := (dTm (w_va X)).

Section TypeDecl.
  Variable (T: Type).
  Variable (fibT: Fib T).

  Definition typDecl   : Decl.
    unshelve refine
             (
               {| dC := fun Γ (wΓ : Γ ⊢ ) => C_TY (fC_C (semC fibT wΓ));
                  dTy := fun Γ A (wΓ : Γ ⊢ ) (wA : Γ ⊢ A)
                           (γ : C_TY (fC_C (semC fibT wΓ))) =>
                           G_of_T
                             (T_TY (fT_T (semT fibT wΓ wA)) (transport _ γ));
                  dTm :=
                    fun Γ A t (wΓ : Γ ⊢ ) 
                      (wt : Γ ⊢ t : A) (wA : Γ ⊢ A) (γ : C_TY (fC_C (semC fibT wΓ))) =>
                      t_t
                        (transport2 _ _ (ft_t (semt fibT wΓ wA wt)))
                        (transport _ γ);

                  dS := fun Γ Δ σ (wσ : Γ ⊢ σ ⇒ Δ) (wΓ : Γ ⊢ ) (wΔ : Δ ⊢ ) =>
                           S (transport2 _ _ (fS_S (semS fibT wΓ wΔ wσ) )) 
                  |}
               ).
    - apply:eqf_CC_TC.
    - apply:eqf_tC_TC.
    - apply:eqf_tT_TT.
    - apply:eqf_SC1_CC.
    - apply:JMeq_from_eq.
      apply:eqf_SC2_CC.
Defined.

End TypeDecl.



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



(* TODO : utiliser cette tactique pour simplifier la preuve de sem* qui construit la fonction
vérifiant la relation fonctionelle *)
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
Ltac clear_jmsigma' := clear_jmsigma.

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