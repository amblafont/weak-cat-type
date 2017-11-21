
(* -*- coq-prog-name: "coqtop"; -*- *)
Require Import ssreflect ssrfun ssrbool .

Require Import Coq.Logic.JMeq.
From Modules Require Import libhomot lib brunerietype untypeduippackrl.
Set Bullet Behavior "Strict Subproofs".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TypeRl.
  Variable (T: Type).
  Variable (fibT: Fib T).

Record rfC (Γ : Con) (wΓ : WC Γ) :=
  { fC_C : rC T ;
    fC_r : rl_C fibT wΓ fC_C
  }.

Record rfT (Γ : Con) (A : Ty) (wΓ : WC Γ) (wA : (Γ ⊢ A)) :=
  { fT_C : rC T;
    fT_T : rT fT_C;
    fT_r : rl_T fibT wΓ wA (mkpT fT_T)
  }.

Record rft (Γ : Con) (A : Ty) (t : Tm) (wΓ : WC Γ) (wA : (Γ ⊢ A)) (wt : Γ ⊢ t : A) :=
  { ft_C : rC T;
    ft_T : rT ft_C;
    ft_t : rtm ft_T;
    ft_r :  rl_t fibT wΓ wA wt (mkpt ft_t );
    (* ft_rT :  rl_T fibT wΓ wA (mkpT ft_T)  *)
  }.
Definition ft_rT (Γ : Con) (A : Ty) (t : Tm) (wΓ : WC Γ) (wA : (Γ ⊢ A)) (wt : Γ ⊢ t : A)
      (ft : rft wΓ wA wt) : rl_T fibT wΓ wA (mkpT (ft_T ft)) := rl_t_Tη (ft_r ft).

Record rfV (Γ : Con) (A : Ty) (x : Var) (wΓ : WC Γ) (wA : (Γ ⊢ A)) (wx : WVar Γ A x) :=
  { fV_C : rC T;
    fV_T : rT fV_C;
    fV_t : rtm fV_T;
    fV_r :  rl_V fibT wΓ wA wx (mkpt fV_t );
    (* fV_rT :  rl_T fibT wΓ wA (mkpT fV_T) ; *)
    (* fV_rC T :  rl_C fibT wΓ fV_C  *)
  }.
Definition fV_rT (Γ : Con) (A : Ty) (x:Var) (wΓ : WC Γ) (wA : (Γ ⊢ A)) ( wx : WVar Γ A x)
      (fx : rfV wΓ wA wx) : rl_T fibT wΓ wA (mkpT (fV_T fx)) := rl_V_Tη (fV_r fx).
Definition fV_rC  (Γ : Con) (A : Ty) (x:Var) (wΓ : WC Γ) (wA : (Γ ⊢ A)) ( wx : WVar Γ A x)
      (fx : rfV wΓ wA wx) : rl_C fibT wΓ  ((fV_C fx)) := rl_V_Cη (fV_r fx).

Record rfS (Γ Δ : Con) (σ : sub) (wΓ : WC Γ) (wΔ : WC Δ) (wσ : Γ ⊢ σ ⇒ Δ) :=
  { fS_Γ : rC T;
    fS_Δ : rC T;
    fS_S : rS fS_Γ fS_Δ;
    fS_r : rl_S fibT wΓ wΔ wσ (mkpS fS_S)}.


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
  Lemma eqf_SC1_CC (Γ : Con)  (wΓ : WC Γ) 
        (Δ : Con) (wΔ : WC Δ) (σ : sub) (wσ : Γ ⊢ σ ⇒ Δ)
        (fΓ : rfC wΓ)(fσ : rfS wΓ wΔ wσ) :
    fS_Γ fσ = fC_C fΓ.
  Proof.
    apply:rl_hpC.
    + apply:(rl_S_C1 (pσ := mkpS (fS_S fσ))).
      apply:fS_r.
    + apply:fC_r.
  Qed.
  Lemma eqf_SC2_CC (Γ : Con)  (wΓ : WC Γ) 
        (Δ : Con) (wΔ : WC Δ) (σ : sub) (wσ : Γ ⊢ σ ⇒ Δ)
        (fΔ : rfC wΔ)(fσ : rfS wΓ wΔ wσ) :
    fS_Δ fσ = fC_C fΔ.
  Proof.
    apply:rl_hpC.
    + apply:(rl_S_C2 (pσ := mkpS (fS_S fσ))).
      apply:fS_r.
    + apply:fC_r.
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
    * apply :r_rl_astar => //.
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
    unshelve econstructor.
    * exact (fC_C semC).
    * apply:r_rl_star=> //.
    * abstract(clear_hprop; by move/rl_star:(fC_r semC)).
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
      -- assert (h' : rl_T fibT w w0 (mkpT (eq_rect _ (@rT T) (fT_T IHA) _ e))).
         { move: (fT_r IHA).
           apply:transport.
           move:(fT_T IHA).
           pattern (fT_C IHA),e.
           by apply:J.
         }
         exact:h'.
      -- apply:(rl_S_C2 (fS_r semS)).
      -- apply:(rl_S_C1 (fS_r semS)).
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
    have rAu : rl_T fibT wΓ' wA {| pT_C := fV_C IHx; pT_T :=
                                                       eq_rect_r (@rT T) (ft_T IHu) eΓ |}.
    {
      move:(ft_rT IHu).
      apply:transport.
      move:(ft_T IHu).
      pattern (ft_C IHu),eΓ.
        by apply:J_r.
    }
    have ru' :
      rl_t fibT wΓ' wA wu
           {|
             pt_C := fV_C IHx;
             pt_T := eq_rect_r (@rT T) (ft_T IHu) eΓ;
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
      cbn.
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
    (* have r :  rl_C fibT wΓ' (ft_C IHu) *)

    econstructor.
    * constructor; last by apply:ru.
      -- exact:(rl_t_C ru).
      -- exact:(ft_rT IHu).
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
    (* have r :  rl_C fibT wΓ' (ft_C IHu) *)

    econstructor.
    * apply:rl_v0 ; last by apply:ru.
      -- exact:(rl_t_C ru).
      -- exact:(ft_rT IHu).
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
    have ft_rT2 := rl_t_Tη ft_r2.
    have ft_rT1 := rl_t_Tη ft_r1.
    have e :   fT_T0  = ft_T0.
    { apply:π_eq_pTη; apply:rl_hpT.
      - eassumption.
      - apply:rl_t_Tη.
        eassumption.
    }
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
            **  eassumption.
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
    assumption.
Defined.


End TypeRl.
