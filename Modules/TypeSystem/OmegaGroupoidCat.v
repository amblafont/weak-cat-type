
(* an omega groupoid is an omega cat *)
Require Import ssreflect ssrfun ssrbool .

From Modules Require Import libhomot untypeduippackrl TypesAreOmegaGroupoids.FunctionalRelation lib PreSyntaxOnlyContr WfSyntaxBrunerieOnlyContr gtypeext omegagroupoids omegacategories.
Require Import Coq.Logic.JMeq.
Set Bullet Behavior "Strict Subproofs".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation "⟦ X ⟧V" := (dTm (w_va X)).

Local Notation SB := (WfSyntaxBrunerieOnlyContr.syntax).
Local Notation SC := (WfSyntaxEricSamOnlyPs.syntax).

Module Syn := Syntax.
Local Notation "'WC' S" := (@Syn.WC _ S) (at level 0).
Local Notation "'WTy' S" := (@Syn.WTy _ S)(at level 0).
Local Notation "'Wtm' S":= (@Syn.Wtm _ S)(at level 0).
Local Notation "'WS' S":= (@Syn.WS _ S)(at level 0).
Local Notation "'SC_WVar' S":= (WfSyntaxEricSamOnlyPs.WVar S)(at level 0).
Local Notation "'SB_WVar' S":= (WfSyntaxBrunerieOnlyContr.WVar S)(at level 0).
(*
Local Notation WTy := (@Syn.WTy _).
Local Notation Wtm := (@Syn.Wtm _).
Local Notation WS := (@Syn.WS _).
Local Notation SC_WVar := (WfSyntaxEricSamOnlyPs.WVar).
Local Notation SB_WVar := (WfSyntaxBrunerieOnlyContr.WVar).
*)

(*
La syntaxe bien typée d'eric sam s'inject dans la syntaxe bien typée de Brunerie
 *)

Fixpoint wCB_C (Γ : Con) (wΓ : WC SC Γ) : WC SB Γ
with wCB_T Γ A (wA : WTy SC Γ A) : WTy SB Γ A
with wCB_Tm Γ A t (wt : Wtm SC Γ A t) : Wtm SB Γ A t
with wCB_V Γ A x (wx : SC_WVar Γ A x) : SB_WVar Γ A x
with wCB_S Γ Δ σ (wσ : WS SC Γ Δ σ) : WS SB Γ Δ σ.
  - destruct wΓ.
    + constructor.
    + constructor.
      * apply:wCB_C => //.
      * apply:wCB_T => //.
      * constructor.
        apply:wCB_V => //.
  - destruct wA.
    + constructor.
      apply:wCB_C => //.
    + constructor.
      * apply:wCB_T => //.
      * apply:wCB_Tm => //.
      * apply:wCB_Tm => //.
  - destruct wt.
    + constructor.
      by apply:wCB_V => //.
    + constructor.
      * apply:wCB_C => //.
      * apply:wCB_T => //.
      * apply:wCB_S => //.
    + rewrite -/((ar  A t u).[σ]T).
      constructor.
      * apply:wCB_C => //.
      * constructor.
        -- apply:wCB_T => //.
        -- apply:wCB_Tm => //.
        -- apply:wCB_Tm => //.
      * apply:wCB_S => //.
 - destruct wx.
   + constructor.
   + constructor.
     * apply:wCB_V => //.
     * apply:wCB_Tm => //.
   + constructor.
     apply:wCB_Tm => //.
   + constructor.
     apply:wCB_Tm => //.
 - destruct wσ.
   + constructor.
     apply:wCB_Tm => //.
   + constructor.
      * apply:wCB_S => //.
      * apply:wCB_T => //.
      * apply:wCB_Tm => //.
      * apply:wCB_Tm => //.
      * apply:wCB_Tm => //.
Defined.

Section GroupoidToCat.
  Context (d : @Decl _ SB).

  Definition d' : @Decl _ SC :=
    {|
      dC := fun Γ  (wΓ : Syn.WC Γ) => ⟦ wCB_C wΓ ⟧C;
      dTy := fun (Γ : Con) (A : Ty) (wΓ : Syn.WC Γ) (wA : Γ ⊢ A) => ⟦ wCB_T wA ⟧T;
      dTm := fun (Γ : Con) (A : Ty) (t : Tm) (wΓ : Syn.WC Γ) (wt : Γ ⊢ t : A) (wA : Γ ⊢ A) =>
               ⟦ wCB_Tm wt ⟧t (wCB_T wA);
      dS := fun (Γ Δ : Con) (σ : sub) (wσ : WfSyntaxEricSamOnlyPs.WS Γ Δ σ) (wΓ : WfSyntaxEricSamOnlyPs.WC Γ) (wΔ : WfSyntaxEricSamOnlyPs.WC Δ) =>
              ⟦ wCB_S wσ ⟧S (wCB_C wΓ)(wCB_C wΔ) |}.

  Import omegagroupoids.
  Lemma isGroupoid_isCat (G : GType)  (gr : isOmegaGroupoid G d) : isOmegaCategory G d'.
    constructor.
    - by apply:dC_astar.
    - intros.
      apply:(dC_ext gr).
    - intros.
      apply:(dT_star gr).
    - intros.
      apply:(dT_ar gr).
    - intros.
      simpl.
      apply:JMeq_trans; last by apply:(sb_dTm gr).
      match goal with
        [ |- ⟦ ?w1 ⟧t ?w2 γ ≅ ⟦ ?w3 ⟧t ?w4 γ ] =>
        rewrite (WTm_hp w1 w3) (WTy_hp w2 w4)
      end.
      easy.
    - apply:(dTm_vstar gr).
    - intros; apply:(dTm_v1 gr).
      eassumption.
    - intros; apply:(dTm_v0 gr) => //.
    - intros; apply:(dTm_vwk gr) => //.
      eassumption.
    - intros;apply:(dS_to_star gr) => //.
    - intros;apply:(dS_to_ext gr) => //.
      exact:H.
      exact:H0.
      exact:H1.
  Qed.

End GroupoidToCat.

