(* We make a translation from full brunerie (any ctx) to brunerie *)
Require Import ssreflect ssrfun ssrbool .

From Modules Require Import HomotopicalEquality TypesAreOmegaGroupoids.FunctionalRelation lib PreSyntaxOnlyContr .
From Modules Require Import WfSyntaxBrunerieOnlyContr.
(* gtype decl omegagroupoids fullomegagroupoids. *)
From Modules Require Import WfSyntaxBrunerieAllCtx.
Set Bullet Behavior "Strict Subproofs".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Local Notation "⟦ X ⟧V" := (dTm (w_va X)). *)

Module B := WfSyntaxBrunerieOnlyContr.
Module FB := WfSyntaxBrunerieAllCtx.


Local Notation SB := (B.syntax).
Local Notation SF := (FB.syntax).

Module Syn := Syntax.
Local Notation "'WC' S" := (@Syn.WC _ S) (at level 0).
Local Notation "'WTy' S" := (@Syn.WTy _ S)(at level 0).
Local Notation "'Wtm' S":= (@Syn.Wtm _ S)(at level 0).
Local Notation "'WS' S":= (@Syn.WS _ S)(at level 0).
Local Notation "'SF_WVar' S":= (FB.WVar S)(at level 0).
Local Notation "'SB_WVar' S":= (B.WVar S)(at level 0).

Module SS  := PreSyntaxOnlyContr.
(*
Local Notation WTy := (@Syn.WTy _).
Local Notation Wtm := (@Syn.Wtm _).
Local Notation WS := (@Syn.WS _).
Local Notation SC_WVar := (WfSyntaxEricSamOnlyPs.WVar).
Local Notation SB_WVar := (WfSyntaxBrunerieOnlyContr.WVar).
*)
(*

On pourrait essayer de montrer la chose suivante pour la syntaxe full brunerie :
si Γ ⊢ coh_Δ,A[σ] alors il existe Γ' ⊂ Γ  contractile et Γ' ⊢ δ : Δ telles que σ 
bof..

Ou encore: on fait une traduction Full Brunerie -> Brunerie pour la sous-syntaxe de Full Brunerie
restreint aux contextes contractiles.
C'est parti


*)

Fixpoint tradV Γ x  : SS.Var :=
  match Γ,x with
    ext empty _, v0 => vstar
  | ext (ext Γ A) B, v0 => SS.v0
  | ext (ext Γ A) B, vwk v0 => SS.v1
  | ext (ext Γ A) B, vwk (vwk x) => SS.vwk (tradV Γ x)
  (* dummy *)
  | _,_ => vstar
  end.

(*
Fixpoint tradV Γ A x (wx : SF_WVar Γ A x) : SB.Var.
 destruct wx.
 - (* dummy *)
   exact:vstar.
 - (* cas v0 *)
*)

Ltac exfalsoinvert h := exfalso; inversion h.
    
Fixpoint tradC (Γ : FB.Con)  (isC : isContr Γ) (wΓ: FB.WC Γ) : SS.Con
with tradTy (Γ : FB.Con) (A : FB.Ty) (wA : FB.WTy Γ A) : SS.Ty
with tradTm (Γ : FB.Con) A (t : FB.Tm) (wt : FB.Wtm Γ A t) : SS.Tm
with tradS Γ (Δ : FB.Con) (σ : FB.sub) (wσ : FB.WS Γ Δ σ) : SS.sub.
- destruct wΓ as [| ? ? ? wA].
  + by exfalsoinvert isC.
  + destruct wΓ.
    * destruct A ; last by exfalsoinvert isC.
      exact:astar.
    * destruct A; first by exfalsoinvert isC.
      destruct t; last by  exfalsoinvert isC.
      destruct x; last by  exfalsoinvert isC.
      apply:SS.ext.
    -- apply:(tradC _  (snd isC)) => //.
    (* apply:isContr_WC => //. *)
    -- apply:(tradTy Γ).
      eassumption.
    -- apply:tradTm.
      eassumption.
- destruct wA.
  (* star *)
  + exact:SS.star.
  + apply:SS.ar.
    * apply:tradTy.
      exact:wA.
    * apply:tradTm.
      exact :w.
    * apply:tradTm.
      exact :w0.
- destruct wt.
  (* variable *)
  + exact:(SS.va (tradV Γ x)).
  + apply:SS.coh.
    * apply:tradC; last by eassumption.
      (* eassumption. *)
    * apply:tradTy.
      exact:w0.
    * apply:tradS.
      eassumption.
- destruct wσ.
  (* to_empty.. *)
  + (* dummy *)
    exact :(SS.to_star (SS.va (SS.vstar))).
  + destruct wσ; first by exact :(SS.to_star (SS.va (SS.vstar))).
    apply:SS.to_ext.
    * apply:tradS.
      eassumption.
    * apply:tradTm.
      exact:w2.
    * apply:tradTm.
      exact:w0.
Defined.

(*
Fixpoint tradC (Γ : FB.Con)  (isC : isContr Γ) : SS.Con
with tradTy (Γ : FB.Con) (A : FB.Ty) (wA : FB.WTy Γ A) : SS.Ty
with tradTm (Γ : FB.Con) A (t : FB.Tm) (wt : FB.Wtm Γ A t) : SS.Tm
with tradS Γ (Δ : FB.Con) (σ : FB.sub) (wσ : FB.WS Γ Δ σ) : SS.sub.
- destruct isC.
  + exact:astar.
  + apply:SS.ext.
    * apply:(tradC _  isC) => //.
      (* apply:isContr_WC => //. *)
    * apply:(tradTy Γ).
      eassumption.
    * apply:tradTm.
      eassumption.
- destruct wA.
  (* star *)
  + exact:SS.star.
  + apply:SS.ar.
    * apply:tradTy.
      exact:wA.
    * apply:tradTm.
      exact :w.
    * apply:tradTm.
      exact :w0.
- destruct wt.
  (* variable *)
  + exact:(SS.va (tradV Γ x)).
  + apply:SS.coh.
    * apply:tradC; last by eassumption.
      (* eassumption. *)
    * apply:tradTy.
      exact:w0.
    * apply:tradS.
      eassumption.
- destruct wσ.
  (* to_empty.. *)
  + (* dummy *)
    exact :(SS.to_star (SS.va (SS.vstar))).
  + destruct wσ; first by exact :(SS.to_star (SS.va (SS.vstar))).
    apply:SS.to_ext.
    * apply:tradS.
      eassumption.
    * apply:tradTm.
      exact:w2.
    * apply:tradTm.
      exact:w0.
Defined.

Local Notation "⟦ X  ⟧C" := (tradC X ).
Local Notation "⟦ X ⟧T" := (tradTy X).
Local Notation "⟦ X ⟧t" := (tradTm X).
Local Notation "⟦ X ⟧S" := (tradS X).

Lemma w_tradStar (Γ : FB.Con) wΓ (isC : isContr Γ)   : B.WTy ⟦ isC ⟧C ⟦ w_star (Γ := Γ) wΓ ⟧T.
Proof.
  induction isC => /=; repeat constructor.
Abort.

Fixpoint w_tradC Γ  (isC : isContr Γ) : (B.WC ⟦ isC ⟧C * B.WTy ⟦ isC ⟧C ⟦ w_star (Γ := Γ) (isContr_WC isC) ⟧T)
with w_tradTy (Γ : FB.Con) (isC : isContr Γ) (A : FB.Ty) (wA : FB.WTy Γ A) : B.WTy ⟦ isC ⟧C ⟦ wA ⟧T.
- destruct isC => /=.
  + repeat constructor.
  + split.
    {
      constructor.
    * apply:(fst (w_tradC _ _)).
    * apply:w_tradTy.
    * admit.
      }
    {
      repeat constructor.
      - apply:(fst (w_tradC _ _)).
      - apply:w_tradTy.
      - admit.
        }

- Guarded.
    destruct wA => /=.
  + apply:(snd (w_tradC _ isC)).
  + Guarded.
(*
Fixpoint tradC (Γ : FB.Con)  : SS.Con :=
  match Γ with
    | ext empty star => astar
    | ext (ext Γ A) (ar _ (va v0) u) => astar
    (* dummy *)
    | _ => astar
  end
with tradTy (Γ : FB.Con) (A : FB.Ty) : SS.Ty
with tradTm (Γ : FB.Con) (t : FB.Tm) : SS.Tm
with tradS (Δ : FB.Con) (σ : FB.sub) : SS.sub.
  - destruct isC.
    + exact astar.
    + apply:SB.ext.
      * exact:(tradC _ isC).
      * exact:IHisC.
*)


(*
La syntaxe bien typée full brunerie s'injecte dans brunerie minimal
avec des contextes non vides

Traduction Full Brunerie --> Brunerie

⟦ x:* ⟧ = ⟦ x : * ⟧
⟦ Γ , x : A ⟧ = ⟦ Γ ⟧ , x : ⟦ A ⟧, f : x -> coh_⟦Γ⟧,⟦A⟧ 

⟦ * ⟧ = *
⟦ t ->_A u ⟧ = ⟦ t ⟧ ->_⟦A⟧ ⟦ u ⟧

⟦ v0 ⟧ = v1
⟦ vwk x ⟧ = vwk ⟦ x ⟧
⟦ coh_Γ,A [σ ] ⟧ = coh_⟦Γ⟧,⟦A⟧ [ ⟦ σ ⟧ ]

Pour les substitutions
⟦ (t) ⟧ = to_star ⟦ t ⟧
⟦ (σ, t) ⟧ =  (⟦ σ ⟧, ⟦ t ⟧, coh_⟦Γ⟧,(⟦t⟧ -> coh_⟦Δ⟧,⟦A⟧[⟦σ⟧])

où Γ ⊢ (σ,t) : (Δ, x : A)

 Γ ⊢ A implique  ⟦ Γ ⟧ ⊢ ⟦ A ⟧
 Γ ⊢ t: A -> ⟦ Γ ⟧ ⊢ ⟦ t ⟧ : ⟦ A ⟧
 Γ ⊢ σ : Δ -> ⟦ Γ ⟧ ⊢ ⟦ σ ⟧ : ⟦ Δ ⟧




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

