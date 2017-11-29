
(* an omega groupoid is an omega cat *)
Require Import ssreflect ssrfun ssrbool .

From Modules Require Import libhomot untypeduippackrl TypesAreOmegaGroupoids.FunctionalRelation lib Syntax WfSyntaxBrunerieOnlyContr gtypeext omegagroupoids fullomegagroupoids WfSyntaxBrunerieAllCtx.
Require Import Coq.Logic.JMeq.
Set Bullet Behavior "Strict Subproofs".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation "⟦ X ⟧V" := (dTm (w_va X)).

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
(*
Local Notation WTy := (@Syn.WTy _).
Local Notation Wtm := (@Syn.Wtm _).
Local Notation WS := (@Syn.WS _).
Local Notation SC_WVar := (WfSyntaxEricSamOnlyPs.WVar).
Local Notation SB_WVar := (WfSyntaxBrunerieOnlyContr.WVar).
*)

(*
Indépendemment du pb d'équivalence dont je parle ensuite, de toute manière, je suis obligé de
redéfinir par récurrence l'interprétation de FB à partir de l'interprétation de B. Donc,
il faut un inductif pour la relation fonctionnelle, etc... 

Est-ce que ça vaut le coup de définir une bonne fois pour toute le schéma d'élimination ?



Maintenant, pour transformer un modèle de B (Brunerie) vers FB (full brunerie), je suis confronté au
pb suivant :
- pour B, ⟦ (x : * ) ⟧ = Σ_(γ : ⊤) | G |
- pour FB, ⟦ (x : * ) ⟧ = | G |

Ce qui est un peu relou. Les deux types sont équivalents mais pas égaux strictement.
Du coup j'ai 2 solutions :


+ changer la def de ce que c'est un omega groupoide en demandant non pas une égalité mais une équivalence.
Appelons cette définition une déf wild. Par contre, on demande ⟦ σ , t ⟧ = ⟦ σ ⟧, ⟦ t ⟧ strictement.
Mais pour l'équivalence, on utilise quelle égalité ??


+ avoir les 2 définitions, et montrer qu'un omega groupoide wild induit un omega groupoide normal.



Autre idée :
imposer qu'un omega groupoide s'interpréte dans GhSet plutôt que GType.
En quoi un type est un omega groupoide ? Etant donné un GType G, on peut considérer sa troncation G'
où tous les obj ont été tronqués au niveau hSet. On a un morphisme
Je ne pense pas qu'on puisse tronquer ainsi un GType.

--------------
Il faudrait montrer qu'un omega groupoide sur G induit un omega groupoide sur G'

Mais plus généralement, si on a un morphisme de type globulaire G₁ → G₂, si G₁ est un omega groupoide,
G₂ ne l'est-il pas également ?

Si ça marche, alors pas besoin de 2TT pour la def d'omega groupoide., mais besoin d'une troncation hSet.

Est-ce légitime de demander des égalités strites dans la def d'omega groupoides ? Oui, ou alors il faut demander à ce que le type globulaire est un hset. Mais alors comment montrer que les types sont
des omega groupoides ? Peut-on se passer de 2TT ainsi ? Pas sûr. Mais au moins, cette nouvelle def
serait moins chiante (avec l'axiome d'univalence, ou alors sans mais en demandant une équivalence plutôt qu'une égalité) pour montrer ce que je veux dans ce fichier.

Mais puis je me passer de 2TT ?

Ce qui vient après est idiot. J'avais oublié que isEquiv(f) est hprop mais pas Equiv(A,B)
-----------------------------------------------------------
Notion d'égalité hétérogène hprop dans hott :
t : A, u : B
t ≅ u := ∀ (P : ∀ X:Type, X -> Type), P A t ~ P B u
où '~' est l'équivalence hprop isEquiv
t ≅ u -> A ~ B et t ~ u par cette equivalence (prendre P X x = X ~ B et e(x) = b)

Mais alors, false ≅ true avec cette égalité.

Peut on donner une définition sans 2TT d'un omega groupoide avec cette égalité malgré tout ?



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

