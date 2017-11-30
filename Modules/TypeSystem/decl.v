
Require Import ssreflect ssrfun ssrbool .

From Modules Require Import Syntax HomotopicalEquality lib gtype.

Set Bullet Behavior "Strict Subproofs".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Class Decl {P : PreSyntax} {S : Syntax P} :=
  { dC : forall Γ, WC Γ -> Type;
    dTy : forall Γ A (wΓ : WC Γ)(wA: Γ ⊢ A), dC wΓ -> GType ;
    dTm : forall Γ A t (wΓ : WC Γ)(wt : Γ ⊢ t : A)(wA: Γ ⊢ A)(γ : dC wΓ) ,
            ∣ dTy wA γ ∣ ;
    dS : forall Γ Δ σ (wσ: Γ ⊢ σ ⇒ Δ)(wΓ : WC Γ)(wΔ : WC Δ) (γ : dC wΓ),
            dC wΔ
  }.

Definition extΣ_G (Γ : Type) (A : Γ -> GType) (u : forall γ, ∣ A γ ∣) :=
  { δ : { γ : Γ & ∣ A γ ∣ } & ∣ hom δ..2 (u δ..1) ∣ }.

Notation "⟦ X ⟧C" := (dC X).
Notation "⟦ X ⟧T" := (dTy X).
Notation "⟦ X ⟧t" := (dTm X).
Notation "⟦ X ⟧S" := (dS X).
