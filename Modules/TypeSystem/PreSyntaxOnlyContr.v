From Modules Require Import Syntax.
From Modules Require Export Syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive Tm : Type :=
  | va (x:Var)
          (* Coh Γ A σ  *)
  | coh : Con -> Ty -> sub -> Tm
with Ty : Type :=
  | star
  | ar : Ty -> Tm -> Tm -> Ty
with  Con : Type :=
      | astar
          (* Γ , x : A, f : x → u is encoded as ext Γ A u *)
      | ext : Con -> Ty -> Tm -> Con
with sub : Type :=
       | to_star : Tm -> sub
       | to_ext : sub -> Tm -> Tm -> sub
with Var : Type :=
  | vstar
  (* toutes ces variables sont dans des contextes étendues *)
  | vwk (v : Var)
  | v0 
  | v1 .

Notation "x:⋆" := astar : presyntax_scope.
Notation " Gamma ,C B , #0 → u " := (ext Gamma B u) (at level 68, B at level 58)
                                   : presyntax_scope.

Notation "⋆" := star : presyntax_scope.
Notation "x →⟨ B ⟩ y" := (ar B x y)  (at level 68, B at level 58) : presyntax_scope.

Notation "❪ t ❫" := (to_star t)   : subst_scope.
Notation " Gamma ,S a  , f" := (to_ext Gamma a f) (at level 68, a at level 58)
                               : presyntax_scope.

Delimit Scope presyntax_scope with Pre.
Open Scope presyntax_scope.

Module S := Syntax.

Instance preSyntax : PreSyntax := {| S.Con := Con ;  S.Ty := Ty ; S.Tm := Tm ; S.sub := sub |}.


(*
Reserved Notation "Gamma ⊢ A : B"
  (at level 68, A at level 99, no associativity,
   format "Gamma  ⊢  A  :  B").
Reserved Notation "Gamma ⊢ A"
  (at level 68, A at level 99, no associativity,
   format "Gamma  ⊢  A").

Reserved Notation "Gamma ⊢ A ⇒ B"
  (at level 68, A at level 99, no associativity,
   format "Gamma  ⊢  A  ⇒  B").

Reserved Notation "Gamma ⊢_v A : B"
  (at level 68, A at level 99, no associativity,
   format "Gamma  ⊢_v  A  :  B").

Notation "Gamma ⊢ A" := (WTy Gamma A)  : wf_scope.
Notation "Gamma ⊢ s : A" := (Wtm Gamma A s) : wf_scope.
Notation "Gamma ⊢  s  ⇒ Delta" :=
  (WS Gamma Delta s)
    : wf_scope.

Open Scope wf_scope.

(* Reserved Notation "sigma ∘ tau"  (at level 56, left associativity). *)

Reserved Notation "s .[ sigma ]T" (at level 2, sigma at level 200, left associativity,
   format "s .[ sigma ]T" ).
Reserved Notation "s .[ sigma ]oT" (at level 2, sigma at level 200, left associativity,
   format "s .[ sigma ]oT" ).

Reserved Notation "s .[ sigma ]wT" (at level 2, sigma at level 200, left associativity,
   format "s .[ sigma ]wT" ).

Reserved Notation "s .[ sigma ]t" (at level 2, sigma at level 200, left associativity,
   format "s .[ sigma ]t" ).

Reserved Notation "s .[ sigma ]V" (at level 2, sigma at level 200, left associativity,
   format "s .[ sigma ]V" ).


*)

Fixpoint sub_Var (σ : sub) (x : Var) : Tm :=
   match σ , x with
     to_star t, vstar => t
   | to_ext σ a f, vwk x => x .[ σ ]V
   | to_ext σ a f, v0 => f
   | to_ext σ a f, v1 => a
   | _,_ => va vstar (* dummy *)
   end
where "s .[ sigma ]V" := (sub_Var sigma s) : subst_scope.


Fixpoint sub_Tm (σ : sub) (t : Tm) : Tm :=
  match t with
  | va x => x .[ σ ]V
          (* Coh Γ A σ  *)
  | coh Γ A δ => coh Γ A (compS δ σ)
  end
    (*
Γ ⊢ σ : Δ
E ⊢ δ : Γ
E ⊢ σ ∘ δ : Δ
     *)
with compS (σ : sub) (δ : sub) : sub :=
       match σ with
         | to_star t => to_star (t .[ δ ]t)
         (* Γ ⊢ σ' : Δ' *)
         (* E ⊢ σ ∘ δ : Δ *)
         (* E ⊢ (σ ∘ δ)' : Δ' *)
         | to_ext σ a f => to_ext (compS σ δ) (a .[ δ ]t) (f .[ δ ]t)
       end
where "s .[ sigma ]t" := (sub_Tm sigma s) : subst_scope.
Notation "sigma ∘ delta"  :=(compS sigma delta)(at level 40, left associativity) : subst_scope.


(* Γ ⊢ idS : Γ *)
Fixpoint idS (Γ : Con) : sub :=
  match Γ with
    astar => to_star (va vstar)
  | ext Γ A u => to_ext (idS Γ) (va v1) (va v0)
  end.


Fixpoint wkt (t : Tm) : Tm :=
  match t with
    va x => va (vwk x)
  | coh Γ A σ => coh Γ A (wkS σ)
  (* | coh_ar Γ A t u σ => coh_ar Γ A t u (wkS σ) *)
  end
with wkS (σ : sub) : sub :=
  match σ with
  | to_star t => to_star (wkt t)
  | to_ext σ a f => to_ext (wkS σ) (wkt a) (wkt f)
  end.

Fixpoint wkT (A : Ty) : Ty :=
  match A with
    star => star
  | ar A t u => ar (wkT A) (wkt t) (wkt u)
  end.


Open Scope subst_scope.


Fixpoint sub_Ty (σ : sub) (A : Ty) : Ty :=
  match A with
    star => star
  | ar A t u => ar (A .[ σ ]T) (t .[ σ ]t) (u .[ σ ]t)
  end
    where "s .[ sigma ]T" := (sub_Ty sigma s) : subst_scope.


(* Definition sub_oTy (σ : sub) (A : option Ty) : option Ty := *)
(*   if A is Some A then Some (A .[ σ ]T) else None. *)

(* Notation "s .[ σ ]oT" := (sub_oTy σ s) : subst_scope. *)

  
(*
Fixpoint beq_var ( x y : Var) : bool :=
  match x,y with
    vstar,vstar => true
  | vwk v, vwk v' => beq_var v v'
  | v0,v0 => true
  | v1, v1 => true
  | _,_ => false
  end.
  
Fixpoint beq_tm (x y : Tm) : bool :=
        (match x,y with
       | va x, va x' => beq_var x x'
       | coh Γ A σ, coh Γ' A' σ' => [ && beq_Con Γ Γ' , beq_Ty A A' & beq_sub σ σ' ]
       | _,_ => false
         end)
with beq_Ty (x y : Ty) :=
       (
       match x,y with
       | star, star => true
       | ar A t u, ar A' t' u' =>
         [ && beq_Ty A A' , beq_tm t t' & beq_tm u u' ]
       (* | none,none => true *)
       | _,_ => false

       end)
with beq_Con (x y : Con) :   bool :=
      (match x , y with
  | astar, astar => true
  | ext Γ A u, ext Γ' A' u' => [ && beq_Con Γ Γ' , beq_Ty A A' & beq_tm u u' ]
  | _,_ => false
     end)
with beq_sub (x y : sub) :   bool :=
  (match x , y with
      | to_star t, to_star t' => beq_tm t t'
      | to_ext σ a f, to_ext σ' a' f' => [ && beq_sub σ σ' , beq_tm a a' & beq_tm f f']
        | _,_ => false
        end).

*)
(*
Definition Var_eqP : Equality.axiom beq_var.
Admitted.
Definition tm_eqP : Equality.axiom beq_tm.
Admitted.
Definition Ty_eqP : Equality.axiom beq_Ty.
Admitted.
Definition sub_eqP : Equality.axiom beq_sub.
Admitted.
Definition Con_eqP : Equality.axiom beq_Con.
Admitted.

Canonical var_eqMixin := EqMixin Var_eqP.
Canonical var_eqType := Eval hnf in EqType Var var_eqMixin.

Canonical tm_eqMixin := EqMixin tm_eqP.
Canonical tm_eqType := Eval hnf in EqType Tm tm_eqMixin.

Canonical Ty_eqMixin := EqMixin Ty_eqP.
Canonical Ty_eqType := Eval hnf in EqType Ty Ty_eqMixin.

Canonical sub_eqMixin := EqMixin sub_eqP.
Canonical sub_eqType := Eval hnf in EqType sub sub_eqMixin.

Canonical Con_eqMixin := EqMixin Con_eqP.
Canonical Con_eqType := Eval hnf in EqType Con Con_eqMixin.

*)