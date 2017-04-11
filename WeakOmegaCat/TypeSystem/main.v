(* remarque *)
Set Implicit Arguments.

(* Inductive Ctx2 := R:Ctx2. *)
(*
Inductive Ctx : Type :=
  ctxEmpty
| ctxCons : forall Γ : Ctx, forall A : Ty Γ -> Ctx
with Ty : Ctx -> Type :=
     | tyUnit : forall Γ, Ty Γ
     | tyArrow : forall Γ (A:Ty Γ) (t u :  Term A), Ty Γ
with Term : forall Γ, (Ty Γ -> Type) -> Ty Γ -> Type.
*)
Axiom myadmit : forall {A:Type} , A.


(* Ctx est l'ensemble des variables libres *)
Inductive Ctx : Type :=
  ctxEmpty
| ctxCons : forall Γ : Ctx, forall A : Ty Γ , Ctx
with Ty : Ctx -> Type :=
     | tyUnit : forall Γ, Ty Γ
     | tyArrow : forall Γ (A:Ty Γ) (t u :  Term A), Ty Γ
with Term : forall Γ, Ty Γ -> Type :=
   (* | termVar : forall Γ (A:Ty Γ), Var A -> Term  A *)
     | termVar0 : forall Γ  A A',WkTy A A'-> Term (Γ:=(ctxCons Γ A)) A'
     | termWk : forall Γ B A A' , WkTy A A' -> Term (Γ:=Γ) A -> Term
                                                          (Γ:=(ctxCons Γ B))
                                                            A'
                                                        (*
with SmallerCtx : Ty -> Ty -> Type :=

with Var : forall Γ, Ty Γ -> Type :=
       var0 : forall Γ  A A',WkTy A A'-> Var (Γ:=(ctxCons Γ A)) A'
     | varS : forall Γ (A B  :Ty Γ) A', WkTy A A' ->
                                   Var (Γ:=Γ) A -> Var (Γ:=(ctxCons Γ B)) A'
*)
with WkTy : forall Γ Γ', Ty Γ -> Ty Γ' -> Type :=
     | wkTy0 : forall Γ B, WkTy (Γ:=Γ) (Γ':= ctxCons Γ B) (tyUnit _) (tyUnit _)
     | wkTyArrow : forall Γ B (A :Ty Γ) A' (t u : Term A) (w:WkTy A A') ,
         WkTy (Γ:=Γ) (Γ':=ctxCons Γ B)
               (tyArrow _ _ t u)
               (tyArrow
                  (ctxCons Γ B)
                  _
                  (termWk Γ B A A' w t)
                  (termWk Γ B A A' w u)
                ).

Unset Implicit Arguments.
Axiom expladmit : (forall A,A).
Inductive substs : Ctx -> Ctx -> Type :=
| subEmpty : forall Gamma, substs Gamma ctxEmpty
| subNext  : forall (Delta Gamma:Ctx) (sigma : substs Delta Gamma),
                     forall (A:Ty Gamma),
                ( Term (Γ := Delta) (@sub_type Delta Gamma A sigma)) ->
                (* ( Term (sub_type Δ Γ)) ->  *)
                     (* ( Term (sub_type σ)) ->  *)
    substs Delta (ctxCons A)
           fix sub_type (Delta Gamma:Ctx) (A:Ty Gamma) {struct A} :
                  substs Delta Gamma -> Ty Delta :=
  match A in Ty Gamma return substs Delta Gamma -> Ty Delta with
    tyUnit _ => fun _ => tyUnit _
  | @tyArrow Γ A t u =>
    fun (sigma:substs Delta Γ) =>
    let Asub:= sub_type Delta Γ A sigma in
    
    let fix sub_term (t:Term A)  : Term Asub :=
        match t in @Term Γ A  with
        | @termVar0 Γ1   Af A' w   =>
          expladmit (Term Asub)
                    (*
            match sigma return Term Asub
            with
            subEmpty _ => myadmit (* impossible*)
          | @subNext Δ Γ1 σ' A1 t => myadmit
            end
*)
            (*
          let Γext := (ctxCons (Γ:=Γ1) Af) in
          (* fun (sigma : substs Delta Γext  ) => *)
                  (* forall (A:Ty Γ),  *)
                  (*   Term (sub_type Delta Γ A _) *)
            with
            subEmpty _ => myadmit (* impossible*)
          | @subNext Δ Γ1 σ' A1 t => myadmit
                (*                       t *)
                (* : ( Term (Γ := Δ) (@sub_type Δ Γ1 A1 σ' ))  *)
          end
*)
              
        | @termWk   Γ B A A' w t => myadmit
        end
            
    in
    @tyArrow Delta Asub (sub_term t) (sub_term u)
    end.

       match t with
         termVar0 Γ A A'


Inductive substs : Ctx -> Ctx -> Type :=
| subEmpty : forall Gamma, substs Gamma ctxEmpty
| subNext  : forall (Delta Gamma:Ctx) (sigma : substs Delta Gamma),
              0 = sub_type Delta Gamma sigma ->
            (* ( Term (Γ := Delta) (@sub_type Delta Gamma sigma )) -> *)
            (* ( Term (sub_type Δ Γ)) ->  *)
                  (* ( Term (sub_type σ)) ->  *)
                     forall (A:Ty Gamma),
    substs Delta (ctxCons A)
           fix sub_type (Delta Gamma:Ctx) (sigma:substs Delta Gamma) : nat := 0.
  : Ty Delta
  := tyUnit _.
(σ : substs Δ Γ) (A:Ty Γ) : Ty Δ := tyUnit. myadmit.
    