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
(* with Ty' : forall Γ : Ctx , Ty Γ -> Type := *)
(*                | alone Γ (B:Ty Γ): Ty (ctxCons Γ B) -> Ty' B *)
with Term : forall Γ, Ty Γ -> Type :=
   (* | termVar : forall Γ (A:Ty Γ), Var A -> Term  A *)
     | termVar0 : forall Γ  A A',WkTy A A'-> Term (Γ:=(ctxCons Γ A)) A'
     (* | termVar0' : forall Γ  A A', WkTy A A' -> Term (Γ:=(ctxCons Γ A)) A' *)
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

(* Je voudrais définir maintenant le weakening sur les types par un point fixe *)
(*
Definition wkty :=
  fix wkty Γ (A B :Ty Γ) {struct B} :Ty (ctxCons A)  :=
    myadmit
    with wkterm Γ (A B:Ty Γ) (t:Term B) {struct t} : Term (wkty Γ A B) := myadmit
                                                                 for wkty.
  induction B.
  - apply tyUnit.
  - unshelve eapply tyArrow.
    apply IHB.
*)

Scheme wfCtx_mut := Induction for Ctx Sort Type
with wfTy_mut := Induction for Ty Sort Type
with ty_mut := Induction for Term Sort Type
with wkty_mut := Induction for WkTy Sort Type.
Module CustomInduction.
  Parameter (Tstar:Type).
  Axiom wfCtx_mut :
    (
      forall (P : forall c : Ctx, Type)
        (P0 : forall (c : Ctx) (A : Ty c), P c -> Type)
        (Pt : forall (Γ : Ctx) (A:Ty Γ) (t  : Term A) rΓ , P0 Γ A rΓ -> Type)
        (Pw : forall (Γ Γ':Ctx) (A : Ty Γ) (A' : Ty Γ') rΓ rΓ' (rA : P0 Γ A rΓ)
                (rA' : P0 Γ' A' rΓ'), Type),
        P ctxEmpty ->
        (* extension des contexte *)
        forall Pext : (forall (Γ : Ctx) (A : Ty Γ) (* (w : wfCtx Γ), *),
                  forall (γ : P Γ ),  P0 Γ A γ -> P (ctxCons  A)),
          (* tyUnit *)
          (forall (Γ : Ctx)  (γ: P Γ ) , P0 Γ (tyUnit _) γ) ->
          (* pour la flèche *)
          (forall (Γ : Ctx) (A:Ty Γ) (t u : Term A)  
             (rΓ : P Γ )
             (rA : P0 Γ A rΓ),
              Pt Γ A t rΓ rA -> Pt Γ A u rΓ  rA-> P0 Γ A rΓ) ->
          (forall (Γ : Ctx) (A : Ty Γ)
             (Γ' := ctxCons A)
             (A': Ty Γ')  (wA : WkTy A A')
             (rΓ : P Γ) 
             (rΓ' : P Γ') 
             (rA : P0 _ A  rΓ)
             (rA' : P0 _ A' rΓ')
             (rWa : Pw Γ _ A A' rΓ rΓ' rA rA'),
              Pt Γ' A' (termVar0 (A:=A) wA ) rΓ' rA')  ->
          (*
*)
          (*
(forall (Γ : ctx) (s A B : term) (t : Γ |- s : A),
 P1 Γ A s t -> forall w : Γ |- B, P0 Γ B w -> P1 (B :: Γ) A.[ren (+1)] s.[ren (+1)] (ty_termS t w)) ->
           *)
          forall (c : Ctx) , P c ).
  Definition needed  h := @wfCtx_mut (fun _ _ => Type) (fun _ _ _ => Type) (fun _ _ _ _ => Type) unit h
                                     (fun _ _ _ => Tstar).
  Definition tneeded := ltac: (match (type of needed) with ?x => set (y:=x); cbn in y; exact y end).
  Goal True.
    (match (type of needed) with ?x => set (y:=x); cbn in y end).
    P0 := fun c _ _ => P c -> Type
End CustomInduction.
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
    