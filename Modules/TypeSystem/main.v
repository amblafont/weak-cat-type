(* remarque 14/04/2017

Il sembel y avoir une forte limiitation des inductifs inductifs pour le schéma d'élimination.
Dans un point fixe mutuellement récursif, je ne peux pas faire apparaître une fonction du groupe
mutuellement récursif dans le type d'un autre...

 *)
Axiom myadmit : forall {A:Type} , A.



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


(* Ctx est l'ensemble des variables libres *)
Inductive Ctx : Type :=
  ctxEmpty
| ctxCons : forall Γ : Ctx, forall A : Ty Γ , Ctx
with Ty : Ctx -> Type :=
     | tyUnit : forall Γ, Ty Γ
     | tyArrow : forall Γ (A:Ty Γ) (t u :  Term A), Ty Γ
with Term : forall Γ, Ty Γ -> Type :=
     | termVar0 : forall Γ  A A',WkTy A A'-> Term (Γ:=(ctxCons Γ A)) A'
     | termWk : forall Γ B A A' , WkTy A A' -> Term (Γ:=Γ) A -> Term
                                                          (Γ:=(ctxCons Γ B))
                                                            A'
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
(* ************

ici le weakening sur les types,
qui se déduit du weakening sur les termes, est une règle admissible. Il y a donc
un algo qui étant donné un type Γ |- A, construit le type affaibli Γ, B |- A'
Comme je ne peux pas définir cette algo en inductif récursif (car les conditions
de typage sont trop strictes : on ne peut pas avoir un constructeur dans le types
du recurseur), j'ai spécifié son comportement à l'aide de l'inductif WkTy

Thorsten dans son papier a mis un constructeur de weakening sur les types explicite
, puis à l'aide d'un HIT il a imposé que ce weakening est le même que celui induit
par les termes.

Je pourrai essayer de définir plus proprement le weakening en intégrant les substitutions
à cette définition (cad en définissant à la fois ce qu'est une substitution bien typée
et comment les termes/types sont substitués à l'aide d'un IR)
En effet, l'existence de σ évident ici Γ,B |- σ : Γ permet de calculer le B affaibli :
c'est B[σ] : Γ,B |- B[σ]



... Non en fait je serai toujours bloqué car comment définir σ ? Ca va faire intervenir
le constructeur _,_ lors de la construction de la substitution affaiblissement
dans le typage Γ,B |- σ : Γ



************ *)

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


Inductive test1 : Type :=
  T1 : test1
with test2 : test1 -> Type :=
       T2 : test2 T1.

(*
**************

Impossible de mettre rec1 dans le type de rec2 !!

Cela veut dire que je ne pourrai pas définir
par récursion mutuelle wfCtx_mut (cf plus loin

pourtant ca rentre bien dans les critères de Matthieu et Cyprien non ?
*)
Definition yop:= (fix rec1 (a:test1) (* {struct a} *) : nat :=
         match a with
           T1 => myadmit
         end
         with rec2 (z:test1)  (u:test2 z) {struct u} : rec1 z  = 0 :=
           match u in test2 z' return rec1 z' = 0  with
             T2 => @myadmit (@myadmit nat = 0)
           end
           (* myadmit *)
      for rec1).

(*
Fail (fix rec1 (a:test1) : Type :=
         myadmit
         with rec2 (z:test1)  (u:test2 z) : rec1 z := myadmit
      for rec1).
*)
                    

Module CustomInduction.
  Lemma wfCtx_mut :
    (
      forall (P : forall c : Ctx, Type)
        (P0 : forall (c : Ctx) (A : Ty c), P c -> Type)
        (Pt : forall (Γ : Ctx) (A:Ty Γ) (t  : Term A) rΓ , P0 Γ A rΓ -> Type)
        (Pw : forall (Γ Γ':Ctx) (A : Ty Γ) (A' : Ty Γ') rΓ rΓ' (rA : P0 Γ A rΓ)
                (rA' : P0 Γ' A' rΓ'), Type)
        (Pempty :(P ctxEmpty)),
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
             (rA : P0 _ A  rΓ)
             (rΓ' := Pext Γ A rΓ rA)
             (* (rΓ' : P Γ')  *)
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
    Admitted.

Unset Implicit Arguments.

  Variables (P : forall c : Ctx, Type)
        (P0 : forall (c : Ctx) (A : Ty c), P c -> Type)
        (Pt : forall (Γ : Ctx) (A:Ty Γ) (t  : Term A) rΓ , @P0 Γ A rΓ -> Type)
        (Pw : forall (Γ Γ':Ctx) (A : Ty Γ) (A' : Ty Γ') rΓ rΓ' (rA : @P0 Γ A rΓ)
                (rA' : P0 Γ' A' rΓ'), Type)
        (Pempty :(P ctxEmpty))
        (* extension des contexte *)
        (Pext : (forall (Γ : Ctx) (A : Ty Γ) (* (w : wfCtx Γ), *),
                  forall (γ : P Γ ),  P0 Γ A γ -> P (ctxCons  A)))
          (* tyUnit *)
          (Pstar : forall (Γ : Ctx)  (γ: P Γ ) , P0 Γ (tyUnit _) γ)
          (* pour la flèche *)
          (Par : forall (Γ : Ctx) (A:Ty Γ) (t u : Term A)  
             (rΓ : P Γ )
             (rA : P0 Γ A rΓ),
              Pt Γ A t rΓ rA -> Pt Γ A u rΓ  rA-> P0 Γ A rΓ) 
          (Pvar0 : forall (Γ : Ctx) (A : Ty Γ)
             (Γ' := ctxCons A)
             (A': Ty Γ')  (wA : WkTy A A')
             (rΓ : P Γ) 
             (rA : P0 _ A  rΓ)
             (rΓ' := Pext Γ A rΓ rA)
             (* (rΓ' : P Γ')  *)
             (rA' : P0 _ A' rΓ')
             (rWa : Pw Γ _ A A' rΓ rΓ' rA rA'),
              Pt Γ' A' (termVar0 (A:=A) wA ) rΓ' rA').

  Definition custom_elim (c:Ctx) : P c :=
    fix wfctx (c:Ctx) : P c :=
      match c with
        ctxEmpty => Pempty
      | ctxCons Γ A => Pext Γ A (wfctx Γ) (wfty
          (*
*)
          (*
(forall (Γ : ctx) (s A B : term) (t : Γ |- s : A),
 P1 Γ A s t -> forall w : Γ |- B, P0 Γ B w -> P1 (B :: Γ) A.[ren (+1)] s.[ren (+1)] (ty_termS t w)) ->
           *)
          forall (c : Ctx) , P c )
    intros ??????.
    intros Pstar Parrow Pvar0 .
    refine (fix wfctx (c:Ctx) {struct c}: P c :=
              match c with
                ctxEmpty => Pvar0
              | 
            with wfty c A r : P0 c A r := myadmit for wfctx).
    revert c.
    (*

impossible de définir le point fixe , à cause de la raison donnée plus haut
    refine (fix wfctx (c:Ctx) {struct c}: P c :=
              myadmit
            with wfty c A r : P0 c A r := myadmit for wfctx).
*)
  Admitted.

  Parameter (Tstar:Type).
  Parameter (Tarrow : (forall (Γ : Ctx) (A : Ty Γ),
        Term A -> Term A -> forall (rΓ : Type) (rA : rΓ -> Type),
        (forall γ : rΓ, rA γ) -> (forall γ : rΓ, rA γ) -> rΓ -> Type)).
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  eq_rect x P u y p.

(* C'est la naturalité de phi vis à vis de pi qui donne cette equation *)
  Definition Pext (Γ Γ' : Ctx) (A:Ty Γ) (A': Ty Γ') (rΓ rΓ' : Type)
             (rA:rΓ -> Type) (rA':rΓ' -> Type):Type :=
    forall (e : rΓ' = sigT rA) (γ:rΓ'),  rA' γ = rA (projT1 (transport (fun z => z) e γ)).

  Definition modVar0 : (forall (Γ : Ctx) (A : Ty Γ) (A' : Ty (ctxCons A)),
        WkTy A A' ->
        forall (rΓ : Type) (rA : rΓ -> Type) (rA' : {x : rΓ & rA x} -> Type),
        (forall (e : {x : rΓ & rA x} = {x : rΓ & rA x}) (γ : {x : rΓ & rA x}),
         rA' γ = rA (projT1 (transport (fun z : Type => z) e γ))) -> forall γ : {x : rΓ & rA x}, rA' γ).
  intros Γ A A' wk rΓ rA rA' h γ.
  specialize (h eq_refl γ).
  rewrite h.
  exact(projT2 γ).
  Defined.

  
  Definition needed   := @wfCtx_mut (fun _  => Type) (* (fun _ _ _ => Type) *)
                                     (fun _ _   γ => γ -> Type)
                                     (fun _ _ _ _   rA => forall γ, rA γ)
                                     Pext
                                     (* (fun _ _ _ _ _ _ rA rA' => Type) *)
                                     unit (fun _ _ _ rA => sigT rA)
                                     (fun _ _ _ => Tstar)
                                     Tarrow
                                     modVar0.
  Definition tneeded := ltac: (match (type of needed) with ?x => set (y:=x); cbn in y; exact y end).
  Goal True.
    (match (type of needed) with ?x => set (y:=x); cbn in y end).
    unfold Pext in y.

  y := forall
         h : forall Γ Γ' : Ctx,
             Ty Γ -> Ty Γ' -> forall rΓ rΓ' : Type, (rΓ -> Type) -> (rΓ' -> Type) -> Type,

       (forall (Γ : Ctx) (A : Ty Γ) (A' : Ty (ctxCons A)),
        WkTy A A' ->
        forall (rΓ : Type) (rA : rΓ -> Type) (rA' : {x : rΓ & rA x} -> Type),
        h Γ (ctxCons A) A A' rΓ {x : rΓ & rA x} rA rA' -> forall γ : {x : rΓ & rA x}, rA' γ) ->
       Ctx -> Type : Type
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
    