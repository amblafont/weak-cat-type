
Axiom myadmit : forall (A:Type) , A.
(* Comment on fait ça dans le lambda calcul typé ? *)
(* Definition augment {A:Type} (f:A -> Type) (a:A) : A -> Type := ?? *)
Inductive Ty (ty:Type) (fv:ty -> Type) : Type :=
  ty_fv (A:ty): Ty ty fv 
(* | ty_star : Ty ty fv *)
| ty_arrow (A:ty) (t: fv A) (u:fv A):  Ty ty fv
  with Term (ty:Type) (fv:ty -> Type) : Ty ty fv -> Type :=
  tm_fv (A:ty) (v:fv A): Term ty fv (ty_fv A) .

Inductive derive_tm (ty:Type) (fv:ty -> Type) (A:ty) : ty -> Type :=
  Some_fv B : fv B -> derive_tm ty fv A B
| New_fv : derive_tm ty fv A A.

Record Ctx := New_Ctx { ctx_ty : Type; ctx_tm : ctx_ty -> Type}.

Definition empty_ctx : Ctx := New_Ctx  False  (fun _ => False).
Definition empty_star_ctx : Ctx := New_Ctx  unit  (fun _ => False).

Definition TT (c:Ctx) : Ctx :=
  New_Ctx (Ty (ctx_ty c) (ctx_tm c)) (Term (ctx_ty c) (ctx_tm c)).

Definition E (c:Ctx) (A:ctx_ty c) :=
  New_Ctx (ctx_ty c) (derive_tm (ctx_ty c) (ctx_tm c) A).

(*

Je veux construire le contexte x:*, y : * -> * |-

*)

(* Un modèle : j'ai un contexte ctx et son type associé [| ctx |].
Je veux le type de E(ctx)A (dérivaion par un type A) *)
Record Model :=
  Build_Model {
      Tstar : Type;
      Tarrow : forall (Γ : Ctx) (sΓ : Type),
          forall (A : ctx_ty Γ) (sA : sΓ -> Type) ,
            ctx_tm Γ A -> ctx_tm Γ A ->
            forall (st su : forall γ, sA γ),
            sΓ -> Type}.

Record Semantique Γ :=
  { sΓ : Type;
    styΓ: forall A:ctx_ty Γ, sΓ -> Type;
    stmΓ : forall (A:ctx_ty Γ) (t:ctx_tm Γ A) (γ : sΓ), styΓ A γ}.

Definition empty_semantique : Semantique empty_ctx :=
  {| sΓ := unit; styΓ := fun _ _ => unit; stmΓ := fun _ _ _ => tt |}.

Definition empty_star_semantique (m:Model) : Semantique empty_star_ctx :=
 {|
 sΓ := unit;
 styΓ := fun (_ : ctx_ty empty_star_ctx) (_ : unit) => Tstar m;
 stmΓ := fun (_ : unit) (t : False) (_ : unit) => False_rect (Tstar m) t |}.

Section model.

  Variables (Γ : Ctx) (semΓ : Semantique Γ).



  Section model_EE.
    Variable (A:ctx_ty Γ).
    Definition sΓA  : Type := sigT (semΓ.(styΓ _) A).
    Definition styΓA  (B:ctx_ty (E Γ A)) (x:sΓA) : Type := semΓ.(styΓ _) B (projT1 x).
    Definition stmΓA  (B:ctx_ty (E Γ A)) (t:ctx_tm (E Γ A) B) (γ : sΓA)
      : styΓA B γ :=
      match t in (derive_tm _ _ _ y) return (styΓA y γ) with
      | Some_fv _ _ _ B0 t0 => semΓ.(stmΓ _) B0 t0 (projT1 γ)
      | New_fv _ _ _ => projT2 γ
      end.
    Definition semΓA := Build_Semantique _ sΓA styΓA stmΓA.
  End model_EE.

  Section model_TT.
    (* paramètres du modèle *)
    Variable (m:Model).

    Definition sTTΓ := semΓ.(sΓ _).
    Definition styTTΓ  (A:ctx_ty (TT Γ)) (x:semΓ.(sΓ _)) : Type :=
      match A with
      | ty_fv _ _ A0 => semΓ.(styΓ _) A0 x
      (* | ty_star _ _ => m.(Tstar) *)
      | ty_arrow _ _ A0 t u => m.(Tarrow) Γ semΓ.(sΓ _) A0
                                         (semΓ.(styΓ _) A0) t u
                                         (semΓ.(stmΓ _) A0 t)
                                         (semΓ.(stmΓ _) A0 u) x
      end.

    Definition stmTTΓ  (B:ctx_ty (TT Γ )) (t:ctx_tm _ B) (γ : sTTΓ)
      : styTTΓ B γ :=
      match t in (Term _ _ t0) return (styTTΓ t0 γ) with
      | tm_fv _ _ A v => semΓ.(stmΓ _) A v γ
      end.

    Definition semTTΓ := Build_Semantique _ sTTΓ styTTΓ stmTTΓ.
  End model_TT.

End model.

Inductive finCtx : Ctx  -> Type :=
  (* fin_empty : finCtx (empty_ctx) *)
  fin_empty : finCtx (empty_star_ctx)
| fin_E c (A:ctx_ty c) : finCtx c -> finCtx ( (E c A))
| fin_TT c  : finCtx c -> finCtx (TT c ).
Fixpoint semType (m:Model) Γ (e:finCtx Γ) : Semantique Γ :=
  match e in (finCtx c) return (Semantique c) with
  (* | fin_empty => (* semTTΓ _ *) empty_semantique (* m *) *)
  | fin_empty => (* semTTΓ _ *) empty_star_semantique m (* m *)
  | fin_E c A e0 => (semΓA c (semType m c e0) A) 
  | fin_TT c e0 => semTTΓ c (semType m c e0) m
  end.

(* Je veux faire le context x : *, y : * |- *)
Definition simplctx :=  (E ( (E (empty_star_ctx) tt)) tt).

Lemma is_fin_simplctx : finCtx simplctx.
  repeat constructor.
Defined.

Definition t_simplctx : ctx_tm simplctx _ (* (ty_fv _ _ tt) *) :=
  (* tm_fv _ _ _ *)
  (Some_fv _ _ _ _
     (New_fv _ _ _)).

Definition u_simplctx : ctx_tm simplctx _ (* (ty_fv _ _ tt) *) :=
  (* tm_fv _ _ _ *)
  ((New_fv _ _ _)).

Definition shift_model (m:Model) (x y : m.(Tstar)) : Model.
  set (h := semType m _ is_fin_simplctx).
  (* set (tm := ctx_tm simplctx (ty_star _ _)). *)
  (* cbn  in tm. *)
  (* assert ( *)
  (* set (t := tm_fv _ _ _ (New_fv _ _ _ ): tm). *)
  (* set (u := Some_fv _ _ _ _ (New_fv _ _ _)  : tm). *)
  set (tar := ty_arrow _ _ _ t_simplctx u_simplctx: ctx_ty (TT simplctx)).
  set (h' := semTTΓ _ h m).
  econstructor.
  - eapply (styΓ _ h' tar).
    unshelve eexists.
    + exists tt.
      exact x.
    + exact y.
  - exact m.(Tarrow).
Defined.

CoInductive gset : Type :=
  { cells : Type;
    suite : cells -> cells -> gset }.

CoFixpoint model_gset (m:Model) : gset :=
  {| cells := m.(Tstar);
     suite := fun x y => model_gset (shift_model m x y) |}.

Definition typeModel (T:Type) : Model .
  econstructor.
  exact T.
  intros Γ sΓ A sA t u st su γ.
  exact (st γ = su γ).
Defined.

Definition typeGset T := model_gset (typeModel T).

Goal True.
  set (x := (typeGset nat).(suite) 1 2).
  set (y := x.(cells)).
  cbn  in y.
    
