
Set Implicit Arguments.
Axiom myadmit : forall (A:Type) , A.
(* Inutile  ??? Il suffit de définir l'extension de contexte non ?*)
Inductive Ty (ty:Type) (fv:ty -> Type) : Type :=
  ty_fv (A:ty): Ty  fv 
| ty_star : Ty fv
| ty_arrow (A:Ty fv) (t u: Term (* ty  *)(* fv  *)A):  Ty (* ty  *)fv
  with Term (ty:Type) (fv:ty -> Type) : Ty ty fv -> Type :=
  tm_fv (A:ty) (v:fv A): Term (* ty  fv*) (ty_fv A) .

Class PreCtx := Build_PreCtx { ctx_ty : Type; ctx_tm : ctx_ty -> Type}.
Arguments ctx_ty  _ : clear implicits.
Arguments ctx_tm  _ _ : clear implicits.
Class AlgCtx (c:PreCtx) :=
  Build_AlgCtx
    { ctx_arrow : forall A (t u :ctx_tm c A), ctx_ty c;
    ctx_star : ctx_ty c}.

Arguments ctx_arrow  _ [_ _] _ _ .
Arguments ctx_star  _ [_].

Definition TT (c:PreCtx) : PreCtx :=
  Build_PreCtx  (Term (fv:=ctx_tm c)).

Instance AlgTT (c:PreCtx) : AlgCtx (TT c) :=
  Build_AlgCtx (TT c) (@ty_arrow (ctx_ty c) (ctx_tm c)) (ty_star (ctx_tm c)).


Section Derivation.
  (* On veut étendre le contexte en ajoutant une variable de type B *)
  Variables (ty:Type) (fv:ty -> Type) (B:ty).

  (* adTy : soit un ancien type, soit un nouveau type qu'on peut former grace
à B
 adTm : pareil mais pour les termes
 dTy : les nouveaux types qu'on peut former
 dTm : les nouveaux termes qu'on peut former
   *)
  Inductive adTy : Type :=
  | adty_old : ty -> adTy
  | adty_new : dTy -> adTy
  with adTm : adTy -> Type :=
       | adtm_new A : dTm A -> adTm A
       | adtm_old A : fv A -> adTm (adty_old A)
  with dTy : Type :=
       | dty_arrowr A (t :fv A) (u:dTm (adty_old A)) : dTy
       | dty_arrowl A (t :dTm (adty_old A)) (u:fv A) : dTy
       | dty_arrowboth A (t :dTm A) (u:dTm A) : dTy
  with dTm : adTy -> Type := 
  | dtm_new : dTm (adty_old B).
End Derivation.


  Definition E (c:PreCtx) (A:ctx_ty c) : PreCtx :=
    Build_PreCtx (ctx_ty:=adTy (ctx_tm c) A) (@adTm _ _ _).

  Instance AlgE (c:PreCtx) {ac:AlgCtx  c} (A:ctx_ty c) :
    AlgCtx (E c A).
  unshelve econstructor.
  - intros B t u.
    destruct t as [C t | C t].
    + apply adty_new.
      destruct u as [ C u | C u].
      * apply (dty_arrowboth t u).
      * apply (dty_arrowl t u).
    + remember ( adty_old _ _ _) as C' eqn:eC in u.
      destruct u as [ C' u | C' u].
      * apply adty_new. subst. apply (dty_arrowr t u).
      * apply adty_old.
        apply (ctx_arrow _ (A:=C) t).
        injection eC.
        destruct 1.
        exact u.
  - apply adty_old.
    apply (ctx_star c).
  Defined.

Definition empty_prectx : PreCtx := Build_PreCtx (ctx_ty :=False)  (fun _ => False).
Definition empty_ctx : PreCtx := TT empty_prectx.

Inductive FinCtx : PreCtx -> Type := 
  fin_nil : FinCtx empty_ctx
| fin_cons C A :  FinCtx C -> FinCtx (E C A).

Fixpoint algFinCtx C (w:FinCtx C) : AlgCtx C.
  destruct w; eauto with typeclass_instances.
Defined.
Existing Instance algFinCtx.

CoInductive gset :=
  Gset { objects : Type ;
         hom :> objects -> objects -> gset }.
CoFixpoint empty_gset : gset := {| objects :=  False ;
                                   hom := fun _ _ => empty_gset  |}.

 Notation "x ..1" := (projT1 x) (at level 2).
Notation "x ..2" := (projT2 x) (at level 2).
Section GSet_Model.
 Variable (g:gset).

  Lemma to_type C (w:FinCtx C) :
    { sΓ : Type & forall ty : ctx_ty C, { sA : sΓ -> gset &
                                               forall tm : ctx_tm C ty, forall γ, objects(sA γ)}}.
    induction w.
    - exists unit.
      intro A.
      exists (fun _ => g).
      cbn.
      now destruct 1.
    - destruct IHw as (sΓ & sAs).
      set (IA := sAs A).
      exists (sigT (fun γ => objects (IA..1 γ))).
      intro B.
      destruct B as [B|B].
      + (* ancien type *)
        set (IB := sAs B).
        exists (fun γ=> IB..1 γ..1).
        remember ( adty_old _ _ _) as C' eqn:eC.
        destruct 1 as [C' u| C' u].
        *  (* nouveau terme *)
          destruct u.
          (* donc A = B *)
          injection eC ; intros ?; subst.
          exact (fun γ => γ..2).
        * (* ancien term *)
          intro γ.
          apply IB..2.
          injection eC.
          destruct 1.
          exact u.
      + (* nouveau type *)
        destruct B as [B t u|B t u|B t u].              
        * (* B est ancien *)
          (* u est nouveau *)
          assert (hAB : A=B) by  now inversion u.
          subst A.
          exists (fun γ => hom (IA..1 γ..1) (IA..2 t γ..1) γ..2).
          now inversion 1.
        * (* B est ancien  t nouveau*)
          assert (hAB : A=B) by  now inversion t.
          subst A.
          exists (fun γ => hom (IA..1 γ..1) (IA..2 u γ..1) γ..2).
          now inversion 1.
        * (* t et u nouveaux. Donc t = u et A = B *)
          destruct t.
          exists (fun γ => hom (IA..1 γ..1) γ..2 γ..2).
          now inversion 1.
  Defined.

  End GSet_Model.



Section Model_GSet.
  Definition simplctx :=  E ( E empty_ctx (ctx_star _)) (ctx_star _).
  Lemma is_fin_simplctx : FinCtx simplctx.
    repeat constructor.
  Defined.

Definition t_simplctx : ctx_tm simplctx (ctx_star _) (* (ty_fv _ _ tt) *).
  apply adtm_old.
  apply adtm_new.
  constructor.
Defined.

Definition u_simplctx : ctx_tm simplctx (ctx_star _) (* (ty_fv _ _ tt) *).
  apply adtm_new.
  constructor.
Defined.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  eq_rect x P u y p.
(* Class Ctx := { ctx_pre : PreCtx; ctx_alg : AlgCtx ctx_pre}. *)
(* Existing Instance ctx_alg. *)
(*
but construire Γ' = x,y:*, Δ où Δ est Γ où * est remplacé par x ->* y dans Γ

Finalement, peut etre inutile
*)
Definition shift_ctx (Γ : PreCtx) (fΓ : FinCtx Γ) :
  {Δ : PreCtx &
       (FinCtx Δ *
        {
          cty : ctx_ty Γ -> ctx_ty Δ &
                           forall A, ctx_tm _ A -> ctx_tm _ (cty A)
       }
            (* (forall A :ctx_ty Γ , {A' : ctx_ty Δ & ctx_tm _ A -> ctx_tm _ A'}) *)
       )%type
  }.
  induction fΓ.
  - unshelve econstructor.
    exact simplctx.
    split.
    exact is_fin_simplctx.
    unshelve eexists.
    {
      induction 1.
    + contradiction.
    + exact ( ctx_arrow _ t_simplctx u_simplctx).
    + destruct t; contradiction.
    }
    {
      intro A.
      destruct 1; contradiction.
    }
    (*
    intro A.
    induction A.
    + contradiction.
    + exists ( ctx_arrow _ t_simplctx u_simplctx).
      induction 1; contradiction.
    + induction t; contradiction.
*)
  - destruct IHfΓ as [Δ [fΔ IΔ]].
    exists (E Δ (IΔ ..1 A)).
    (* exists (E Δ (IΔ A)..1). *)
    split.
    now constructor.
    (* intro B. *)
    unshelve eexists.
    {
    intro B.
    induction B as [B|B].
    + (* old type *)
      (* unshelve eexists. *)
      * apply adty_old.
        exact (IΔ ..1 B).
        (* exact (IΔ B)..1. *)
        (*
      * remember (adty_old _ _ _) as D eqn:eD.
        destruct 1 as [D t|D t].
        -- (* nouvelle variable *)
          apply adtm_new.
          destruct t.
          injection eD; intro eAB.
          pattern B.
          eapply (transport _ eAB).
          constructor.
        -- (* ancienne variable *)
          apply adtm_old.
          apply (IΔ _)..2.
          injection eD; intro eBD.
          pattern B.
          apply (transport _ eBD t).
         *)

    + (* new type *)
      induction B as [B t u|B t u| B t u].
      (* * unshelve eexists; [ apply adty_new|]. *)
      *  apply adty_new.
        -- eapply dty_arrowr.
           (* ++ apply ((IΔ _)..2 t). *)
           ++ apply ((IΔ..2 _ t)).
           ++ assert (eAB : A=B) by now inversion u.
              pattern B.
              eapply (transport _ eAB).
              constructor.
              (*
         -- intro x.
            inversion_clear x.
            inversion X.
*)
      (* * unshelve eexists; [ apply adty_new|]. *)
      *  apply adty_new.
        -- eapply dty_arrowl.
           ++ constructor.
           ++ assert (eAB : B=A) by now inversion t.
              pattern A.
              eapply (transport _ eAB ).
              (* apply ((IΔ _)..2 u). *)
              apply ((IΔ..2 _) u).
      (*
        --  intro x.
            inversion_clear x.
            inversion X.
*)
      (* * unshelve eexists; [ apply adty_old|]. *)
      * apply adty_new.
        -- unshelve eapply dty_arrowboth.
           ++  apply adty_old.
               exact (IΔ..1 A).
           ++ constructor.
           ++ destruct u.
              constructor.
    }
    intros B t.
    induction t as [D t| D t].
    + apply adtm_new.
      induction t; cbn.
      (* nouvelle variable *)
      constructor.
    + apply adtm_old.
      apply (IΔ..2 _ t).
Defined.

Definition ap := f_equal.
(* Inductive monunit : Type := montt. *)

Record ModelOne Γ :=
  { ctx_mod : Type;
    typ_mod : forall A : ctx_ty Γ, ctx_mod -> Type;
    term_mod : forall A (t:ctx_tm Γ A), forall γ, typ_mod A γ }.

Arguments ctx_mod {Γ} m : rename.
Arguments typ_mod {Γ} m _ _ : rename.
Arguments term_mod {Γ} m {_} _ _ : rename.
Record NextModel Γ (m:ModelOne Γ) (A:ctx_ty Γ) :=
  { next_arrowr : forall  (t: ctx_tm Γ A), forall γ : ctx_mod m, m.(typ_mod) A γ -> Type ;
    next_arrowl : forall  (u: ctx_tm Γ A), forall γ : ctx_mod m, m.(typ_mod) A γ -> Type ;
  next_arrowboth : forall γ : ctx_mod m, m.(typ_mod) A γ -> Type}.


Definition next_model Γ A (m:ModelOne Γ) (s:NextModel m A) : ModelOne (E Γ A).
  unshelve econstructor.
  - exact (sigT (m.(typ_mod) A)).
  - destruct 1 as [B|B].
    + (* ancien type *)
      exact (fun γ => m.(typ_mod) B γ..1).
    + (* nouveau type *)
      intro γ.
      induction B as [B t u|B t u|B t u].
      * assert (eAB : A = B) by now inversion u.
        destruct eAB.
        eapply (s.(next_arrowr) t _ γ..2).
      * assert (eAB : A = B) by now inversion t.
        destruct eAB.
        eapply (s.(next_arrowl) u _ γ..2).
      * destruct t.
        eapply (s.(next_arrowboth) _ γ..2).
  - intros B t.
    destruct t as [B t| B t].
    + (* nouveau terme *)
      destruct t.
      apply projT2.
    + exact (fun γ => m.(term_mod)  t γ..1).
Defined.

    
CoInductive rec_model Γ A m :=
  { msig : NextModel m A;
    mmod := @next_model Γ A m msig;
    msuite : forall B, @rec_model (E Γ A) B mmod }.

Definition model_empty (Tstar:Type) : ModelOne empty_ctx.
  unshelve econstructor.
  - exact unit.
  - induction 1.
    + contradiction.
    + exact (fun _ => Tstar).
    + destruct t; contradiction.
  - intros a t; destruct t; contradiction.
Defined.

Record full_model :=
  { mTstar : Type;
    mNext : forall B, rec_model B (model_empty mTstar) }.

Definition full_ctx_mod_aux (m:full_model) (Γ : PreCtx) (fΓ : FinCtx Γ) B :
  { m' : ModelOne Γ & rec_model (Γ := Γ) B m'}.
  induction fΓ.
  - eexists.
    apply m.(mNext).
  -  specialize (IHfΓ A).
     eexists.
     apply IHfΓ..2.(msuite).
Defined.

Definition full_ctx_mod (m:full_model)  (Γ : PreCtx) (fΓ : FinCtx Γ) : ModelOne Γ.
  destruct fΓ.
  - apply (model_empty m.(mTstar)).
  - set ( m' :=full_ctx_mod_aux m fΓ A).
    apply (mmod (m'..2 )).
Defined.

Record raw_ctx_mor Γ Δ :=
  { f_ty : ctx_ty Γ -> ctx_ty Δ;
    f_tm : forall A: ctx_ty Γ, ctx_tm _ A -> ctx_tm _ (f_ty A) }.

Definition E_raw_ctx_mor Γ Δ A (s :raw_ctx_mor Γ Δ) : raw_ctx_mor (E Γ A)
                                                                  (E Δ (f_ty s A)).
Proof.
  unshelve econstructor.
  - destruct 1 as [B|B].
    + (* ancien type *)
      apply adty_old.
      apply (f_ty s B).
    + (* nouveau type *)
      apply adty_new.
      induction B as [B t u|B t u| B t u].
      * eapply dty_arrowr.
        -- eapply (f_tm s).
           exact t.
        -- 
          inversion u.
           apply dtm_new.
      * eapply dty_arrowl.
        -- apply dtm_new.
        -- eapply (f_tm s).
           inversion t.
           exact u.
      * destruct t.
        unshelve eapply dty_arrowboth.
        -- apply adty_old.
           apply (f_ty s A).
        -- constructor.
        -- destruct u.
           constructor.
  - intro B.
    destruct 1 as [B t|B t].
    + destruct t.
      apply adtm_new.
      apply dtm_new.
    + apply adtm_old.
      apply (f_tm s _ t).
Defined.
Record modelone_mor Γ Δ (s:raw_ctx_mor Γ Δ) (mΓ:ModelOne Γ) (mΔ:ModelOne Δ) :=
  { f_ctx_mod : mΓ.(ctx_mod) -> mΔ.(ctx_mod);
    f_typ_mod : forall (A:ctx_ty Γ) γ, mΓ.(typ_mod) A γ -> mΔ.(typ_mod) (s.(f_ty) A)
                                                                  (f_ctx_mod γ);
    (* f_term_mod :forall A (t:ctx_tm Γ A) γ, *)
    (*     mΓ.(term_mod) t γ -> mΔ.(term_mod) (s.(f_tm) t) (f_ctx_mod γ) *)
  }.

Definition lift_sig Γ Δ A (s:raw_ctx_mor Γ Δ) (mΓ:ModelOne Γ)
           (mΔ:ModelOne Δ) (mor:modelone_mor s mΓ mΔ)
           (sΔ : NextModel mΔ (s.(f_ty) A)) : NextModel mΓ A.
Proof.
  unshelve econstructor.
  - intros t γ t_mod.
    exact (next_arrowr sΔ (f_tm s _ t) _ (mor.(f_typ_mod) _ _ t_mod)).
  - intros t γ t_mod.
    exact (next_arrowl sΔ (f_tm s _ t) _ (mor.(f_typ_mod) _ _ t_mod)).
  - intros  γ t_mod.
    exact (next_arrowboth sΔ  _ (mor.(f_typ_mod) _ _ t_mod)).
Defined.


Definition E_modelone_mor Γ Δ A (s:raw_ctx_mor Γ Δ) (mΓ:ModelOne Γ)
           (mΔ:ModelOne Δ) (mor:modelone_mor s mΓ mΔ)
           (sΔ : NextModel mΔ (s.(f_ty) A)) (sΓ := lift_sig A mor sΔ)  :
  modelone_mor (E_raw_ctx_mor ( A) s) (next_model sΓ)(next_model sΔ). 
Proof.
  unshelve econstructor.
  - cbn.
    intros γ.
    exists (mor.(f_ctx_mod) γ..1).
    apply (mor.(f_typ_mod) _ _ γ..2).
  - intros B γ sB.
    destruct B as [B|B].
    + (* ancien type *)
      apply (mor.(f_typ_mod)).
      assumption.
    + (* nouveau type *)
      destruct B as [B t u|B t u | B t u].
      *(*j'en suis la *)
        set (B' := adty_old _ _ _) in u,sB.
        set (u' := transport _ (eq_refl B') u).
        set (g:= typ_mod _ _ _).
        change u with u' in sB,g.
        subst u' g.
        revert sB.
        generalize (eq_refl B').
        unfold B' at 2.
        destruct u.
        intro e.
        injection e.
        intro e'.
        destruct e'.
        assert (he : e = eq_refl) by apply myadmit.
        subst e.
        apply id.
      * 
        set (B' := adty_old _ _ _) in t,sB.
        set (t' := transport _ (eq_refl B') t).
        set (g:= typ_mod _ _ _).
        change t with t' in sB,g.
        subst t' g.
        revert sB.
        generalize (eq_refl B').
        unfold B' at 2.
        destruct t.
        intro e.
        injection e.
        intro e'.
        destruct e'.
        assert (he : e = eq_refl) by apply myadmit.
        subst e.
        apply id.
      * destruct t.
        exact sB.
Defined.
     

CoFixpoint lift_rec_model Γ Δ A (s:raw_ctx_mor Γ Δ) (mΓ:ModelOne Γ)
           (mΔ:ModelOne Δ) (mor:modelone_mor s mΓ mΔ)
           (yop : rec_model (s.(f_ty) A) mΔ) :
  rec_model A mΓ.
unshelve econstructor.
- exact (lift_sig A mor yop.(msig)).
- intro B.
  cbn.
  eapply (lift_rec_model _ (E Δ (f_ty s A))).
  + eapply E_modelone_mor.
  + apply yop.(msuite).
Defined.

  Definition arrow_simplctx := ctx_arrow _ t_simplctx  u_simplctx.


Definition shift_full_model (m:full_model) 
           (γ0 : ctx_mod (full_ctx_mod m is_fin_simplctx  ) ) : full_model.
  unshelve econstructor.
  - cbn in γ0.
    eapply (typ_mod (full_ctx_mod m is_fin_simplctx  )).
    exact arrow_simplctx.
    exact γ0.
  - intros B.
    unshelve eapply (lift_rec_model (Δ := simplctx)).
    + (* ctx_mor empty -> simpl *)
      unshelve econstructor.
      * clear B.
        induction 1 ; try contradiction.
        -- (* star *)
          exact arrow_simplctx.
        -- (* arrow *)
          destruct t; contradiction.
      *  intros ? t; destruct t; contradiction.
    + (* la je ne usi pas sur... *)
      apply (full_ctx_mod  m (Γ :=simplctx)).
      apply is_fin_simplctx.
    + (* modelone_mor modele one mor *)
      unshelve econstructor.
      * (* ctx mod *)
        intros ?.
        cbn.
        exact γ0.
      * (* typ mod *)
        clear B.
        intros A γ sA.
        destruct A.
        -- contradiction.
        -- (* star *)
          exact sA.
        -- destruct t; contradiction.
    + cbn.
      unshelve refine (let monmod :=
                  full_ctx_mod_aux m is_fin_simplctx 
                                   in _).
      eapply ((monmod _)..2).
Defined.

(* Version pour les gset : l'interprétation des types renvoie un gset *)
Record gModelOne Γ :=
  { gctx_mod : Type;
    gtyp_mod : forall A : ctx_ty Γ, gctx_mod -> gset;
    gterm_mod : forall A (t:ctx_tm Γ A), forall γ, objects (gtyp_mod A γ) }.


Arguments gctx_mod {Γ} m : rename.
Arguments gtyp_mod {Γ} m _ _ : rename.
Arguments gterm_mod {Γ} m {_} _ _ : rename.

Definition gModelOne_to_bare Γ (m:gModelOne Γ) : ModelOne Γ :=
  {| ctx_mod := gctx_mod m;
     typ_mod := fun A γ => objects (gtyp_mod m A γ);
     term_mod := @gterm_mod _ m |}.

Definition simpl_NextModel Γ (m:ModelOne Γ) (A:ctx_ty Γ) :=
  forall γ : ctx_mod m,  m.(typ_mod) A γ -> m.(typ_mod) A γ -> Type.

Definition simpl_NextModel_to_real Γ (m:ModelOne Γ) (A:ctx_ty Γ)
           (m' : simpl_NextModel m A) : NextModel m A :=
  {| next_arrowr := fun t γ su => m' γ (m.(term_mod) t γ) su;
     next_arrowl := fun u γ st => m' γ st (m.(term_mod) u γ);
     next_arrowboth := fun γ st => m' γ st st |}.



Definition simpl_gNextModel Γ (m:ModelOne Γ) (A:ctx_ty Γ) :=
  forall γ : ctx_mod m,  m.(typ_mod) A γ -> m.(typ_mod) A γ -> gset.

Definition simpl_gNextModel_to_simpl_real Γ (m:gModelOne Γ) (A:ctx_ty Γ)
           (m' : simpl_gNextModel (gModelOne_to_bare m) A) : simpl_NextModel
                                                               (gModelOne_to_bare m) A :=
  fun γ x y => objects (m' γ x y).
Definition infer_gNextModel Γ A (m:gModelOne Γ) :
  simpl_gNextModel (gModelOne_to_bare m) A :=
  fun γ x y => ((gtyp_mod m A γ) x y).
Record gNextModel Γ (m:gModelOne Γ) (A:ctx_ty Γ) :=
  { gnext_arrowr : forall  (t: ctx_tm Γ A), forall γ : gctx_mod m, objects (m.(gtyp_mod) A γ) -> gset ;
    gnext_arrowl : forall  (u: ctx_tm Γ A), forall γ : gctx_mod m, objects (m.(gtyp_mod) A γ) -> gset ;
    gnext_arrowboth : forall γ : gctx_mod m, objects (m.(gtyp_mod) A γ) -> gset}.
Definition simpl_gNextModel_to_real Γ (m:gModelOne Γ) (A:ctx_ty Γ)
           (m' : simpl_gNextModel (gModelOne_to_bare m) A) : gNextModel m A :=
  {| gnext_arrowr := fun t γ su => m' γ (m.(gterm_mod) t γ) su;
     gnext_arrowl := fun u γ st => m' γ st (m.(gterm_mod) u γ);
     gnext_arrowboth := fun γ st => m' γ st st |}.
  


(* quasiment un copié collé de next_model *)
Definition gnext_model Γ A (m:gModelOne Γ) (s:gNextModel m A) : gModelOne (E Γ A).
  unshelve econstructor.
  - exact (sigT (fun x => objects (m.(gtyp_mod) A x))).
  - destruct 1 as [B|B].
    + (* ancien type *)
      exact (fun γ => m.(gtyp_mod) B γ..1).
    + (* nouveau type *)
      intro γ.
      induction B as [B t u|B t u|B t u].
      * assert (eAB : A = B) by now inversion u.
        destruct eAB.
        eapply (s.(gnext_arrowr) t _ γ..2).
      * assert (eAB : A = B) by now inversion t.
        destruct eAB.
        eapply (s.(gnext_arrowl) u _ γ..2).
      * destruct t.
        eapply (s.(gnext_arrowboth) _ γ..2).
  - intros B t.
    destruct t as [B t| B t].
    + (* nouveau terme *)
      destruct t.
      apply projT2.
    + exact (fun γ => m.(gterm_mod)  t γ..1).
Defined.

Definition raw_ctx_mor_id Γ : raw_ctx_mor Γ Γ :=
  {| f_ty := fun x => x;
     f_tm := fun A t => t |}.

Definition gmodel1  Γ B mg : ModelOne (E Γ B) :=
  gModelOne_to_bare ( gnext_model (simpl_gNextModel_to_real (infer_gNextModel B mg))).

Definition gmodel2  Γ B mg : ModelOne (E Γ B) :=
    (next_model (simpl_NextModel_to_real (simpl_gNextModel_to_simpl_real (infer_gNextModel B mg)))).

(* sans doute il y a moyen de définir ça sans passer par le morphisme gmodel1 -> gmodel2
mais j'ai la flemme d'y refélcéhir *)
Definition mor_gmodel12 Γ B mg : modelone_mor (raw_ctx_mor_id (E Γ B))
                                              (gmodel2 B mg) (gmodel1 B mg).
  unshelve econstructor.
  easy.
  intros A γ.
  destruct A as [A|A].
  - (* ancien type *)
    easy.
  - (* nouveau type *)
    induction A.
    +
        set (B' := adty_old _ _ _) in *.
        set (u' := transport _ (eq_refl B') u).
        change u with u'.
        subst u' .
        generalize (eq_refl B').
        unfold B' at 2.
        destruct u.
        intro e.
        injection e.
        intro e'.
        destruct e'.
        assert (he : e = eq_refl) by apply myadmit.
        subst e.
        cbn.
        easy.
    +
        set (B' := adty_old _ _ _) in *.
        set (u' := transport _ (eq_refl B') t).
        change t with u'.
        subst u' .
        generalize (eq_refl B').
        unfold B' at 2.
        destruct t.
        intro e.
        injection e.
        intro e'.
        destruct e'.
        assert (he : e = eq_refl) by apply myadmit.
        subst e.
        cbn.
        easy.
    + now destruct t.
      Defined.


CoFixpoint gset_to_recmodel_aux Γ (B:ctx_ty Γ) (mg : gModelOne Γ):
  rec_model B (gModelOne_to_bare mg).
  unshelve econstructor.
  -  eapply simpl_NextModel_to_real.
     eapply simpl_gNextModel_to_simpl_real.
     apply infer_gNextModel.
  - intros A.
    set (mg' := gnext_model (A:=B) (m:=mg )
                            (simpl_gNextModel_to_real (infer_gNextModel _ mg))).
    set (suite := (gset_to_recmodel_aux _ A mg')).
    apply  myadmit.
    Defined.
    eapply (lift_rec_model (Δ:= E Γ B) A).
    eapply (mor_gmodel12).
    exact suite.
  Defined.
  mg' := gnext_model (simpl_gNextModel_to_real (infer_gNextModel B mg)) : gModelOne (E Γ B)
                                                                                    e
    (next_model (simpl_NextModel_to_real (simpl_gNextModel_to_simpl_real (infer_gNextModel B mg))))
    Set Printing Implicit.
  :w
     kDefinition gset_to_full_model (g:gset) : full_model.
      

Definition lift_sig Γ Δ A (s:raw_ctx_mor Γ Δ) (mΓ:ModelOne Γ)
           (mΔ:ModelOne Δ) (mor:modelone_mor s mΓ mΔ)
           (sΔ : NextModel mΔ (s.(f_ty) A)) : NextModel mΓ A.

Definition shift_ctx_mor Γ (fΓ:FinCtx Γ) : raw_ctx_mor Γ (shift_ctx fΓ)..1.
   econstructor.
  exact (snd (shift_ctx fΓ)..2)..2.
Defined.

(*


Definition raw_subst_modelOne Γ Δ (s:raw_subst Γ Δ) (s'
           (m:ModelOne Δ) : ModelOne Γ.
  unshelve econstructor.
  -
*)
Definition shift_rec_model Γ (fΓ : FinCtx Γ) (B:ctx_ty Γ)
           (m: ModelOne fΓ)
           (* (m:rec_model B (full_ctx_mod fΓ)) *)
           (m' : ModelOne (shift_ctx fΓ)..1)
           (mor : modelone_mor (shift_ctx_mor fΓ) m m')
           (γ0 : ctx_mod (full_ctx_mod m is_fin_simplctx  ) )
  : { m' : ModelOne (shift_ctx fΓ)..1 &
           { m'' : ModelOne Γ &
                   (rec_model B m'') * (modelone_mor (shift_ctx_mor fΓ) m'' m')
                                         * 
                         NextModel m'
                                   (f_ty (shift_ctx_mor fΓ) B)
    }}%type.
Proof.
Admitted.

Definition shift_rec_model Γ (fΓ : FinCtx Γ) (B:ctx_ty Γ) (m:full_model)
           (γ0 : ctx_mod (full_ctx_mod m is_fin_simplctx  ) )
  induction fΓ.
  - unshelve eexists.
    + unshelve econstructor.
      * exact
          (typ_mod (full_ctx_mod m is_fin_simplctx) (ctx_arrow _ t_simplctx u_simplctx) γ0).
      *


Definition shift_rec_model Γ (fΓ : FinCtx Γ) (B:ctx_ty Γ) (m:full_model)
           (γ0 : ctx_mod (full_ctx_mod m is_fin_simplctx  ) )
  : { m' : ModelOne (shift_ctx fΓ)..1 & NextModel m'
                                                  ((snd (shift_ctx fΓ)..2)..1 B)}.
(* nouveau model & ancien model *)

Definition shift_rec_model Γ (fΓ : FinCtx Γ) (B:ctx_ty Γ) (m:full_model)
           (γ0 : ctx_mod (full_ctx_mod m is_fin_simplctx  ) )
            : { m' : _ & NextModel m' B}. (* nouveau model & ancien model *)
  set (Γ' := shift_ctx fΓ).
  induction fΓ.
  - admit.
  - unshelve eexists.
    unshelve eexists.
    + apply  model_empty.
      
    

Record ModelTwo :=
  { star_mod : Type;
    arrow_mod :forall Γ A (t u:ctx_tm Γ A), FinCtx Γ ->
        forall (sΓ: Type) (sA : sΓ -> Type) (st su : forall γ, sA γ), sΓ -> Type
  }.

(* Record Model := { all_mod :> forall Γ, FinCtx Γ -> ModelOne Γ; *)
(*                  nil_unit : ctx_mod (all_mod fin_nil ) = unit }. *)
Definition one_to_two (m:forall Γ, FinCtx Γ -> ModelOne Γ) : ModelTwo.
  unshelve econstructor.
  - set (m' :=  m _ (fin_cons (ctx_star _) fin_nil)).
    apply (ctx_mod m').
  - intros Γ A t u fΓ sΓ sA st su .
    intro γ.
    refine { e : sΓ = ctx_mod (m _ fΓ) &
                typ_mod (m _ fΓ) (ctx_arrow Γ t u) (transport _ e γ) }.
    eauto with typeclass_instances.
Defined.

Definition two_to_one (m:ModelTwo) : forall Γ, FinCtx Γ -> ModelOne Γ.
   intro Γ.
    induction 1 as [|Γ A fΓ IHΓ].
  (* unshelve econstructor. *)
    + (* contexte vide *)
      unshelve econstructor.
      * exact unit.
      * induction 1.
        -- contradiction.
        -- exact (fun _ => (star_mod m)).
        -- destruct t; contradiction.
      * intros A t.
        destruct t; contradiction.
    + set (sΓ := (sigT (IHΓ.( typ_mod) A))).
      unshelve econstructor.
      -- apply sΓ.
      -- induction 1 as [B|B].
         ++ (* ancien type *)
           exact (fun x => IHΓ.(typ_mod) B x..1).
         ++ (* nouveau type *)
           intro γ.
           induction B as [B t u|B t u| B t u].
           ** simple refine (@arrow_mod m (E Γ A) (adty_old _ A B) _ _ _ 
                                          (sΓ )
                                          (fun γ =>  (IHΓ.(typ_mod) B γ..1))
                                          _ _ γ
                               ).
              --- apply adtm_old.
                  exact t.
              --- apply adtm_new.
                  clear -u.
                  inversion u.
                  constructor.
              --- now constructor.
              --- exact (fun γ => IHΓ.(term_mod)  t γ..1).
              --- intro γ'.
                  inversion u.
                  pattern B.
                  eapply transport.
                  eassumption.
                  exact γ'..2.
           ** simple refine (@arrow_mod m (E Γ A) (adty_old _ A B) _ _ _ 
                                          (sΓ )
                                          (fun γ =>  (IHΓ.(typ_mod) B γ..1))
                                          _ _ γ
                               ).
              --- apply adtm_new.
                  clear -t.
                  inversion t.
                  constructor.
              --- apply adtm_old.
                  exact u.
              --- now constructor.
              --- intro γ'.
                  inversion t.
                  pattern B.
                  eapply transport.
                  eassumption.
                  exact γ'..2.
              --- exact (fun γ => IHΓ.(term_mod)  u γ..1).
           ** destruct t.
              set (B:=A).
             simple refine (@arrow_mod m (E Γ A) (adty_old _ A B) _ _ _
                                          (sΓ )
                                          (fun γ =>  (IHΓ.(typ_mod) B γ..1))
                                          _ _ γ
                               ).
              --- apply adtm_new.
                  constructor.
              --- apply adtm_new.
                  constructor.
              --- now constructor.
              --- exact (fun γ' =>projT2 γ').
              --- exact (fun γ' =>projT2 γ').
      -- intro B.
         induction 1 as [D t|D t].
         ++ (* nouveau terme *)
           destruct t.
           cbn.
           apply projT2.
         ++ (* ancien terme *)
           cbn.
           exact (fun γ => IHΓ.(term_mod) t  γ..1).
Defined.

(* J'ai donc une fonction one_one de ModelOne vers ModelOne par composition de
one_to_two et de two_to_one. Maintenant j'ai envie de dire qu'un modèle
est un ModelOne muni d'une fonction de one_one vers lui-même.

Mais pour que ça marche j'aurai besoin d'UIP *)

(*
Class Model := 
  { (* ctxempty_mod : Type; *)
    (* ctxcons_mod : forall Γ (fΓ : FinCtx Γ) (A:ctx_ty Γ), Type; *)
    ctx_mod : forall Γ, FinCtx Γ -> {
                    } ;
    (* ctx_mod : forall Γ, FinCtx Γ -> Type := *)
    (*   @FinCtx_rect _ unit (fun Γ A f _ => ctxcons_mod  f A); *)

    (* forall Γ, FinCtx Γ -> Type; *)
    (* star_mod : Type; *)
    typ_mod : forall Γ (fΓ  :FinCtx Γ) (A : ctx_ty Γ), ctx_mod  fΓ -> Type;
    typ_term:  forall Γ (fΓ  :FinCtx Γ) (A : ctx_ty Γ) (t:ctx_tm _ A)
                 (γ : ctx_mod  fΓ), typ_mod (* fΓ  *)A γ
        (* ctx_mod fΓ; *)


    (* unit_eq : ctx_mod fin_nil = unit; *)

  }.
*)

  Variable (m:Model).
  (* (x y: typ_mod (all_mod m fin_nil) (ctx_star _) *)
  (*                                      (transport (fun x => x) (eq_sym (nil_unit m)) tt )) *)
  Definition shift_model (g:ctx_mod (m simplctx is_fin_simplctx))  : Model.
    unshelve econstructor.
    - intros Γ fΓ.
      induction fΓ.
      + (* contexte vide *)
        unshelve econstructor.
        * exact unit.
        * induction 1.
          -- contradiction.
          -- (* star *)
            set (Δ := shift_ctx fin_nil).
            intros _.
            apply (typ_mod (all_mod m (fst Δ..2))).
            ++ apply (snd Δ..2)..1.
               refine (ctx_star _).
            ++ exact g.
          -- destruct t; contradiction.
        * intro A.
          destruct 1 ; contradiction.
      + (* Extension de contexte *)
        unshelve econstructor.
        * apply (sigT (typ_mod IHfΓ A)).
        * destruct 1 as [B|B].
          -- (* ancien type *)
            intro γ.
            apply (typ_mod IHfΓ A γ..1).
          -- (* nouveau type *)
            
             

            cbn in Δ.

  (* Definition shift_model  (x y: typ_mod fin_nil (ctx_star _) *)
  (*                                      tt ) : Model. *)
    unshelve econstructor .
    - intros Γ fΓ A.
      set (shift := shift_ctx fΓ).
      unshelve eapply (ctxcons_mod  _ ((snd shift..2)..1 A)).
      exact (fst shift..2).
    - intros Γ fΓ A γ.
      set (shift := shift_ctx fΓ).

  set (h:= ctx_mod (is_fin_simplctx)).
  set (tar := ctx_arrow _ t_simplctx u_simplctx).
  set (h' := typ_mod (is_fin_simplctx) tar  ).
  unshelve econstructor.
  - 

  Definition 
End Model_GSet.
  


  (*
*************************



Tout ce qui vient après est DEPRECATED












************************
   *)
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
 stmΓ := fun (_ : unit) (t : False) (_ : unit) => False_rect (Tstar m) t |}. Section model.

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

Inductive is_psTerm : forall Γ (A:ctx_ty Γ), ctx_tm _ A -> Type :=
  is_ps_init : is_psTerm (E empty_star_ctx tt) tt (New_fv _ _ _)
| is_ps_ar_end Γ A x y f : is_psTerm (TT Γ) (ty_arrow (ctx_ty Γ) (ctx_tm Γ) A x y) f
                       -> is_psTerm Γ A y


| is_ps_tt Γ A t : is_psTerm (TT Γ) (ty_fv _ _ A) (tm_fv  _ _ _ t)
    (* peut etre inutile *)

| is_ps_ar Γ A x : is_psTerm Γ A x ->
                   is_psTerm 
                     (E (TT (E Γ A))
                                (ty_arrow
                                   (ctx_ty (E Γ A))
                                   (ctx_tm (E Γ A))
                                   A
                                   (Some_fv 
                                      (ctx_ty Γ)
                                      (ctx_tm Γ )
                                      _ _ x
                                   )
                                   (New_fv (ctx_ty Γ)
                                           (ctx_tm Γ )
                                           A)
                             ))
                     _
                     (New_fv (ctx_ty (TT (E Γ A)))
                             (ctx_tm (TT (E Γ A)))
                             _).

(*
Inductive is_psTerm : forall Γ (A:ctx_ty Γ), ctx_tm _ A -> Type :=
  is_ps_init : is_psTerm (E empty_star_ctx tt) tt (New_fv _ _ _)
| is_ps_ar_end Γ A x y f : is_psTerm (TT Γ) (ty_arrow (ctx_ty Γ) (ctx_tm Γ) A x y) f
                                     -> finCtx Γ (* je suis obligé de rajouter explicitement
cette hypothèse car sinon je ne peux pas le montrer à moins de supposer funext ou un truc du genre *)
                       -> is_psTerm Γ A y


| is_ps_tt Γ A t : finCtx Γ -> is_psTerm (TT Γ) (ty_fv _ _ A) (tm_fv  _ _ _ t)
    (* peut etre inutile *)

| is_ps_ar Γ A x : is_psTerm Γ A x ->
                   is_psTerm 
                     (E (TT (E Γ A))
                                (ty_arrow
                                   (ctx_ty (E Γ A))
                                   (ctx_tm (E Γ A))
                                   A
                                   (Some_fv 
                                      (ctx_ty Γ)
                                      (ctx_tm Γ )
                                      _ _ x
                                   )
                                   (New_fv (ctx_ty Γ)
                                           (ctx_tm Γ )
                                           A)
                             ))
                     _
                     (New_fv (ctx_ty (TT (E Γ A)))
                             (ctx_tm (TT (E Γ A)))
                             _).
*)

Fixpoint star_from_finCtx Γ (h:finCtx Γ) : ctx_ty Γ :=
  match h with
  (* | fin_empty => (* semTTΓ _ *) empty_semantique (* m *) *)
  | fin_empty => tt
  | fin_E c _ h => star_from_finCtx c h
  | fin_TT c h => ty_fv _ _ (star_from_finCtx c h)
  end.


(*
Fixpoint finTT_is_fin Γ (h:finCtx (TT Γ)) : finCtx Γ.

  remember (TT Γ) as Γ' eqn:e in h .
  destruct h.
  - apply myadmit.
  -
*)
(*
Fixpoint psTerm_is_fin Γ t A (h:is_psTerm Γ t A) : finCtx Γ.
  destruct h.
  - repeat constructor.
  - assert (h':finCtx (TT Γ)).
    eapply psTerm_is_fin.
    exact h.
    remember (TT Γ) as Γ' eqn:e in h' .
    assert(e':=f_equal ctx_ty e); cbn in e'.
    destruct h'; auto; cbn in e'.
    + apply myadmit.
    +
      cbn in e.
      discriminate.

    cbn in e.
    apply f_equal
    destruct e.
    discriminate.
    inversion h'.
Definition is
*)

Fixpoint is_var Γ A (h:finCtx Γ) (x:ctx_tm Γ A) {struct h} : bool.
  destruct h.
  - now exfalso.
  - destruct x.
    + apply is_var in c0.
      exact c0.
      exact h.
    + exact true.
  - destruct x.
    eapply is_var.
    exact h.
    exact v.
Defined.

Module IsPsCtx.
  Record t Γ :=
    { isFin : finCtx Γ;
      (* obligé de rajouter explicitmenet cette hypothèse *)
      x: _;
      ty_x_star : is_var Γ (star_from_finCtx Γ isFin) isFin x = true}.
End IsPsCtx.

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
    
