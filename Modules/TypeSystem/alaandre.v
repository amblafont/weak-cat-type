
Set Implicit Arguments.
Axiom myadmit : forall (A:Type) , A.
(* Inutile  ??? Il suffit de définir l'extension de contexte non ?*)
Inductive Ty (ty : Type) (term : ty -> Type) : Type :=
| ty_eta : ty -> Ty term 
| ty_star : Ty term
| ty_arrow (A : Ty term) (t u: Term A):  Ty term
with Term (ty : Type) (term : ty -> Type) : Ty ty term -> Type :=
     | term_eta (a : ty) (v : term a) : Term (ty_eta a) .

Record Fam := Build_Fam { base : Type; fam :> base -> Type}.

Definition section A (P : A -> Type) := forall a, P a.

Definition TT (c : Fam) : Fam := Build_Fam (Term (term := c)).

Record Fam_Hom (c d : Fam) :=
  Build_Fam_Hom { base_hom : base c -> base d ;
                  fam_hom : forall x : base c, c x -> d (base_hom x) }.

Definition TAlg (c : Fam) := Fam_Hom (TT c) c.

Class FAlg (c : Fam) :=
  Build_FAlg
    { ctx_arrow : forall A (t u : c A), base c;
    ctx_star : base c}.

Arguments ctx_arrow  _ [_ _] _ _ .
Arguments ctx_star  _ [_].


Instance AlgTT (c : Fam) : FAlg (TT c) :=
  Build_FAlg (TT c) (@ty_arrow (base c) c) (ty_star c).


Section Derivation.
  (* On veut étendre le contexte en ajoutant une variable de type B *)
  Variables (ty : Type) (term : ty -> Type) (B : ty).

  (* extTy : soit un ancien type, soit un nouveau type qu'on peut former grace
à B
 extTm : pareil mais pour les termes
 extTy_New : les nouveaux types qu'on peut former
 extTm_New : les nouveaux termes qu'on peut former
   *)
  Inductive extTy : Type :=
  | eTy_old : ty -> extTy
  | eTy_new : extTy_New -> extTy
  with extTm : extTy -> Type :=
       | eTm_new A : extTm_New A -> extTm A
       | eTm_old A : term A -> extTm (eTy_old A)
  with extTy_New : Type :=
       | eTy_arrowr A (t : term A) (u : extTm_New (eTy_old A)) : extTy_New
       | eTy_arrowl A (t : extTm_New (eTy_old A)) (u : term A) : extTy_New
       | eTy_arrowboth A (t : extTm_New A) (u : extTm_New A) : extTy_New
  with extTm_New : extTy -> Type := 
  | eTm_some : extTm_New (eTy_old B).
End Derivation.


  Definition E (c : Fam) (a : base c) : Fam :=
    Build_Fam (base := extTy c a) (@extTm _ _ _).

  Instance AlgE (c:Fam) {ac : FAlg  c} (A : base c) :
    FAlg (E c A).
  unshelve econstructor.
  - intros B t u.
    destruct t as [C t | C t].
    + apply eTy_new.
      destruct u as [ C u | C u].
      * apply (eTy_arrowboth t u).
      * apply (eTy_arrowl t u).
    + remember ( eTy_old _ _ _) as C' eqn:eC in u.
      destruct u as [ C' u | C' u].
      * apply eTy_new. subst. apply (eTy_arrowr t u).
      * apply eTy_old.
        apply (ctx_arrow _ (A:=C) t).
        injection eC.
        destruct 1.
        exact u.
  - apply eTy_old.
    apply (ctx_star c).
  Defined.

Definition empty_prectx : Fam := Build_Fam (base := False) (fun _ => False).
Definition empty_ctx : Fam := TT empty_prectx.

Inductive FinCtx : Fam -> Type := 
  fin_nil : FinCtx empty_ctx
| fin_cons C A :  FinCtx C -> FinCtx (E C A).

Fixpoint algFinCtx C (w:FinCtx C) : FAlg C.
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

 (*
Commenté car inutile
  Lemma to_type C (w:FinCtx C) :
    { sΓ : Type & forall ty : base C, { sA : sΓ -> gset &
                                               forall tm : C ty, forall γ, objects(sA γ)}}.
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
        remember ( eTy_old _ _ _) as C' eqn:eC.
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
*)

  End GSet_Model.



Section Model_GSet.
  Definition simplctx :=  E ( E empty_ctx (ctx_star _)) (ctx_star _).
  Lemma is_fin_simplctx : FinCtx simplctx.
    repeat constructor.
  Defined.

Definition t_simplctx : simplctx (ctx_star _) (* (ty_fv _ _ tt) *).
  apply eTm_old.
  apply eTm_new.
  constructor.
Defined.

Definition u_simplctx : simplctx (ctx_star _) (* (ty_fv _ _ tt) *).
  apply eTm_new.
  constructor.
Defined.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  eq_rect x P u y p.
(* Class Ctx := { ctx_pre : Fam; ctx_alg : FAlg ctx_pre}. *)
(* Existing Instance ctx_alg. *)
Record ctxMor Γ Δ :=
  { f_ty : base Γ -> base Δ;
    f_tm : forall A: base Γ, Γ A -> Δ (f_ty A) }.

Definition ctxMor_id Γ : ctxMor Γ Γ :=
  {| f_ty := fun x => x;
     f_tm := fun A t => t |}.

(*
but construire Γ' = x,y:*, Δ où Δ est Γ où * est remplacé par x ->* y dans Γ

Finalement, peut etre inutile
En fait je ne l'utilise qu'une seule fois sur le contexte vide
*)
Definition shift_ctx (Γ : Fam) (fΓ : FinCtx Γ) :
  {Δ : Fam & FinCtx Δ & ctxMor Γ Δ}.
  induction fΓ.
  - econstructor.
    exact is_fin_simplctx.
    unshelve econstructor.
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
  - destruct IHfΓ as [Δ fΔ IΔ].
    exists (E Δ (IΔ.(f_ty) A)).
    (* exists (E Δ (IΔ A)..1). *)
    now constructor.
    (* intro B. *)
    unshelve econstructor.
    {
    intro B.
    induction B as [B|B].
    + (* old type *)
      (* unshelve eexists. *)
      * apply eTy_old.
        exact (IΔ.(f_ty) B).
        (* exact (IΔ B)..1. *)
        (*
      * remember (eTy_old _ _ _) as D eqn:eD.
        destruct 1 as [D t|D t].
        -- (* nouvelle variable *)
          apply eTm_new.
          destruct t.
          injection eD; intro eAB.
          pattern B.
          eapply (transport _ eAB).
          constructor.
        -- (* ancienne variable *)
          apply eTm_old.
          apply (IΔ _)..2.
          injection eD; intro eBD.
          pattern B.
          apply (transport _ eBD t).
         *)

    + (* new type *)
      induction B as [B t u|B t u| B t u].
      (* * unshelve eexists; [ apply eTy_new|]. *)
      *  apply eTy_new.
        -- eapply eTy_arrowr.
           (* ++ apply ((IΔ _)..2 t). *)
           ++ apply ((IΔ.(f_tm) _ t)).
           ++ assert (eAB : A=B) by now inversion u.
              pattern B.
              eapply (transport _ eAB).
              constructor.
              (*
         -- intro x.
            inversion_clear x.
            inversion X.
*)
      (* * unshelve eexists; [ apply eTy_new|]. *)
      *  apply eTy_new.
        -- eapply eTy_arrowl.
           ++ constructor.
           ++ assert (eAB : B=A) by now inversion t.
              pattern A.
              eapply (transport _ eAB ).
              (* apply ((IΔ _)..2 u). *)
              apply ((IΔ.(f_tm) _) u).
      (*
        --  intro x.
            inversion_clear x.
            inversion X.
*)
      (* * unshelve eexists; [ apply eTy_old|]. *)
      * apply eTy_new.
        -- unshelve eapply eTy_arrowboth.
           ++  apply eTy_old.
               exact (IΔ.(f_ty) A).
           ++ constructor.
           ++ destruct u.
              constructor.
    }
    intros B t.
    induction t as [D t| D t].
    + apply eTm_new.
      induction t; cbn.
      (* nouvelle variable *)
      constructor.
    + apply eTm_old.
      apply (IΔ.(f_tm) _ t).
Defined.

Definition ap := f_equal.
(* Inductive monunit : Type := montt. *)

Record Model_at Γ :=
  { mod_ctx : Type;
    mod_typ : base Γ -> mod_ctx -> Type; 
    mod_term : forall A, Γ A -> section (mod_typ A) }.

Arguments mod_ctx {Γ} m : rename.
Arguments mod_typ {Γ} m _ _ : rename.
Arguments mod_term {Γ} m {_} _ _ : rename.

Record Model_ext Γ (m : Model_at Γ) (A : base Γ) :=
  {
    (* mext_arrowr : forall B (t : Γ B) (u : extTm_New (eTy_old Γ A B)), *)
    (*   forall γ : mod_ctx m, m.(mod_typ) A γ -> Type ; *)
    mext_arrowr : forall (t: Γ A), forall γ : mod_ctx m, m.(mod_typ) A γ -> Type ;
    mext_arrowl : forall (u: Γ A), forall γ : mod_ctx m, m.(mod_typ) A γ -> Type ;
    mext_arrowboth : forall γ : mod_ctx m, m.(mod_typ) A γ -> Type}.


Definition next_model Γ A (m:Model_at Γ) (s:Model_ext m A) : Model_at (E Γ A).
  unshelve econstructor.
  - exact (sigT (m.(mod_typ) A)).
  - destruct 1 as [B|B].
    + (* ancien type *)
      exact (fun γ => m.(mod_typ) B γ..1).
    + (* nouveau type *)
      intro γ.
      induction B as [B t u|B t u|B t u].
      * assert (eAB : A = B) by now inversion u.
        destruct eAB.
        eapply (s.(mext_arrowr) t _ γ..2).
      * assert (eAB : A = B) by now inversion t.
        destruct eAB.
        eapply (s.(mext_arrowl) u _  γ..2).
      * destruct t.
        eapply (s.(mext_arrowboth) _  γ..2).
  - intros B t.
    destruct t as [B t| B t].
    + (* nouveau terme *)
      destruct t.
      exact (fun x => x..2).
    + exact (fun γ => m.(mod_term)  t γ..1).
Defined.

    
CoInductive rec_model Γ A m :=
  { mext : Model_ext m A;
    mmod := @next_model Γ A m mext;
    msuite : forall B, @rec_model (E Γ A) B mmod }.

Definition model_empty (Tstar:Type) : Model_at empty_ctx.
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

Definition full_mod_ctx_aux (m:full_model) (Γ : Fam) (fΓ : FinCtx Γ) B :
  { m' : Model_at Γ & rec_model (Γ := Γ) B m'}.
  induction fΓ.
  - eexists.
    apply m.(mNext).
  -  specialize (IHfΓ A).
     eexists.
     apply IHfΓ..2.(msuite).
Defined.

Definition full_mod_ctx (m:full_model)  (Γ : Fam) (fΓ : FinCtx Γ) : Model_at Γ.
  destruct fΓ.
  - apply (model_empty m.(mTstar)).
  - set ( m' :=full_mod_ctx_aux m fΓ A).
    apply (mmod (m'..2 )).
Defined.


Definition E_ctxMor Γ Δ A (s :ctxMor Γ Δ) : ctxMor (E Γ A)
                                                                  (E Δ (f_ty s A)).
Proof.
  unshelve econstructor.
  - destruct 1 as [B|B].
    + (* ancien type *)
      apply eTy_old.
      apply (f_ty s B).
    + (* nouveau type *)
      apply eTy_new.
      induction B as [B t u|B t u| B t u].
      * eapply eTy_arrowr.
        -- eapply (f_tm s).
           exact t.
        -- 
          inversion u.
           apply eTm_some.
      * eapply eTy_arrowl.
        -- apply eTm_some.
        -- eapply (f_tm s).
           inversion t.
           exact u.
      * destruct t.
        unshelve eapply eTy_arrowboth.
        -- apply eTy_old.
           apply (f_ty s A).
        -- constructor.
        -- destruct u.
           constructor.
  - intro B.
    destruct 1 as [B t|B t].
    + destruct t.
      apply eTm_new.
      apply eTm_some.
    + apply eTm_old.
      apply (f_tm s _ t).
Defined.
Record Model_at_mor Γ Δ (s:ctxMor Γ Δ) (mΓ:Model_at Γ) (mΔ:Model_at Δ) :=
  { f_mod_ctx : mΓ.(mod_ctx) -> mΔ.(mod_ctx);
    f_mod_typ : forall (A:base Γ) γ, mΓ.(mod_typ) A γ -> mΔ.(mod_typ) (s.(f_ty) A)
                                                                  (f_mod_ctx γ);
    (* f_mod_term :forall A (t:Γ A) γ, *)
    (*     mΓ.(mod_term) t γ -> mΔ.(mod_term) (s.(f_tm) t) (f_mod_ctx γ) *)
  }.

Definition lift_ext Γ Δ A (s:ctxMor Γ Δ) (mΓ:Model_at Γ)
           (mΔ:Model_at Δ) (mor:Model_at_mor s mΓ mΔ)
           (sΔ : Model_ext mΔ (s.(f_ty) A)) : Model_ext mΓ A.
Proof.
  unshelve econstructor.
  - intros t γ t_mod.
    exact (mext_arrowr sΔ (f_tm s _ t) _ (mor.(f_mod_typ) _ _ t_mod)).
  - intros t γ t_mod.
    exact (mext_arrowl sΔ (f_tm s _ t) _ (mor.(f_mod_typ) _ _ t_mod)).
  - intros  γ t_mod.
    exact (mext_arrowboth sΔ  _ (mor.(f_mod_typ) _ _ t_mod)).
Defined.


Definition E_Model_at_mor Γ Δ A (s:ctxMor Γ Δ) (mΓ:Model_at Γ)
           (mΔ:Model_at Δ) (mor:Model_at_mor s mΓ mΔ)
           (sΔ : Model_ext mΔ (s.(f_ty) A)) (sΓ := lift_ext A mor sΔ)  :
  Model_at_mor (E_ctxMor ( A) s) (next_model sΓ)(next_model sΔ). 
Proof.
  unshelve econstructor.
  - cbn.
    intros γ.
    exists (mor.(f_mod_ctx) γ..1).
    apply (mor.(f_mod_typ) _ _ γ..2).
  - intros B γ sB.
    destruct B as [B|B].
    + (* ancien type *)
      apply (mor.(f_mod_typ)).
      assumption.
    + (* nouveau type *)
      destruct B as [B t u|B t u | B t u].
      *(*j'en suis la *)
        set (B' := eTy_old _ _ _) in u,sB.
        set (u' := transport _ (eq_refl B') u).
        set (g:= mod_typ _ _ _).
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
        set (B' := eTy_old _ _ _) in t,sB.
        set (t' := transport _ (eq_refl B') t).
        set (g:= mod_typ _ _ _).
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
     

CoFixpoint lift_rec_model Γ Δ A (s:ctxMor Γ Δ) (mΓ:Model_at Γ)
           (mΔ:Model_at Δ) (mor:Model_at_mor s mΓ mΔ)
           (yop : rec_model (s.(f_ty) A) mΔ) :
  rec_model A mΓ.
unshelve econstructor.
- exact (lift_ext A mor yop.(mext)).
- intro B.
  cbn.
  eapply (lift_rec_model _ (E Δ (f_ty s A))).
  + eapply E_Model_at_mor.
  + apply yop.(msuite).
Defined.

  Definition arrow_simplctx := ctx_arrow _ t_simplctx  u_simplctx.


Definition shift_full_model (m:full_model) 
           (γ0 : mod_ctx (full_mod_ctx m is_fin_simplctx  ) ) : full_model.
  unshelve econstructor.
  - cbn in γ0.
    eapply (mod_typ (full_mod_ctx m is_fin_simplctx  )).
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
      apply (full_mod_ctx  m (Γ :=simplctx)).
      apply is_fin_simplctx.
    + (* Model_at_mor modele one mor *)
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
                  full_mod_ctx_aux m is_fin_simplctx 
                                   in _).
      eapply ((monmod _)..2).
Defined.

(* Version pour les gset : l'interprétation des types renvoie un gset *)
Record gModel_at Γ :=
  { gmod_ctx : Type;
    gmod_typ : forall A : base Γ, gmod_ctx -> gset;
    gmod_term : forall A (t:Γ A), forall γ, objects (gmod_typ A γ) }.


Arguments gmod_ctx {Γ} m : rename.
Arguments gmod_typ {Γ} m _ _ : rename.
Arguments gmod_term {Γ} m {_} _ _ : rename.

Definition gModel_at_to_bare Γ (m:gModel_at Γ) : Model_at Γ :=
  {| mod_ctx := gmod_ctx m;
     mod_typ := fun A γ => objects (gmod_typ m A γ);
     mod_term := @gmod_term _ m |}.

Definition simpl_Model_ext Γ (m:Model_at Γ) (A:base Γ) :=
  forall γ : mod_ctx m,  m.(mod_typ) A γ -> m.(mod_typ) A γ -> Type.

Definition simpl_Model_ext_to_real Γ (m:Model_at Γ) (A:base Γ)
           (m' : simpl_Model_ext m A) : Model_ext m A :=
  {| mext_arrowr := fun t γ su => m' γ (m.(mod_term) t γ) su;
     mext_arrowl := fun u γ st => m' γ st (m.(mod_term) u γ);
     mext_arrowboth := fun γ st => m' γ st st |}.



Definition simpl_gModel_ext Γ (m:Model_at Γ) (A:base Γ) :=
  forall γ : mod_ctx m,  m.(mod_typ) A γ -> m.(mod_typ) A γ -> gset.

Definition simpl_gModel_ext_to_simpl_real Γ (m:gModel_at Γ) (A:base Γ)
           (m' : simpl_gModel_ext (gModel_at_to_bare m) A) : simpl_Model_ext
                                                               (gModel_at_to_bare m) A :=
  fun γ x y => objects (m' γ x y).
Definition infer_gModel_ext Γ A (m:gModel_at Γ) :
  simpl_gModel_ext (gModel_at_to_bare m) A :=
  fun γ x y => ((gmod_typ m A γ) x y).
Record gModel_ext Γ (m:gModel_at Γ) (A:base Γ) :=
  { gmext_arrowr : forall  (t: Γ A), forall γ : gmod_ctx m, objects (m.(gmod_typ) A γ) -> gset ;
    gmext_arrowl : forall  (u: Γ A), forall γ : gmod_ctx m, objects (m.(gmod_typ) A γ) -> gset ;
    gmext_arrowboth : forall γ : gmod_ctx m, objects (m.(gmod_typ) A γ) -> gset}.
Definition simpl_gModel_ext_to_real Γ (m:gModel_at Γ) (A:base Γ)
           (m' : simpl_gModel_ext (gModel_at_to_bare m) A) : gModel_ext m A :=
  {| gmext_arrowr := fun t γ su => m' γ (m.(gmod_term) t γ) su;
     gmext_arrowl := fun u γ st => m' γ st (m.(gmod_term) u γ);
     gmext_arrowboth := fun γ st => m' γ st st |}.
  


(* quasiment un copié collé de next_model *)
Definition gnext_model Γ A (m:gModel_at Γ) (s:gModel_ext m A) : gModel_at (E Γ A).
  unshelve econstructor.
  - exact (sigT (fun x => objects (m.(gmod_typ) A x))).
  - destruct 1 as [B|B].
    + (* ancien type *)
      exact (fun γ => m.(gmod_typ) B γ..1).
    + (* nouveau type *)
      intro γ.
      induction B as [B t u|B t u|B t u].
      * assert (eAB : A = B) by now inversion u.
        destruct eAB.
        eapply (s.(gmext_arrowr) t _ γ..2).
      * assert (eAB : A = B) by now inversion t.
        destruct eAB.
        eapply (s.(gmext_arrowl) u _ γ..2).
      * destruct t.
        eapply (s.(gmext_arrowboth) _ γ..2).
  - intros B t.
    destruct t as [B t| B t].
    + (* nouveau terme *)
      destruct t.
      apply projT2.
    + exact (fun γ => m.(gmod_term)  t γ..1).
Defined.


Section GModels2.

  Variables (Γ : Fam) (B : base Γ) (mg : gModel_at Γ).
  Variables(m:Model_at Γ)
      (mod_mor : Model_at_mor (ctxMor_id _) m (gModel_at_to_bare mg)).
  Definition gmodel1 : Model_at (E Γ B):=
    (next_model
       (lift_ext B mod_mor
          (simpl_Model_ext_to_real
             (simpl_gModel_ext_to_simpl_real
                (infer_gModel_ext (f_ty (ctxMor_id Γ) B)
                   mg))))).
  Definition gmodel2 : Model_at (E Γ B) :=
    (gModel_at_to_bare
       (gnext_model
          (simpl_gModel_ext_to_real (infer_gModel_ext B mg)))).

(* sans doute il y a moyen de définir ça sans passer par le morphisme gmodel1 -> gmodel2
mais j'ai la flemme d'y refélcéhir *)
Definition mor_gmodel12 : Model_at_mor (ctxMor_id (E Γ B))
                                              gmodel1 gmodel2.
  unshelve econstructor.
  { cbn.
    intros γ.
    eexists.
    eapply (f_mod_typ mod_mor).
    exact γ..2.
  }
  intros A γ.
  destruct A as [A|A].
  - (* ancien type *)
    eapply (f_mod_typ mod_mor).
  - (* nouveau type *)
    induction A.
    +
        set (B' := eTy_old _ _ _) in *.
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
        set (B' := eTy_old _ _ _) in *.
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



  (*
Definition gmodel1  Γ B mg : Model_at (E Γ B) :=
  gModel_at_to_bare ( gnext_model (simpl_gModel_ext_to_real (infer_gModel_ext B mg))).

Definition gmodel2  Γ B mg : Model_at (E Γ B) :=
    (next_model (simpl_Model_ext_to_real (simpl_gModel_ext_to_simpl_real (infer_gModel_ext B mg)))).
*)

(* sans doute il y a moyen de définir ça sans passer par le morphisme gmodel1 -> gmodel2
mais j'ai la flemme d'y refélcéhir *)
(*
Definition mor_gmodel12 Γ B mg : Model_at_mor (ctxMor_id (E Γ B))
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
        set (B' := eTy_old _ _ _) in *.
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
        set (B' := eTy_old _ _ _) in *.
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
*)

End GModels2.
(* Je suis obligé d'introduire ce m intermédiaire, et ce morphisme
de modèle, moralement égale à l'identité, car sinon la condition de
garde n'est pas vérifiée *)
CoFixpoint gset_to_recmodel_aux Γ (B:base Γ) (mg : gModel_at Γ)
           (m:Model_at Γ)
           (mod_mor : Model_at_mor (ctxMor_id _) m (gModel_at_to_bare mg)) :
  rec_model B m.
  (* rec_model B (gModel_at_to_bare mg). *)
  unshelve econstructor.
  - eapply lift_ext.
    exact mod_mor.
    eapply simpl_Model_ext_to_real.
     eapply simpl_gModel_ext_to_simpl_real.
     apply infer_gModel_ext.
  - intros A.
    set (mg' := gnext_model (A:=B) (m:=mg )
                            (simpl_gModel_ext_to_real (infer_gModel_ext _ mg))).
    unshelve eapply (gset_to_recmodel_aux _ A mg').
    eapply mor_gmodel12.
  Defined.
  (* OUIIII *)
  (* Tout ce qui vient après est pourri







C'est à dire a supprimer




   *)

CoFixpoint gset_to_recmodel_aux Γ (B:base Γ) (mg : gModel_at Γ):
  rec_model B (gModel_at_to_bare mg).
  unshelve econstructor.
  -  eapply simpl_Model_ext_to_real.
     eapply simpl_gModel_ext_to_simpl_real.
     apply infer_gModel_ext.
  - intros A.
                 lift_rec_model A (mor_gmodel12 B mg)
               (gset_to_recmodel_aux (E Γ B) A
                  (gnext_model
                     (simpl_gModel_ext_to_real
                        (infer_gModel_ext B mg)))) |})

    eapply (lift_rec_model (Δ:= E Γ B) A).
    eapply (mor_gmodel12).
    Guarded.
    eapply (gset_to_recmodel_aux _ A).
    Show Proof.
    df:w
         Guarded.
    set (mg' := gnext_model (A:=B) (m:=mg )
                            (simpl_gModel_ext_to_real (infer_gModel_ext _ mg))).
    set (suite := (gset_to_recmodel_aux _ A mg')).
   : rec_model A (gModel_at_to_bare mg')

  rec_model A
    (next_model
       (simpl_Model_ext_to_real
          (simpl_gModel_ext_to_simpl_real
             (infer_gModel_ext B mg))))
    apply myadmit.
    Show Proof.
    (cofix
 gset_to_recmodel_aux (Γ : PreCtx) (B : ctx_ty Γ)
                      (mg : gModel_at Γ) :
   rec_model B (gModel_at_to_bare mg) :=
   {|
   mext := simpl_Model_ext_to_real
             (simpl_gModel_ext_to_simpl_real
                (infer_gModel_ext B mg));
   msuite := fun A : ctx_ty (E Γ B) =>
             let mg' :=
               gnext_model
                 (simpl_gModel_ext_to_real
                    (infer_gModel_ext B mg)) in
             let suite := gset_to_recmodel_aux (E Γ B) A mg'
               in
             myadmit
               (rec_model A
                  (next_model
                     (simpl_Model_ext_to_real
                        (simpl_gModel_ext_to_simpl_real
                           (infer_gModel_ext B mg))))) |})
    Defined.
    eapply (lift_rec_model (Δ:= E Γ B) A).
    eapply (mor_gmodel12).
    exact suite.
  Defined.
  mg' := gnext_model (simpl_gModel_ext_to_real (infer_gModel_ext B mg)) : gModel_at (E Γ B)
                                                                                    e
    (next_model (simpl_Model_ext_to_real (simpl_gModel_ext_to_simpl_real (infer_gModel_ext B mg))))
    Set Printing Implicit.
  :w
     kDefinition gset_to_full_model (g:gset) : full_model.
      

Definition lift_ext Γ Δ A (s:ctxMor Γ Δ) (mΓ:Model_at Γ)
           (mΔ:Model_at Δ) (mor:Model_at_mor s mΓ mΔ)
           (sΔ : Model_ext mΔ (s.(f_ty) A)) : Model_ext mΓ A.

Definition shift_ctx_mor Γ (fΓ:FinCtx Γ) : ctxMor Γ (shift_ctx fΓ)..1.
   econstructor.
  exact (snd (shift_ctx fΓ)..2)..2.
Defined.

(*


Definition raw_subst_modelOne Γ Δ (s:raw_subst Γ Δ) (s'
           (m:Model_at Δ) : Model_at Γ.
  unshelve econstructor.
  -
*)
Definition shift_rec_model Γ (fΓ : FinCtx Γ) (B:base Γ)
           (m: Model_at fΓ)
           (* (m:rec_model B (full_mod_ctx fΓ)) *)
           (m' : Model_at (shift_ctx fΓ)..1)
           (mor : Model_at_mor (shift_ctx_mor fΓ) m m')
           (γ0 : mod_ctx (full_mod_ctx m is_fin_simplctx  ) )
  : { m' : Model_at (shift_ctx fΓ)..1 &
           { m'' : Model_at Γ &
                   (rec_model B m'') * (Model_at_mor (shift_ctx_mor fΓ) m'' m')
                                         * 
                         Model_ext m'
                                   (f_ty (shift_ctx_mor fΓ) B)
    }}%type.
Proof.
Admitted.

Definition shift_rec_model Γ (fΓ : FinCtx Γ) (B:base Γ) (m:full_model)
           (γ0 : mod_ctx (full_mod_ctx m is_fin_simplctx  ) )
  induction fΓ.
  - unshelve eexists.
    + unshelve econstructor.
      * exact
          (mod_typ (full_mod_ctx m is_fin_simplctx) (ctx_arrow _ t_simplctx u_simplctx) γ0).
      *


Definition shift_rec_model Γ (fΓ : FinCtx Γ) (B:base Γ) (m:full_model)
           (γ0 : mod_ctx (full_mod_ctx m is_fin_simplctx  ) )
  : { m' : Model_at (shift_ctx fΓ)..1 & Model_ext m'
                                                  ((snd (shift_ctx fΓ)..2)..1 B)}.
(* nouveau model & ancien model *)

Definition shift_rec_model Γ (fΓ : FinCtx Γ) (B:base Γ) (m:full_model)
           (γ0 : mod_ctx (full_mod_ctx m is_fin_simplctx  ) )
            : { m' : _ & Model_ext m' B}. (* nouveau model & ancien model *)
  set (Γ' := shift_ctx fΓ).
  induction fΓ.
  - admit.
  - unshelve eexists.
    unshelve eexists.
    + apply  model_empty.
      
    

Record ModelTwo :=
  { star_mod : Type;
    arrow_mod :forall Γ A (t u:Γ A), FinCtx Γ ->
        forall (sΓ: Type) (sA : sΓ -> Type) (st su : forall γ, sA γ), sΓ -> Type
  }.

(* Record Model := { all_mod :> forall Γ, FinCtx Γ -> Model_at Γ; *)
(*                  nil_unit : mod_ctx (all_mod fin_nil ) = unit }. *)
Definition one_to_two (m:forall Γ, FinCtx Γ -> Model_at Γ) : ModelTwo.
  unshelve econstructor.
  - set (m' :=  m _ (fin_cons (ctx_star _) fin_nil)).
    apply (mod_ctx m').
  - intros Γ A t u fΓ sΓ sA st su .
    intro γ.
    refine { e : sΓ = mod_ctx (m _ fΓ) &
                mod_typ (m _ fΓ) (ctx_arrow Γ t u) (transport _ e γ) }.
    eauto with typeclass_instances.
Defined.

Definition two_to_one (m:ModelTwo) : forall Γ, FinCtx Γ -> Model_at Γ.
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
    + set (sΓ := (sigT (IHΓ.( mod_typ) A))).
      unshelve econstructor.
      -- apply sΓ.
      -- induction 1 as [B|B].
         ++ (* ancien type *)
           exact (fun x => IHΓ.(mod_typ) B x..1).
         ++ (* nouveau type *)
           intro γ.
           induction B as [B t u|B t u| B t u].
           ** simple refine (@arrow_mod m (E Γ A) (eTy_old _ A B) _ _ _ 
                                          (sΓ )
                                          (fun γ =>  (IHΓ.(mod_typ) B γ..1))
                                          _ _ γ
                               ).
              --- apply eTm_old.
                  exact t.
              --- apply eTm_new.
                  clear -u.
                  inversion u.
                  constructor.
              --- now constructor.
              --- exact (fun γ => IHΓ.(mod_term)  t γ..1).
              --- intro γ'.
                  inversion u.
                  pattern B.
                  eapply transport.
                  eassumption.
                  exact γ'..2.
           ** simple refine (@arrow_mod m (E Γ A) (eTy_old _ A B) _ _ _ 
                                          (sΓ )
                                          (fun γ =>  (IHΓ.(mod_typ) B γ..1))
                                          _ _ γ
                               ).
              --- apply eTm_new.
                  clear -t.
                  inversion t.
                  constructor.
              --- apply eTm_old.
                  exact u.
              --- now constructor.
              --- intro γ'.
                  inversion t.
                  pattern B.
                  eapply transport.
                  eassumption.
                  exact γ'..2.
              --- exact (fun γ => IHΓ.(mod_term)  u γ..1).
           ** destruct t.
              set (B:=A).
             simple refine (@arrow_mod m (E Γ A) (eTy_old _ A B) _ _ _
                                          (sΓ )
                                          (fun γ =>  (IHΓ.(mod_typ) B γ..1))
                                          _ _ γ
                               ).
              --- apply eTm_new.
                  constructor.
              --- apply eTm_new.
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
           exact (fun γ => IHΓ.(mod_term) t  γ..1).
Defined.

(* J'ai donc une fonction one_one de Model_at vers Model_at par composition de
one_to_two et de two_to_one. Maintenant j'ai envie de dire qu'un modèle
est un Model_at muni d'une fonction de one_one vers lui-même.

Mais pour que ça marche j'aurai besoin d'UIP *)

(*
Class Model := 
  { (* ctxempty_mod : Type; *)
    (* ctxcons_mod : forall Γ (fΓ : FinCtx Γ) (A:base Γ), Type; *)
    mod_ctx : forall Γ, FinCtx Γ -> {
                    } ;
    (* mod_ctx : forall Γ, FinCtx Γ -> Type := *)
    (*   @FinCtx_rect _ unit (fun Γ A f _ => ctxcons_mod  f A); *)

    (* forall Γ, FinCtx Γ -> Type; *)
    (* star_mod : Type; *)
    mod_typ : forall Γ (fΓ  :FinCtx Γ) (A : base Γ), mod_ctx  fΓ -> Type;
    typ_term:  forall Γ (fΓ  :FinCtx Γ) (A : base Γ) (t:_ A)
                 (γ : mod_ctx  fΓ), mod_typ (* fΓ  *)A γ
        (* mod_ctx fΓ; *)


    (* unit_eq : mod_ctx fin_nil = unit; *)

  }.
*)

  Variable (m:Model).
  (* (x y: mod_typ (all_mod m fin_nil) (ctx_star _) *)
  (*                                      (transport (fun x => x) (eq_sym (nil_unit m)) tt )) *)
  Definition shift_model (g:mod_ctx (m simplctx is_fin_simplctx))  : Model.
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
            apply (mod_typ (all_mod m (fst Δ..2))).
            ++ apply (snd Δ..2)..1.
               refine (ctx_star _).
            ++ exact g.
          -- destruct t; contradiction.
        * intro A.
          destruct 1 ; contradiction.
      + (* Extension de contexte *)
        unshelve econstructor.
        * apply (sigT (mod_typ IHfΓ A)).
        * destruct 1 as [B|B].
          -- (* ancien type *)
            intro γ.
            apply (mod_typ IHfΓ A γ..1).
          -- (* nouveau type *)
            
             

            cbn in Δ.

  (* Definition shift_model  (x y: mod_typ fin_nil (ctx_star _) *)
  (*                                      tt ) : Model. *)
    unshelve econstructor .
    - intros Γ fΓ A.
      set (shift := shift_ctx fΓ).
      unshelve eapply (ctxcons_mod  _ ((snd shift..2)..1 A)).
      exact (fst shift..2).
    - intros Γ fΓ A γ.
      set (shift := shift_ctx fΓ).

  set (h:= mod_ctx (is_fin_simplctx)).
  set (tar := ctx_arrow _ t_simplctx u_simplctx).
  set (h' := mod_typ (is_fin_simplctx) tar  ).
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
          forall (A : base Γ) (sA : sΓ -> Type) ,
            Γ A -> Γ A ->
            forall (st su : forall γ, sA γ),
            sΓ -> Type}.

Record Semantique Γ :=
  { sΓ : Type;
    styΓ: forall A:base Γ, sΓ -> Type;
    stmΓ : forall (A:base Γ) (t:Γ A) (γ : sΓ), styΓ A γ}.

Definition empty_semantique : Semantique empty_ctx :=
  {| sΓ := unit; styΓ := fun _ _ => unit; stmΓ := fun _ _ _ => tt |}.

Definition empty_star_semantique (m:Model) : Semantique empty_star_ctx :=
 {|
 sΓ := unit;
 styΓ := fun (_ : base empty_star_ctx) (_ : unit) => Tstar m;
 stmΓ := fun (_ : unit) (t : False) (_ : unit) => False_rect (Tstar m) t |}. Section model.

  Variables (Γ : Ctx) (semΓ : Semantique Γ).



  Section model_EE.
    Variable (A:base Γ).
    Definition sΓA  : Type := sigT (semΓ.(styΓ _) A).
    Definition styΓA  (B:base (E Γ A)) (x:sΓA) : Type := semΓ.(styΓ _) B (projT1 x).
    Definition stmΓA  (B:base (E Γ A)) (t:(E Γ A) B) (γ : sΓA)
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
    Definition styTTΓ  (A:base (TT Γ)) (x:semΓ.(sΓ _)) : Type :=
      match A with
      | ty_fv _ _ A0 => semΓ.(styΓ _) A0 x
      (* | ty_star _ _ => m.(Tstar) *)
      | ty_arrow _ _ A0 t u => m.(Tarrow) Γ semΓ.(sΓ _) A0
                                         (semΓ.(styΓ _) A0) t u
                                         (semΓ.(stmΓ _) A0 t)
                                         (semΓ.(stmΓ _) A0 u) x
      end.

    Definition stmTTΓ  (B:base (TT Γ )) (t:_ B) (γ : sTTΓ)
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
| fin_E c (A:base c) : finCtx c -> finCtx ( (E c A))
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

Definition t_simplctx : simplctx _ (* (ty_fv _ _ tt) *) :=
  (* tm_fv _ _ _ *)
  (Some_fv _ _ _ _
     (New_fv _ _ _)).

Definition u_simplctx : simplctx _ (* (ty_fv _ _ tt) *) :=
  (* tm_fv _ _ _ *)
  ((New_fv _ _ _)).

Definition shift_model (m:Model) (x y : m.(Tstar)) : Model.
  set (h := semType m _ is_fin_simplctx).
  (* set (tm := simplctx (ty_star _ _)). *)
  (* cbn  in tm. *)
  (* assert ( *)
  (* set (t := tm_fv _ _ _ (New_fv _ _ _ ): tm). *)
  (* set (u := Some_fv _ _ _ _ (New_fv _ _ _)  : tm). *)
  set (tar := ty_arrow _ _ _ t_simplctx u_simplctx: base (TT simplctx)).
  set (h' := semTTΓ _ h m).
  econstructor.
  - eapply (styΓ _ h' tar).
    unshelve eexists.
    + exists tt.
      exact x.
    + exact y.
  - exact m.(Tarrow).
Defined.

Inductive is_psTerm : forall Γ (A:base Γ), _ A -> Type :=
  is_ps_init : is_psTerm (E empty_star_ctx tt) tt (New_fv _ _ _)
| is_ps_ar_end Γ A x y f : is_psTerm (TT Γ) (ty_arrow (base Γ) (Γ) A x y) f
                       -> is_psTerm Γ A y


| is_ps_tt Γ A t : is_psTerm (TT Γ) (ty_fv _ _ A) (tm_fv  _ _ _ t)
    (* peut etre inutile *)

| is_ps_ar Γ A x : is_psTerm Γ A x ->
                   is_psTerm 
                     (E (TT (E Γ A))
                                (ty_arrow
                                   (base (E Γ A))
                                   ((E Γ A))
                                   A
                                   (Some_fv 
                                      (base Γ)
                                      (Γ )
                                      _ _ x
                                   )
                                   (New_fv (base Γ)
                                           (Γ )
                                           A)
                             ))
                     _
                     (New_fv (base (TT (E Γ A)))
                             ((TT (E Γ A)))
                             _).

(*
Inductive is_psTerm : forall Γ (A:base Γ), _ A -> Type :=
  is_ps_init : is_psTerm (E empty_star_ctx tt) tt (New_fv _ _ _)
| is_ps_ar_end Γ A x y f : is_psTerm (TT Γ) (ty_arrow (base Γ) (Γ) A x y) f
                                     -> finCtx Γ (* je suis obligé de rajouter explicitement
cette hypothèse car sinon je ne peux pas le montrer à moins de supposer funext ou un truc du genre *)
                       -> is_psTerm Γ A y


| is_ps_tt Γ A t : finCtx Γ -> is_psTerm (TT Γ) (ty_fv _ _ A) (tm_fv  _ _ _ t)
    (* peut etre inutile *)

| is_ps_ar Γ A x : is_psTerm Γ A x ->
                   is_psTerm 
                     (E (TT (E Γ A))
                                (ty_arrow
                                   (base (E Γ A))
                                   ((E Γ A))
                                   A
                                   (Some_fv 
                                      (base Γ)
                                      (Γ )
                                      _ _ x
                                   )
                                   (New_fv (base Γ)
                                           (Γ )
                                           A)
                             ))
                     _
                     (New_fv (base (TT (E Γ A)))
                             ((TT (E Γ A)))
                             _).
*)

Fixpoint star_from_finCtx Γ (h:finCtx Γ) : base Γ :=
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
    assert(e':=f_equal base e); cbn in e'.
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
    
