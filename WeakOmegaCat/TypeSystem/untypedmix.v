(* -*- coq-prog-name: "coqtop"; -*- *)
Require Import Autosubst.Autosubst.

(* différences par rapport au papier :

Γ |- B dans weakening des termes

Γ |- dans la substitution du contexte vide

*)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Bullet Behavior "Strict Subproofs".
(* Ici, on mélange les types et les termes dans une seule définition inductive
pour bénéficier au mieux de autosubst *)


(* AutosubstSsr (examples) *)
(** * Autosubst wrapper for ssreflect *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section MMapInstances.

Variable (A B C : Type).
Variable (MMap_A_B : MMap A B).
Variable (MMap_A_C : MMap A C).
Variable (MMapLemmas_A_B : MMapLemmas A B).
Variable (MMapLemmas_A_C : MMapLemmas A C).
Variable (MMapExt_A_B : MMapExt A B).
Variable (MMapExt_A_C : MMapExt A C).


Global Instance MMap_option : MMap A (option B) := fun f => omap (mmap f).
Global Instance MMapLemmas_option : MMapLemmas A (option B). derive. Qed.
Global Instance MMapExt_option : MMapExt A (option B). derive. Defined.


Global Instance MMap_pair : MMap A (B * C). derive. Defined.
Global Instance MMapLemmas_pair : MMapLemmas A (B * C). derive. Qed.
Global Instance MMapExt_pair : MMapExt A (B * C). derive. Defined.


Global Instance mmap_seq : MMap A (seq B) := fun f => map (mmap f).
Global Instance mmapLemmas_seq : MMapLemmas A (seq B). derive. Qed.
Global Instance mmapExt_seq : MMapExt A (seq B). derive. Defined.


Global Instance MMap_fun : MMap A (B -> C) := fun f g x => mmap f (g x).

Global Instance MMapLemmas_fun : MMapLemmas A (B -> C).
Proof.
  constructor; intros; f_ext; intros; [apply mmap_id|apply mmap_comp].
Qed.

Global Instance MMapExt_fun : MMapExt A (B -> C).
Proof.
  hnf. intros f g H h. f_ext. intro x. apply mmap_ext. exact H.
Defined.

End MMapInstances.

(* Fin AutosubstSsr (examples) *)

(* Example/Context.v *)

Definition get {T} `{Ids T} (Gamma : seq T) (n : var) : T :=
  nth (ids 0) Gamma n.
Arguments get {T _} Gamma n.

Fixpoint dget {T} `{Ids T} `{Subst T} (Gamma : list T) (n : var) {struct n} : T :=
  match Gamma, n with
    | [::], _ => ids 0
    | A :: _, 0 => A.[ren (+1)]
    | _ :: Gamma, n.+1 => (dget Gamma n).[ren (+1)]
  end.
Arguments dget {T _ _} Gamma n.

Lemma get_map {T} `{Ids T} (f : T -> T) Gamma n :
  n < size Gamma -> get (map f Gamma) n = f (get Gamma n).
Proof. exact: nth_map. Qed.

Lemma get_map_gen {T U} `{Ids T} `{Ids U} (f : T -> U) Gamma n :
  n < size Gamma -> get (map f Gamma) n = f (get Gamma n).
Proof. exact: nth_map. Qed.

(* Fin Context.v *)

(*
**************************

Compléments Autosubst

**************************
 *)

(* injectivité de ids (ids est l'injection des indices de De Bruijn dans les termes) *)
Lemma injids:
forall (term : Type) (Ids_term : Ids term) (Rename_term : Rename term) (Subst_term : Subst term),
  SubstLemmas term -> forall (i j : nat) (s s' :term) (e:s <> s') (ei:ids i = ids j) , i = j.
  intros.
  set sigma := fun n => if n == i then s else if n == j then s' else ids n .
  have ei' : (ids i).[sigma] = (ids j).[sigma] by rewrite ei.
  move:ei'.
  asimpl ; subst sigma => /=.
  rewrite !eq_refl.
  case:eqP => //=.
Qed.

Lemma noidsren:
forall (term : Type) (Ids_term : Ids term) (Rename_term : Rename term) (Subst_term : Subst term),
  SubstLemmas term -> forall (s : term)  (u u':term) (eu:u<>u'), ~s.[ren (+1)] = ids 0.
intros.
set a:= (a in a=_).
set b:= (b in _=b).
intro hab.
have hab' : a.[ren(fun x => x.-1)] = b.[ren(fun x=> x.-1)] by rewrite hab.
subst a b.
asimpl in hab'.
have hab'' : s = ids 0.
rewrite <-hab'.
now rewrite subst_id.
subst s.
asimpl in hab.
revert hab.
cbn.
move/(injids _ eu).
discriminate.
Qed.

(* Fin compléments *)

(* Examples/Poplmark.v *)
Notation "Gamma `_ x" := (dget Gamma x).
Notation "Gamma ``_ x" := (get Gamma x) (at level 3, x at level 2,
  left associativity, format "Gamma ``_ x").

Inductive term : Type :=
  | TeVar (x:var)
          (* Coh Γ A σ *)
  | TeCoh : list term -> term -> list term -> term
  | tyUnit
  | tyAr : term -> term -> term -> term.

(* TODO : refaire le principe d'induction pour prendre en compte les list term *)

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.

Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

(* pour l'instant inutile *)

Inductive is_term : term -> Prop :=
  | isteVar x : is_term  (TeVar x).

Definition bis_term (t:term) :=
  match t with
    TeVar _ => true
  | _ => false
  end.

Fixpoint bis_ty (t:term) :=
  match t with
    tyUnit => true
  | tyAr A t u => bis_ty A && bis_term t && bis_term u
  | _ => false
  end.

Inductive is_ty : term -> Prop :=
| istyUnit : is_ty tyUnit
| istyAr A t u : is_ty A -> is_term t -> is_term u -> is_ty (tyAr A t u).

Lemma is_termP t : reflect (is_term t) (bis_term t).
Admitted.

Lemma is_tyP t : reflect (is_ty t) (bis_ty t).
Admitted.



(* *********


Decidable equality


 ********** *)
(* ma tactique de coqonut *)

Section eqdec.
  Import List.

  Hint Resolve eq_comparable list_eq_dec :eq_dec.

  Hint Unfold comparable decidable: eq_dec.

  Ltac solve_eq_dec :=
    repeat autounfold with eq_dec in * ;
    try fix ind 1;
    intros;
    decide equality;
    let x := fresh in
    move: (z in z=_) => x; move : x (z in _=z); rewrite -/(comparable _);
                       auto with eq_dec.
  Lemma eq_dec_term (x y : term) : {x=y} + {~x=y}.
    move:x y. 
    solve_eq_dec.
    unfold var.
    solve_eq_dec.
  Defined.
End eqdec.
Definition term_eqP : Equality.axiom (compareb eq_dec_term) := compareP eq_dec_term.

Canonical term_eqMixin := EqMixin term_eqP.
Canonical term_eqType := Eval hnf in EqType term term_eqMixin.

(*
Instance Ids_type : Ids type.
cbn.
red.
derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
Instance SubstLemmas_type : SubstLemmas type. derive. Qed.
Instance HSubst_term : HSubst type term. derive. Defined.

Instance HSubstLemmas_term : HSubstLemmas type term. derive. Qed.
Instance SubstHSubstComp_type_term : SubstHSubstComp type term. derive. Qed.
*)



Reserved Notation "Gamma |- A : B"
  (at level 68, A at level 99, no associativity,
   format "Gamma  |-  A  :  B").
Reserved Notation "Gamma |- A"
  (at level 68, A at level 99, no associativity,
   format "Gamma  |-  A").

(*

* , * , 0 -> 1 |- 0 : 1 -> 2

*)


Definition ctx := list term.



Inductive ty : ctx -> term -> term  -> Type :=
| ty_var0 Γ A : wfCtx (A :: Γ) -> ty  (A::Γ) A.[ren(+1)] (ids 0)
| ty_termS Γ s A B : Γ |- s : A -> wfTy Γ B -> (B::Γ) |- s.[ren(+1) ] : A.[ren(+1)]
with wfCtx : ctx -> Type :=
     | wfEmpty : wfCtx nil
     | wfCtxNext Γ A :  wfTy Γ A -> wfCtx (A::Γ)
with wfTy :  ctx ->   term -> Type :=
  | wfUnit Γ : wfCtx Γ -> Γ |- tyUnit
  | wfAr Γ A t u : Γ |- t : A -> Γ |- u : A -> Γ |- (tyAr A t u)
where "Gamma |- A" := (wfTy Gamma A) and
 "Gamma |- s : A" := (ty Gamma A s).

Scheme wfCtx_mut := Induction for wfCtx Sort Type
with wfTy_mut := Induction for wfTy Sort Type
with ty_mut := Induction for ty Sort Type.
Module DefProp.
(* la même mais avec des Prop *)
  (*
Inductive ty : list term -> term -> term  -> Prop :=
| ty_var0 Γ A : wfCtx (A :: Γ) -> ty  (A::Γ) A.[ren(+1)] (ids 0)
| ty_termS Γ s A B : Γ |- s : A -> (B::Γ) |- s.[ren(+1) ] : A.[ren(+1)]
with wfCtx : (list term) -> Prop :=
     | wfEmpty : wfCtx nil
     | wfCtxNext Γ A :  wfTy Γ A -> wfCtx (A::Γ)
with wfTy :  (list term) ->   term -> Prop :=
  | wfUnit Γ : wfCtx Γ -> Γ |- tyUnit
  | wfAr Γ A t u : Γ |- t : A -> Γ |- u : A -> Γ |- (tyAr A t u)
where "Gamma |- A" := (wfTy Gamma A) and
 "Gamma |- s : A" := (ty Gamma A s).
*)

(*
Fixpoint bwfTy_aux (A:term) Γ {struct A} :=

  match A with
    tyUnit => true
  | tyAr A' t u => (bty Γ t == Some A') &&( bty Γ u == Some A')
  | _ => false
  end
with
bty Γ t {struct Γ} :=
  match t with
  | TeVar n =>
    match Γ with
      nil => None
    | A :: Γ' => 
      let bwfTy := bwfTy_aux A (Γ') in
      if bwfTy  && (n < size Γ) then
                Some (Γ``_n)
              else
                None
    end
  | _ => None
  end.
*)

  Definition bwfTy_aux (A:term) (is_wfctx: bool) (typ : term -> option term) : bool 
    :=
  match A with
    tyUnit => is_wfctx
  | tyAr A' t u => (typ t == Some A') &&( typ u == Some A')
  | _ => false
  end.

Definition bwfCtx_aux bwfCtx bty (Γ':list term)  A :=
  bwfTy_aux A (bwfCtx Γ') (bty Γ').

Fixpoint bwfCtx  Γ : bool :=
  match Γ with
    nil => true
  | A :: Γ' => bwfCtx_aux bwfCtx bty Γ' A 
  end
with bty (Γ:list term) (t:term) {struct Γ} : option term :=
  match Γ with
    nil => None
  | B::Γ =>
    let wfB := bwfCtx_aux bwfCtx bty Γ B  in
    if wfB is false then
      None
    else
      if t == TeVar 0 then
        Some (B.[ren(+1)])
      else
        let u := t.[ren predn] in
        if t == u.[ren(+1)] then
          match bty Γ u with
            Some A => Some (A.[ren(+1)])
          | None => None
          end
        else
          None
  end.
(*f
Fixpoint bwfCtx_aux  (typ:list term -> term -> option term) Γ : bool :=
  
  match Γ with
    nil => true
  | A :: Γ' => bwfTy_aux A (bwfCtx_aux typ Γ') (typ Γ')
  end.

Fixpoint bty (Γ:list term) (t:term) {struct Γ} : option term :=
  None.
*)
(*
  match Γ with
    nil => None
  | B::Γ =>
    if t == TeVar 0 then
      if bwfCtx_aux bty (B::Γ) then
        Some (B.[ren(+1)])
      else
        None
    else
      let u := t.[ren predn] in
      if t == u.[ren(+1)] then
        match bty Γ u with
          Some A => Some (A.[ren(+1)])
        | None => None
        end
      else
        None
    end.

Definition bwfCtx   := bwfCtx_aux bty.
*)


Definition bwfTy Γ A  := bwfTy_aux A (bwfCtx Γ) (bty Γ).

(* Definition hyp_btyP := forall t Γ A, reflect (Γ |- t : A) (bty Γ t == Some A). *)

(*
Lemma wfTyP_aux (h:hyp_btyP) Γ A  : reflect (wfTy Γ A) (bwfTy Γ A).
  unfold bwfTy, bwfCtx.
  elim : A.
  -  intros; constructor.
     now inversion 1.
  -  cbn. intros; constructor.
     constructor.
  - intros A hA u _ t _.
    simpl.
    case:(h u).
    case:(h t).
    + intros ht hu.
      constructor.
      now constructor.
    + intros.
      constructor.
      now inversion 1.
    + intros.
      constructor.
      now inversion 1.
Defined.
Lemma wfCtxP_aux Γ (h:hyp_btyP): reflect (wfCtx Γ) (bwfCtx Γ).
  case: Γ.
  - repeat constructor.
  - intros A Γ. cbn.
    rewrite -[bwfTy_aux _ (bty Γ)]/(bwfTy Γ _).
    case:(wfTyP_aux h); intros hΓ; constructor.
    + now constructor.
    +  now inversion 1.
Defined.



Fixpoint wftyP t Γ A : reflect (Γ |- t : A) (bty Γ t == Some A).
  set P := (P in reflect P).
  set b := ( b in reflect _ b).
  case:Γ @b @P.
  - intros b P. have :~P by inversion 1.
    subst b.
    now case:(t); auto using ReflectF .
  -  intros B Γ b P .
     subst b.
     simpl.
     rewrite -/(bwfTy _ _) .
     case:(eqP (x:=t) ).
     + subst P; move =>-> /=. 
       case:(wfTyP_aux wftyP).
       * move => tyP. 
         apply:(iffP eqP).
         -- case => <- .
            now repeat constructor.
         --  inversion 1.
             reflexivity.
             subst.
             exfalso.
             rewrite -[TeVar 0]/(ids 0) in H4.
             unshelve eapply (noidsren _ _  (u:=ids 0) (u':=ids 1) H4).
             discriminate.
       *  intro tyB; constructor.
          inversion 1 ; subst.
          -- now inversion H3.
          -- unshelve eapply (noidsren _ _  (u:=ids 0) (u':=ids 1) H4).
             discriminate.
     +  move => ht.
        set u := t.[ren predn] .
        case eqA' : bty => [A'|].
        * have tu:= (wftyP u Γ A').
          rewrite eqA' eq_refl in tu.
          inversion tu as [htg |] => {tu}.
          subst P.
          case:(eqP (x:=t)).
          -- move => ->.
             apply:(iffP eqP).
             ++ move =>  [<-].
                now constructor.
             ++ inversion 1.
                ** exfalso.
                   unshelve eapply (noidsren _ _  (u:=ids 0) (u':=ids 1) (esym H4)).
                   discriminate.
                ** apply lift_inj in H4. subst.
                   move/wftyP:H3 => /eqP.
                   congruence.
          -- move => h.
             constructor.
             inversion 1.
             ++ subst.
                now apply ht.
             ++ subst.
                apply h.
                subst u.
                asimpl.
                reflexivity.
        * have hP:(~P).
          -- subst P. inversion 1.
             ++ subst.
                now apply ht.
             ++ subst.
                move/wftyP/eqP:H4.
                have <- :u=s by subst u; asimpl; apply subst_id.
                congruence.
          -- now case:(eqP (x:=t)) => _ ; constructor.
Qed.
*)

End DefProp.
Lemma weakening_type Γ A B (wA: Γ |- A) (wB: Γ |- B)  : (B::Γ) |- A.[ren(+1)].
 case:Γ A/wA wB.
  + constructor.
    now constructor.
  + move => Γ A t u wt wu wB.
    constructor.
    * now constructor.
    * now constructor.
Qed.

Lemma lemma61 Γ t A (w:Γ |- t : A) : wfTy Γ A.
  (* * wfCtx Γ) . *)
        (* with lemma61' Γ A (wA: Γ |- A)   : wfCtx Γ. *)
  elim:Γ  A t /w.
  + move => Γ A wfA.
    inversion wfA; subst.
    now apply: weakening_type.
  +  move => Γ s A B ct .
     (* move => [wfA wfΓ] cu . *)
     move => wfA cu.
     (* case/lemma61:(ct) => wfA wfΓ. *)
     have wfΓB : wfCtx (B::Γ) by constructor.
     (* split => //. *)
     now apply :weakening_type.
Qed.

Lemma ty_wfctxt Γ t A (w:Γ |- t : A) : wfCtx Γ.
Proof.
  elim:Γ  A t /w => //.
  +  move => Γ s A B ct .
     move => wfA cu.
     now constructor.
Defined.

Lemma wfty_wfctxt Γ A (w:Γ |- A) : wfCtx Γ.
Proof.
  elim:Γ  A  /w => //.
  +  intros.
     apply:ty_wfctxt.
     eauto.
Defined.
(*
Inductive wfTy (Γ:Ctx) : type -> Type :=
  | wfUnit : Γ |- tyUnit
  | wfAr A t u : Γ |- t : A -> Γ |- u : A -> Γ |- (tyAr A t u)
where "Gamma |- A" := (wfTy Gamma A).
*)

Definition substs := list term.

Inductive ty_substs Δ : ctx -> substs -> Type :=
| tysEmpty : wfCtx Δ ->  ty_substs Δ nil nil
| tysNext Γ (A:term) t σ : ty_substs Δ Γ σ
                           -> wfTy Γ A
                           -> Δ |- t : A.[get σ] ->
                                     ty_substs Δ (A::Γ) (t::σ).


Lemma lemma8 Δ Γ A σ t (tyσ : ty_substs Δ Γ σ) (tyt : Γ |- t : A)
  : Δ |- (t.[get σ]) : A.[get σ].
  elim :Γ σ  /tyσ A t tyt.
  - (* impossible *)
    intros;
    inversion tyt.
  - move =>  Γ Aσ tσ σ tyσ IH.
    move => wfAσ tytσ A t.
    move => tyt.
    remember (Aσ :: Γ) as Γ' eqn:eqΓ'.
    induction tyt.
    + cbn.
      asimpl.
      have : A= Aσ by congruence.
      now move => ->.
      (*
      simpl.
      apply:tytσ.
*)
    + asimpl.
      eapply IH.
      congruence.
Qed.

Lemma lemma62 Δ Γ σ :ty_substs Δ Γ σ -> wfCtx Γ.
  now destruct  1; constructor.
Defined.

Lemma lemma622 Δ Γ σ :ty_substs Δ Γ σ -> wfCtx Δ.
  destruct  1 => //. 
  apply:ty_wfctxt.
  eauto.
Defined.

Lemma size_ty_substs Δ Γ σ :ty_substs Δ Γ σ -> size σ = size Γ.
  induction 1 => //=.
  congruence.
Defined.


Lemma subst_term_rien  t σ τ Γ A  (wA : Γ |- t:A) (hs: forall n, n < size Γ -> σ n = τ n) :
  t.[σ] = t.[τ].
Proof.
elim:Γ A t / wA σ τ hs.
  + move => Γ A wfΓ σ τ hs.
    now apply hs.
  + move => Γ t A B wft HI wfB σ τ hs.
    asimpl.
    apply:HI.
    move => n ltn.
    cbn.
    now apply:hs.
Qed.
Lemma subst_typ_rien A σ τ Γ (wA : Γ |- A) (hs: forall n, n < size Γ -> σ n = τ n)  :
  A.[σ] = A.[τ].
Proof.
  induction A; try by inversion wA.
  asimpl.
  inversion_clear wA.
  congr tyAr.
  +  apply:IHA1.
     apply:lemma61; eauto.
  + apply: (subst_term_rien  ) => //; eauto.
  + apply: (subst_term_rien  ) => //; eauto.
Qed.

(* *************

substitution identité

 ************** *)

Instance Ids_nat : Ids nat := id. 

Lemma cat_wfctxt Γ Δ (w:wfCtx (Δ++Γ)) : wfCtx Γ.
  elim:Δ Γ w => //.
  move => A Δ hI Γ wfΓ.
  inversion_clear wfΓ.
  apply:hI.
  apply:wfty_wfctxt.
  eauto.
Qed.

(* Lemma wfCtx_rect2 :forall P : forall l : seq term, Type, *)
(* P [::] -> *)
(* (forall (l : seq term) (t:term), P l -> P (t::l)) -> P *)
Lemma id_subst Γ Δ (w:wfCtx( Δ++Γ))  : ty_substs (Δ++Γ) Γ
                                           (mkseq (fun n => ids (n+size Δ)) (size Γ)).
  elim:Γ Δ w.
  - now constructor.
  - intros A Γ IH Δ w.
    apply :tysNext.

    + specialize (IH (Δ ++ A::nil)).
      move:w.
      rewrite -cat_rcons -cats1 => /IH w.
      refine (eq_rect _ (fun z => ty_substs _ _ z) w _ _).
      cbn.
      rewrite /mkseq.
      cbn.
      rewrite (iota_addl (1) (0)).
      rewrite -map_comp.
      cbn.
      apply:eq_map.
      move => n //=.
      rewrite size_cat /funcomp /=.
      congr ids.
      rewrite -addnE addnA addnC.
      reflexivity.
    + move/cat_wfctxt:w.
      now inversion 1.
    + cbn.
      elim:Δ w. 
      * cbn.
        move => w.
        set A' := (A' in _ |- _ :A').
        set A'' := A.[ren(+1)].
        suff eqA : A' = A''.
        { rewrite eqA.
        now constructor.
        }
        have wA : Γ |- A by inversion w.
        apply:(subst_typ_rien wA).
        move => n ltn.
        rewrite get_map_gen.
        cbn.
        rewrite -addnE addn0.
        congr ids.
        asimpl.
        now apply:nth_iota.
        now rewrite size_iota.
      * move => B Δ hI w.
        set A'' := (A' in _ |- _ :A').
        set A' := (A in _ |- _ : A) in hI.
        set A''2 :=A'.[ren(+1)].
        suff eqA : A'' = A''2.
        { rewrite eqA.
          apply:(ty_termS (s:=ids (size Δ))) => //.
          apply:hI.
          apply:(cat_wfctxt (Δ:=B::nil)).
          apply:w.
          now inversion w.
        }
        subst A''2 A' A''.
        asimpl.
        apply:subst_typ_rien.
        apply (cat_wfctxt (Δ:=B::Δ)) in w.
        inversion w; eauto.
        move => n ltn.
        cbn.
        rewrite get_map_gen ?size_iota //.
        cbn.
        rewrite get_map_gen ?size_iota //.
        asimpl.
        congr ids.
Qed.



(* *****************

Composition des substitutions

***************** *)

(* σ o τ *)
Definition comp_subst (σ τ:substs) :=
  mkseq ( ((get σ) >> (get τ))) (size σ).


Lemma wf_comp_subst Δ Γ E (σ τ : substs) (wσ : ty_substs Δ Γ σ) (wτ : ty_substs E Δ τ) :
  ty_substs E Γ (comp_subst σ τ).
Proof.
  induction wσ.
  - constructor.
    apply :lemma622; eauto.
  - apply :tysNext => //.
    (* induction wτ as [|E A t τ]. *)
    + 
      (* rewrite -cat_rcons -cats1 => /IH w. *)
      (* preuve recopiée de la substitution identité
TODO : factoriser *)
      refine (eq_rect _ (fun z => ty_substs _ _ z) IHwσ _ _).
      rewrite /comp_subst.
      rewrite /mkseq.
      cbn.
      rewrite (iota_addl (1) (0)).
      rewrite -map_comp.
      cbn.
      apply:eq_map.
      move => n //=.
    + have tyA := lemma8 wτ t0.
      (* set t' := (t in E|- t:_). *)
      (* have et' : t' = t.[get τ] by reflexivity. *)
      refine (eq_rect _ (fun z => E |- _ : z) tyA _ _).
      asimpl.
      apply:subst_typ_rien .
      exact :w.
      move => n ltn /=.

      have ltnσ:n < size σ by rewrite (size_ty_substs wσ).
      
      rewrite get_map_gen ?size_iota //.
      cbn.
      rewrite [(iota _ _)``_n]/get.
      rewrite nth_iota //.
Qed.


(* ****************


Traduction context -> gset

******************* *)

CoInductive gset :=
  Gset { objects : Type ;
         hom :> objects -> objects -> gset }.
CoFixpoint empty_gset : gset := {| objects :=  False ;
                                   hom := fun _ _ => empty_gset  |}.


Fixpoint get_vars (x y : var) (Γ : list term) (n:nat) : list var :=
  if (x == 0) || (y == 0) then
    nil
  else
    let xm := x.-1 in
    let ym := y.-1 in
    match Γ with
      nil => nil
    |  t:: q =>
         let l := get_vars (xm) (ym) q (n.+1) in
         match t with
         | tyAr _ (TeVar x') (TeVar y') =>
           if (x' == xm) && (y' == ym) then
             n:: l
           else
             l
         | _ => l
         end
    end.
  
Fixpoint find_empty (Γ : list term) (n:nat) : list var :=
  match Γ with
    nil => nil
  | t ::q =>
    let l := find_empty q (n.+1) in
    if t == tyUnit then
      n :: l
    else
      l
  end.

(* Definition next_gset_dummy (x y : var) Γ : Type := *)
(*   let l := get_vars x y 0 in *)

From mathcomp Require Import fintype.

Definition rec_ctx_to_gset_dumm (l:list var) (f:var -> var -> gset) (* (Γ:list term)  *): gset.
  unshelve econstructor.
  - exact (ordinal (size l)).
  - exact f.
    (*
    move => a b.
    eapply f.
    + exact (nth (ids 0) Γ a).
    + exact (nth 0 Γ b).
*)
Defined.

CoFixpoint ctx_to_gset_dumm_next (Γ : list term) (x y: var)  : gset :=
  rec_ctx_to_gset_dumm (get_vars x y Γ 0) (ctx_to_gset_dumm_next Γ).

Definition ctx_to_gset_dumm (Γ:list term):gset :=
  rec_ctx_to_gset_dumm (find_empty Γ 0) (ctx_to_gset_dumm_next Γ).

Definition ο {n} i {lei} := Ordinal (n:=n) (m:=i) lei.
Arguments ο {n} i {lei}.

Module exemple.
  Definition Γ :=[:: tyUnit;tyAr tyUnit (ids 0) (ids 1) ; tyUnit; tyUnit ].
  Eval compute in (find_empty Γ 0).
  Definition exemple := (ctx_to_gset_dumm Γ).
  Eval compute in (objects exemple).
  Eval compute in (objects (@hom exemple (ο 0) (ο 1))).
  Eval compute in (objects ((@hom exemple) (ο 1) (ο 2))).
  Eval compute in (objects ((@hom exemple) (ο 2) (ο 3))).
  Eval compute in (get_vars  1 2 Γ 0).
End exemple.



(* ******************


Definition du typage  |- ps



* **************)
Reserved Notation "Gamma |-_ps A : B"
  (at level 68, A at level 99, no associativity,
   format "Gamma  |-_ps  A  :  B").

Inductive tyPs : ctx -> term -> term -> Type :=
       pstUnit : [:: tyUnit] |-_ps (ids 0) : tyUnit
     | pstEnd Γ t x y A :  Γ |-_ps t : tyAr A x y -> Γ |-_ps y : A
     | pstAr Γ x A  :  Γ |-_ps x : A ->
                                   (tyAr A x (ids 0) ::A::Γ) |-_ps ids 0
                                        : (tyAr A x (ids 0)).[ren (+1)]
where "Gamma |-_ps t : A" := (tyPs Gamma t A).

Inductive wfCtxPs : ctx -> Type :=
  psCtxTerm Γ t: Γ |-_ps t : tyUnit -> wfCtxPs Γ.

Fixpoint is_sub_right t A y {struct A} :=
  if t == y then
    Some A
  else
    if A is tyAr A' x' y' then
      is_sub_right t A' y'
    else
      None.
Fixpoint btyPs Γ t {struct Γ} : option term :=
  match Γ with
  | nil => None
  | (B::nil) =>
    if B is tyUnit then
      if t is TeVar 0 then
        Some tyUnit
      else
        None
    else
      None
  | (B::A::Γ') =>
    match B with
      tyAr A' x y => 
      let x' := x.[ren predn] in
    if (x == x'.[ren (+1)]) && (btyPs Γ' x' == Some A )&& (A' == A.[ren(+1)]) then
        is_sub_right t A' y
      else
        None
    | _ => None
    end
  end.

Definition bwfCtxPs Γ :=
  if btyPs Γ (ids 0) is Some A then
    true
  else
    false.

(*

* , * , 0 -> 1 |- 0 : 1 -> 2

*)
Definition Γps := [:: tyAr tyUnit (ids 1) (ids 0); tyUnit; tyUnit ].
Eval compute in bwfCtxPs Γps.
Eval compute in bwfCtxPs [:: tyUnit; tyUnit].
Eval compute in bwfCtxPs [:: tyUnit].


(* wfCtx_mut nous donne les élements qui constitueront le modèle
notamment le foncteur S_glob -> Type
un objet de S_glob est { Γ : ctxt & wfCtx Γ } *)

Definition needed := @wfCtx_mut (fun _ _ => Type).
Definition tneeded := ltac: (match (type of needed) with ?x => set (y:=x); cbn in y; exact y end).
Goal True.
 (match (type of needed) with ?x => set (y:=x); cbn in y end).
 (*

   forall (P : forall (l : seq term) (t : term), l |- t -> Type)
         (P0 : forall (l : seq term) (t t0 : term), l |- t0 : t -> Type),
       Type ->
       (forall (Γ : seq term) (A : term) (w : Γ |- A), P Γ A w -> Type) ->
       (forall (Γ : seq term) (w : wfCtx Γ), Type -> P Γ tyUnit (wfUnit w)) ->
       (forall (Γ : seq term) (A t u : term) (t0 : Γ |- t : A),
        P0 Γ A t t0 -> forall t1 : Γ |- u : A, P0 Γ A u t1 -> P Γ (tyAr A t u) (wfAr t0 t1)) ->
       (forall (Γ : seq term) (A : term) (w : wfCtx (A :: Γ)),
        Type -> P0 (A :: Γ) A.[ren (+1)] (ids 0) (ty_var0 w)) ->
       (forall (Γ : seq term) (s A B : term) (t : Γ |- s : A),
        P0 Γ A s t -> P0 (B :: Γ) A.[ren (+1)] s.[ren (+1)] (ty_termS B t)) ->
       forall l : seq term, wfCtx l -> Type : Type
*)
 Abort.

Section FunctorObjModel.
Unset Implicit Arguments.
  Variables (Pty : forall (l : seq term) (t : term), wfTy l t -> Type)
         (Pt: forall (l : seq term) (t t0 : term), l |- t0 : t -> Type)
       (Fempty:Type ).
  Variables (Fty : forall (Γ : seq term) (A : term) (w : Γ |- A), Pty Γ A w -> Type)
       (Pty_unit: forall (Γ : seq term) (w : wfCtx Γ), Type -> Pty Γ tyUnit (wfUnit w))
       (Pty_ar : forall (Γ : seq term) (A t u : term) (t0 : Γ |- t : A),
           Pt Γ A t t0 -> forall t1 : Γ |- u : A, Pt Γ A u t1 -> Pty Γ (tyAr A t u) (wfAr t0 t1))
       (Ptvar0 :forall (Γ : seq term) (A : term) (w : wfCtx (A :: Γ)),
        Type -> Pt (A :: Γ) A.[ren (+1)] (ids 0) (ty_var0 w)) 
       (PtS : forall (Γ : seq term) (s A B : term) (t : Γ |- s : A),
        Pt Γ A s t -> Pt (B :: Γ) A.[ren (+1)] s.[ren (+1)] (ty_termS B t)).

  Definition F (l:ctxt) (w:wfCtx l) : Type :=
    @wfCtx_mut (fun _ _ => Type) Pty Pt Fempty Fty Pty_unit Pty_ar Ptvar0 PtS l w.

  Goal True.
    set z := fun Δ wΔ => @ty_substs_rect Δ (fun Γ σ w =>  F Δ wΔ -> F Γ (lemma62 w)).
    cbn in z.
  (*
    : forall (Δ : seq term) (wΔ : wfCtx Δ),
      (F Δ wΔ -> F [::] (lemma62 (tysEmpty Δ))) ->
      (forall (Γ : ctxt) (A t : term) (σ : substs) (t0 : ty_substs Δ Γ σ),
       (F Δ wΔ -> F Γ (lemma62 t0)) ->
       forall (w : Γ |- A) (t1 : Δ |- t : A.[get σ]), F Δ wΔ -> F (A :: Γ) (lemma62 (tysNext t0 w t1))) ->
      forall (c : ctxt) (s : substs) (t : ty_substs Δ c s), F Δ wΔ -> F c (lemma62 t)
*)
