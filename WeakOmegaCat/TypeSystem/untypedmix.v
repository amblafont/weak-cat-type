(* -*- coq-prog-name: "coqtop"; -*- *)
Require Import Autosubst.Autosubst.

(* différences par rapport au papier :

Γ |- B dans weakening des termes

Γ |- dans la substitution du contexte vide

TODO :  remplacer la r_gle Γ,x:A |- en prémisse par Γ |- A

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

(**
**************************

Compléments Autosubst

**************************
 *)

Class Notunit (term : Type) := notunit : { s : term * term & fst s <> snd s}.
(* injectivité de ids (ids est l'injection des indices de De Bruijn dans les termes) *)
Lemma injids:
forall (term : Type) (Ids_term : Ids term) (Rename_term : Rename term) (Subst_term : Subst term),
  SubstLemmas term -> Notunit term -> forall (i j : nat) (ei:ids i = ids j) , i = j.
  intros.
  case:notunit => [[s s'] /= es]. 
  set sigma := fun n => if n == i then s else if n == j then s' else ids n .
  have ei' : (ids i).[sigma] = (ids j).[sigma] by rewrite ei.
  move:ei'.
  asimpl ; subst sigma => /=.
  rewrite !eq_refl.
  case:eqP => //=.
Qed.

Lemma noidsren:
forall (term : Type) (Ids_term : Ids term) (Rename_term : Rename term) (Subst_term : Subst term),
  SubstLemmas term -> Notunit term -> forall (s : term) , ~s.[ren (+1)] = ids 0.
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
move/(injids _ ).
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

Instance Notunit_term : Notunit term.
exists (ids 0,ids 1).
discriminate.
Defined.



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
| ty_var0 Γ A : wfTy Γ A  -> ty  (A::Γ) A.[ren(+1)] (ids 0)
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

Lemma ty_wfty Γ t A (w:Γ |- t : A) : wfTy Γ A.
  (* * wfCtx Γ) . *)
        (* with lemma61' Γ A (wA: Γ |- A)   : wfCtx Γ. *)
  elim:Γ  A t /w.
  + move => Γ A wfA.
    now apply:weakening_type.
  +  move => Γ s A B ct .
     (* move => [wfA wfΓ] cu . *)
     move => wfA cu.
     (* case/lemma61:(ct) => wfA wfΓ. *)
     have wfΓB : wfCtx (B::Γ) by constructor.
     (* split => //. *)
     now apply :weakening_type.
Defined.

Lemma ty_wfctxt Γ t A (w:Γ |- t : A) : wfCtx Γ.
Proof.
  now elim:Γ  A t /w ; constructor.
Defined.

Lemma wfty_wfctxt Γ A (w:Γ |- A) : wfCtx Γ.
Proof.
  elim:Γ  A  /w => //.
  +  intros.
     apply:ty_wfctxt.
     eauto.
Defined.


(* *****************


Unicité du jugement de typage


****************** *)

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  eq_rect x P u y p.

Definition ap := f_equal.


Lemma uniq_wfctxt_aux Γ Γ'  (wΓ :wfCtx Γ) (wΓ':wfCtx Γ')(eΓ : Γ=Γ') :
  transport eΓ wΓ = wΓ'
with uniq_wfty_aux Γ Γ' A A' (wA : Γ |- A) (wA' : Γ' |- A') (eΓ : Γ = Γ') (eA : A=A') :
  transport(P:= fun Γ => Γ |- _) eΓ (transport (P:=fun A => _ |- A) eA wA) = wA'
with uniq_term_aux Γ Γ' A A' t t' (wt:Γ|-t:A) (wt':Γ'|- t':A')
  (eΓ : Γ = Γ') (eA : A = A') (et : t = t'):
  transport( P:= fun t => _ |- t : _) et
                (transport( P:= fun A' => _ |- _ : A') eA
                          (transport (P:= fun c=> c |- _ : _) eΓ wt )) = wt'.
Proof.  
  - case:Γ' / wΓ' Γ wΓ eΓ.
    + move => Γ wΓ eΓ.
      destruct wΓ.
      * rewrite eq_axiomK //=.
      * discriminate.
    + move => Γ' A' wA' Γ wΓ.
      case:Γ / wΓ.
      * discriminate.
      * move => Γ A wA eΓ.
        have [eA' eΓ'] := eΓ.
        subst.
        rewrite eq_axiomK /=.
        f_equal.
        apply:(uniq_wfty_aux _ _ _ _ _ _ erefl erefl).
  - case:Γ' A'/wA' Γ A wA eΓ eA.
    + move => Γ' wΓ' Γ A wA eΓ eA.
      destruct wA.
      * subst.
        rewrite eq_axiomK /=.
        f_equal.
        apply:(uniq_wfctxt_aux _ _ _ _ erefl).
      * discriminate.
    + move => Γ' A' t' u' wt' wu' Γ A wA.
      case :Γ A/wA.
      * discriminate.
      * move => Γ A t u wt wu eΓ eA.
        have [? ? ?] := eA.
        subst.
        rewrite eq_axiomK /=.
        f_equal.
        -- apply:(uniq_term_aux _ _ _ _ _ _ _ _ erefl erefl erefl).
        -- apply:(uniq_term_aux _ _ _ _ _ _ _ _ erefl erefl erefl).
  - case:Γ' A' t' / wt' Γ t A wt eΓ eA et.
    + intros.
      destruct wt.
      * have [eA' eΓ'] := eΓ; subst.
        rewrite !eq_axiomK //=.
        f_equal.
        -- apply:(uniq_wfty_aux _ _ _ _ _ _ erefl erefl).
      * exfalso.
        apply:noidsren.
        exact:et.
    + move => Γ' t' A' B' wt'  wB Γ t A wt eΓ eA et.
    destruct wt.
      * exfalso.
        apply:noidsren.
        exact:(esym et).
      * have [eB eΓ'] := eΓ; subst.
        refine ((fun es eA' => _) (lift_injn _ _ _ et) (lift_injn _ _ _ eA)).
        subst.
        rewrite !eq_axiomK //=.
        f_equal.
        -- apply:(uniq_term_aux _ _ _ _ _ _ _ _ erefl erefl erefl).
        -- apply:(uniq_wfty_aux _ _ _ _ _ _ erefl erefl).
Defined.

Definition uniq_term Γ A t (e e':Γ|- t:A) : e = e' :=
  uniq_term_aux e e' erefl erefl erefl.

Definition uniq_wfctxt Γ (e e':wfCtx Γ) : e = e'  :=
  uniq_wfctxt_aux e e' erefl.

Definition uniq_wfty Γ A (e e':Γ|- A) : e = e' := uniq_wfty_aux e e' erefl erefl.


(* ************************

Substitutions


**************************** *)

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
     apply:ty_wfty; eauto.
  + apply: (subst_term_rien  ) => //; eauto.
  + apply: (subst_term_rien  ) => //; eauto.
Qed.

(* *****************

Composition des substitutions

***************** *)
Definition Ids_nat : Ids nat := id. 

(* σ o τ *)
Definition comp_subst (σ τ:substs) :=
  mkseq ( ((get σ) >> (get τ))) (size σ).
Lemma comp_subst_eq_aux σ τ t:
  [seq (get σ >> get τ) i | i <- iota 0 (size σ)] = [seq ((t :: σ)``_i).[get τ] | i <- iota 1 (size σ)].
  rewrite (iota_addl (1) (0)).
  rewrite -map_comp.
  cbn.
  apply:eq_map.
  move => n //=.
Qed.
Lemma comp_subst_eq σ τ t : comp_subst σ τ = [seq (get (t :: σ) >> get τ) i | i <- iota 1 (size σ)].
  apply:comp_subst_eq_aux.
  Qed.


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
      now rewrite -comp_subst_eq.
    + have tyA := lemma8 wτ t0.
      (* set t' := (t in E|- t:_). *)
      (* have et' : t' = t.[get τ] by reflexivity. *)
      refine (eq_rect _ (fun z => E |- _ : z) tyA _ _).
      asimpl.
      apply:subst_typ_rien .
      exact :w.
      move => n ltn /=.

      have ltnσ:n < size σ by rewrite (size_ty_substs wσ).
      
      rewrite (get_map_gen(H:=Ids_nat)) ?size_iota //.
      cbn.
      rewrite [(iota _ _)``_n]/get.
      rewrite nth_iota //.
Qed.

(* *************

substitution identité

 ************** *)


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
Lemma eq_subst B (Γ Δ:list B) A :
  mkseq (fun n : nat => ids (n + size (Δ ++ [:: A]))) (size Γ) =
  [seq ids (n + size Δ) | n <- iota 1 (size Γ)].
  (* TODO : factoriser avec comp_subst_eq_aux *)
      cbn.
      rewrite -/(comp_subst _ _).
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
Qed.
Lemma id_subst Γ Δ (w:wfCtx( Δ++Γ))  : ty_substs (Δ++Γ) Γ
                                           (mkseq (fun n => ids (n+size Δ)) (size Γ)).
  elim:Γ Δ w.
  - now constructor.
  - intros A Γ IH Δ w.
    apply :tysNext.

    + specialize (IH (Δ ++ A::nil)).
      move:w.
      rewrite -cat_rcons -cats1 => /IH w.
      now rewrite -(eq_subst Γ Δ A).
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
          constructor.
          now inversion w.
        }
        have wA : Γ |- A by inversion w.
        apply:(subst_typ_rien wA).
        move => n ltn.
        rewrite (get_map_gen (H:=Ids_nat)).
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
        rewrite (get_map_gen (H:=Ids_nat)) ?size_iota //.
        cbn.
        rewrite (get_map_gen  (H:=Ids_nat))?size_iota //.
        asimpl.
        congr ids.
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

(* Definition needed := @wfCtx_mut (fun _ _ => Type). *)

(*
Inductive ty : ctx -> term -> term  -> Type :=
| ty_var0 Γ A : wfCtx (A :: Γ) -> ty  (A::Γ) A.[ren(+1)] (ids 0)
| ty_termS Γ s A B : Γ |- s : A -> wfTy Γ B -> (B::Γ) |- s.[ren(+1) ] : A.[ren(+1)]
with wfCtx : ctx -> Type :=
     | wfEmpty : wfCtx nil
     | wfCtxNext Γ A :  wfCtx Γ -> wfTy Γ A -> wfCtx (A::Γ)
with wfTy :  ctx ->   term -> Type :=
  | wfUnit Γ : wfCtx Γ -> Γ |- tyUnit
  | wfAr Γ A t u : Γ |- t : A -> Γ |- u : A -> Γ |- (tyAr A t u)
where "Gamma |- A" := (wfTy Gamma A) and
 "Gamma |- s : A" := (ty Gamma A s).

Scheme wfCtx_mut := Induction for wfCtx Sort Type
with wfTy_mut := Induction for wfTy Sort Type
with ty_mut := Induction for ty Sort Type.

*)
Axiom myadmit : forall {A:Type} , A.

(*
*******

Soit U un type tel que pour tous x y, x = y

Alors U vérifie UIP

La preuve est similaire la preuve de égalité décidable -> UIP

Il suffit de montrer que tout fonction f: forall y, x = y -> x = y
est injective. Pour cela, il suffit de construire un retract.
Pour cela il suffit de montrer que f (e o e') = f e o e' par destruction de e'
(ou de e selon comment est défini la composition des chemins), puis de prendre
e = 1.

*********

*)

Definition comp_eq A (x y z:A) (e:x=y) (e':y=z) : x=z.
  now destruct e'.
Defined.

Lemma comp_eql A (x y  :A) (e:x=y)  : comp_eq erefl e = e.
  now destruct e.
Defined.  

Lemma comp_eq_assoc A (w x y z :A) (e:w=x) (e':x=y) (e'':y=z) :
  comp_eq e (comp_eq e' e'') = comp_eq (comp_eq e e') e''.
  destruct e''.
  now destruct e'.
Defined.

Lemma comp_eq_invl A (x y:A) (e:x=y) : comp_eq (esym e) e = erefl.
now  destruct e.
Defined.
Section Hedberg.
  Variable (U:Type) (x:U) (f:forall y, x = y -> x = y).


  Lemma nat_transf_f y (e:x=x) (e':x=y) :
    f (comp_eq e e') =comp_eq (f e) e' .
  Proof.
    now destruct e'.
  Qed.

  Lemma inj_f y (e:x=y) : e = comp_eq  (esym (f erefl)) (f e).
    have h:=nat_transf_f erefl e.
    rewrite comp_eql in h.
    rewrite h.
    set z := f _.
    clearbody z.
    rewrite comp_eq_assoc comp_eq_invl comp_eql.
    reflexivity.
  Defined.
End Hedberg.

Section AllEqualsUIP.
  Variables (T:Type).
  Hypothesis (allequals : forall (x y:T), x = y).

  Lemma allequals_eqirrelevance (x y:T) (e e':x=y) : e=e'.
    have hinj_f  := inj_f (fun y _ => allequals x y) e.
    have hinj_f'  := inj_f (fun y _ => allequals x y) e'.
    rewrite hinj_f hinj_f'.
    reflexivity.
  Qed.

  Lemma allequals_axiomK (x:T) : all_equal_to (erefl x).
    move => e.
    apply:(allequals_eqirrelevance e(erefl x) ).
  Qed.
End AllEqualsUIP.


(* avec l'univalence, se déduit des deux lemmes précéddents *)
Lemma uniq_wfctxt_wfty Γ A (w w': Γ |- A) :
  (uniq_wfctxt (wfty_wfctxt w) (wfty_wfctxt w')) =
   ap (@wfty_wfctxt Γ A) (uniq_wfty w w') .
  apply:allequals_eqirrelevance.
  apply:uniq_wfctxt.
Qed.


Section testtransport.
  Variables (A:Type) (B:A -> Type)( f:forall a:A, B a -> Type) (a a' : A) (b:B a) (x:f b)
  (e:a=a').

  Definition transport_dep : f (transport e b).
  destruct e.
  exact x.
  Defined.
End testtransport.
Section testtransport2.
  Variables (A:Type) (A':Type) (C:A -> A') (B: A' -> Type) ( f:forall a:A, B (C a) -> Type)
            (a a' : A) (b:B (C a)) (x:f b) (e:a=a') (ec:C a = C a').

  Definition transport_dep2 : f (transport ec b).
    refine (match ec with _ => _ end).
    Abort.
  (* je ne pense pas que ce soit possible *)
End testtransport2.

Record Model :=
  Build_Model {
      Tstar : Type;
      Tarrow : forall (Γ : ctx) (sΓ : Type),
          forall (A : term ) (sA : sΓ -> Type) (t u : term),
            Γ |- t : A -> Γ |- u : A ->
            forall (st su : forall γ, sA γ),
            sΓ -> Type}.

Lemma transportyop Γ A  (P: wfCtx Γ -> Type)
      (wA wA':Γ|-A) rΓ:
    (transport (P:=[eta P ]) (uniq_wfctxt (wfty_wfctxt wA) (wfty_wfctxt wA')) rΓ)
  =
      (transport (P:=fun w => P  (wfty_wfctxt w)) (uniq_wfty wA wA') rΓ).
  have h := uniq_wfctxt_wfty wA wA'.
  unfold ap in h.
  unfold f_equal in h.
  revert h.
  destruct (uniq_wfty wA wA'); cbn.
  move => -> //.
Qed.
Arguments transport {A} P {x y} _ _.
Definition wfCtx_mut_orig := @wfCtx_mut.

Module test.
Axiom wfCtx_mut : (
forall (P : forall c : ctx, wfCtx c -> Type) (P0 : forall (c : ctx) (t : term) (w: c |- t), P c (wfty_wfctxt w) -> Type)
  (Pt : forall (Γ : ctx) (A t  : term) (wt: Γ |- t : A), forall (wΓ: P Γ _), P0 Γ A (ty_wfty wt) wΓ -> Type),
P [::] wfEmpty ->
(* extension des contexte *)
forall Pext : (forall (Γ : ctx) (A : term) (* (w : wfCtx Γ), *),
    forall w0 : Γ |- A,forall (γ : P Γ _),  P0 Γ A w0 γ -> P (A :: Γ) (wfCtxNext  w0)),
(* tyUnit *)
(forall (Γ : ctx) (w : wfCtx Γ) (γ: P Γ w) , P0 Γ tyUnit (wfUnit w) γ) ->
(* pour la flèche *)
(forall (Γ : ctx) (A t u : term) (w0 : Γ |- t : A) (w1 : Γ |- u : A)
   (wA := ty_wfty w0)
   (rΓ : P Γ (wfty_wfctxt wA))
    (rA : P0 Γ A wA rΓ)
    (* (rA' : _), *)
    (rA' := transport_dep (f:=P0 Γ A) rA (uniq_wfty _ _))
    (Pt'' :=  (Pt Γ A u w1 (transport (fun z => P Γ z)
                                        (uniq_wfctxt
                                             (wfty_wfctxt wA)
                                             (wfty_wfctxt (ty_wfty w1))) 
                                        rΓ)))
 (* "P0 Γ A (ty_wfty w1) (transport (uniq_wfctxt (wfty_wfctxt wA) (wfty_wfctxt (ty_wfty w1))) rΓ)" *)
    (Pt' := transport
              (fun z => P0 Γ A (ty_wfty w1) z -> Type)
              (transportyop (P:=@P Γ) (ty_wfty w1) rΓ ) (Pt Γ A u w1 (transport _
                                        (uniq_wfctxt
                                             (wfty_wfctxt wA)
                                             (wfty_wfctxt (ty_wfty w1))) 
                                        rΓ))),
    Pt Γ A t w0 rΓ rA -> Pt' rA' ->
    P0 Γ (tyAr A t u) (wfAr w0 w1) (transport _ (uniq_wfctxt _ _) rΓ)) ->
(forall (Γ : seq term) (A : term) (wA : Γ |- A) 
   (rΓ : P Γ _) 
   (rA : P0 Γ A wA rΓ)
   (rΓext :=  (Pext Γ A wA rΓ rA))
   (rA' : P0 (A :: Γ) A.[ren (+1)] (ty_wfty (ty_var0 wA))
           (transport (P (A :: Γ)) (uniq_wfctxt (wfCtxNext wA) (wfty_wfctxt (ty_wfty (ty_var0 wA))))
              rΓext)),
      Pt (A :: Γ) A.[ren (+1)] (ids 0) (ty_var0 ( wA))
                              (transport _ (uniq_wfctxt _ _) rΓext)
                               rA')  ->
(*
(forall (Γ : ctx) (s A B : term) (t : Γ |- s : A),
 P1 Γ A s t -> forall w : Γ |- B, P0 Γ B w -> P1 (B :: Γ) A.[ren (+1)] s.[ren (+1)] (ty_termS t w)) ->
*)
forall (c : ctx) (w : wfCtx c), P c w).

(*
(forall (Γ : seq term) (A : term) (wA : Γ |- A) (rΓ : P Γ (wfty_wfctxt wA)) (rA : P0 Γ A wA rΓ),
 let rΓext := Pext Γ A wA rΓ rA in
 forall
   rA' : P0 (A :: Γ) A.[ren (+1)] (ty_wfty (ty_var0 (wfCtxNext wA)))
           (transport (P (A :: Γ))
              (uniq_wfctxt (wfCtxNext wA) (wfty_wfctxt (ty_wfty (ty_var0 (wfCtxNext wA))))) rΓext),
*)
Parameter (Tstar:Type).
Arguments transport_dep [A B] f [a a' b] _ _.
Definition tTarrow :=
   (forall (Γ : ctx) (A t u : term) (wt : Γ |- t : A) (wu : Γ |- u : A) 
          (rΓ : Type) (rA : rΓ -> Type),
        (forall γ : rΓ, rA γ) ->
        transport (fun z : Type => (z -> Type) -> Type) (transportyop (ty_wfty wu) rΓ)
          (fun
             wA : transport (fun _ : wfCtx Γ => Type)
                    (uniq_wfctxt (wfty_wfctxt (ty_wfty wt)) (wfty_wfctxt (ty_wfty wu))) rΓ -> Type =>
           forall
             γ : transport (fun _ : wfCtx Γ => Type)
                   (uniq_wfctxt (wfty_wfctxt (ty_wfty wt)) (wfty_wfctxt (ty_wfty wu))) rΓ, 
           wA γ)
          (transport_dep (fun (_ : Γ |- A) (γ : Type) => γ -> Type) rA
             (uniq_wfty (ty_wfty wt) (ty_wfty wu))) ->
        transport (fun _ : wfCtx Γ => Type) (uniq_wfctxt (wfty_wfctxt (ty_wfty wt)) (ty_wfctxt wu)) rΓ ->
        Type).


Lemma transport_trivial A (B:A -> Type) (a a':A) (e:a=a') (t:B a) :
  transport (fun _ => B a) e t = t.
now destruct e.
Qed.
Lemma transport_trivial_trivial A (B:Type) (a a':A) (e:a=a') (t:B ) :
  transport (fun _ => B ) e t = t.
now destruct e.
Qed.
Definition tvraiTarrow := forall Γ A t u (wt : Γ |- t : A) (wt : Γ |- u : A)
                            (sΓ:Type) (sA : sΓ -> Type),
                            forall (st su :forall γ:sΓ, sA γ) (γ:sΓ) , Type.

Definition injectarrow (x:tvraiTarrow) : tTarrow.
  red in x.
  red.
  move => Γ A t u wt wu rΓ rA rs ru γ.
  apply:(x Γ A t u wt wu rΓ rA); last first.
  - move:γ.
    clear.
    rewrite transport_trivial_trivial.
    exact:id.
  - exact:rs.
  - move:ru.
    clear.
    set (e:= transportyop _ _).
    clearbody e.
    cbn in e.
    set trdep := transport_dep _ _ _.
    cbn in trdep.
    change trdep with
    (transport ( fun A => A -> Type)
       (erefl (transport (fun _ : Γ |- A => Type) (uniq_wfty (ty_wfty wt) (ty_wfty wu)) rΓ
       )) trdep).
    move:(erefl _) => eq.
    have e' := e.
    destruct e.
    cbn.
    set euctxt := uniq_wfctxt _ _ in eq *.
    clearbody euctxt.
    destruct euctxt.
    cbn in *.
    move => h γ; specialize (h γ).
    move:h.
    have syminv := esymK eq.
    rewrite <- syminv.
    move:(esym eq).
    clear.
    move => x.
    refine (match x with erefl => _ end).
    destruct x.
    destruct 1.
    move:trdep => trdep'.
    destruct eq.
    change (
        (forall γ , transport (fun A0 : Type => A0 -> Type)
                         eq trdep (transport (fun z => z rΓ) erefl γ)) -> forall γ : rΓ, rA γ).
    move:erefl => e''.
    destruct eq.
    cbn.
  change ((forall γ : transport (fun _ : Γ |- A => Type) euty rΓ,
              transport_dep (fun (_ : Γ |- A) (γ0 : Type) => γ0 -> Type) rA euty
                            (transport id e'' (transport (fun z => transport _ z rΓ) (erefl euty)  γ))) ->
  forall γ : rΓ, rA γ).
  move:erefl.
  change ((fun euty' => forall e : euty' = euty,
  (forall γ : transport (fun _ : Γ |- A => Type) euty' rΓ,
   transport_dep (fun (_ : Γ |- A) (γ0 : Type) => γ0 -> Type) rA euty
                 (transport id e'' (transport (fun z => transport _ z rΓ) e γ))) ->
  forall γ : rΓ, rA γ) euty).
  set P := (P in P _).
  suff Px euty' : P euty' by apply:Px.
  subst P ;cbn.
  move => eueuty.
  destruct euty'.
  cbn.
  move => h γ.
  specialize (h γ).
  move:h.
  clear.
  unfold transport_dep.
  destruct euty.
  rewrite -eueuty.
  symmetry in eueuty.
  destruct eueuty.
  destruct 1.


  pattern euty at 1 3.
  move:{1 3}euty.
  destruct euty.
  change (forall γ : transport (fun _ : Γ |- A => Type) euty rΓ,
   transport_dep (fun (_ : Γ |- A) (γ0 : Type) => γ0 -> Type) rA euty (transport id e'' γ)) ->
  forall γ : rΓ, rA γ
    unfold transport_dep.
    have euty' :=euty.
    destruct euty'.
    have eutyrefl : euty = erefl.
    apply:allequals_axiomK.
    admit.
    destruct eutyrefl.
    have 
    clearbody euty.
    destruct euty.
    rewrite (allequals_axiomK (x:=uni''); cbn.
    clear.
    rewrite /trdep.
    clearbody euty.
    destruct euty.
    cbn.
    exact :id.
    rewrite allequals_axiomK.
    change 
  ((forall γ , trdep (transport (fun z => z rΓ) erefl γ)) ->
  forall γ : rΓ, rA γ).
    move:erefl => e'''.
    clear.
    have yop := transport_trivial_trivial (A:=Γ|-A) (B:=Type)
                                          (uniq_wfty (ty_wfty wt) (ty_wfty wu)) rΓ.
    destruct yop.
     (transport_trivial_trivial _ _).
    change
  ((forall
     γ,
   transport (fun A0 : Type => A0 -> Type) eq
     (transport_dep (fun (_ : Γ |- A) (γ0 : Type) => γ0 -> Type) rA euty) γ) -> 
  forall γ : rΓ, rA γ).
    unfold trdep.
    set euty := uniq_wfty _ _.
    unfold transport_dep.
    clearbody euty.
    destruct e'.
    clear.
    rewrite transport_trivial_trivial.
    set eu := uniq_wfctxt  _ _.
    set tr := transport _ _ _.
    have eeu : eu = erefl.
    rewrite allequals_axiomK.
    clearbody eu.
    move:(uniq_wfctxt _ _).
    refine (match e in _ = b with erefl => _ end).
    destruct e.
    unfold transportyop.

Lemma monTarrow:tTarrow.
  red.
  move => Γ A t u wt wu rΓ rA truc.
  rewrite transport_trivial_trivial.

Parameter (Tarrow: (forall (Γ : ctx) (A t u : term) (wt : Γ |- t : A) (wu : Γ |- u : A) 
          (rΓ : Type) (rA : rΓ -> Type),
        (forall γ : rΓ, rA γ) ->
        transport (fun z : Type => (z -> Type) -> Type) (transportyop (ty_wfty wu) rΓ)
          (fun
             wA : transport (fun _ : wfCtx Γ => Type)
                    (uniq_wfctxt (wfty_wfctxt (ty_wfty wt)) (wfty_wfctxt (ty_wfty wu))) rΓ -> Type =>
           forall
             γ : transport (fun _ : wfCtx Γ => Type)
                   (uniq_wfctxt (wfty_wfctxt (ty_wfty wt)) (wfty_wfctxt (ty_wfty wu))) rΓ, 
           wA γ)
          (transport_dep (fun (_ : Γ |- A) (γ : Type) => γ -> Type) rA
             (uniq_wfty (ty_wfty wt) (ty_wfty wu))) ->
        transport (fun _ : wfCtx Γ => Type) (uniq_wfctxt (wfty_wfctxt (ty_wfty wt)) (ty_wfctxt wu)) rΓ ->
        Type)).

Definition needed   := @wfCtx_mut (fun _ _ => Type) (fun _ _ _ γ => γ -> Type) (fun _ _ _ _ wΓ wA => forall γ:wΓ, wA γ) unit 
(fun _ _ _ d  A => sigT A) (fun _ _ _ _ => Tstar) (@Tarrow).

Definition tneeded := ltac: (match (type of needed) with ?x => set (y:=x); cbn in y; exact y end).
Goal True.
 (match (type of needed) with ?x => set (y:=x)end).
 simpl in y.
 cbn in y.
    move => Γ A wA rΓ rA.
    move:(wfCtxNext wA) => w.
    set e:=(e in transport _ e).
    have e2 := e .
    move => rA'.
    set e':=(e in transport _ e).

    have eqe: e = e' by apply:allequals_eqirrelevance; apply:uniq_wfctxt.
    set rA'' := rA'.
    clearbody rA''.
    rewrite transport_trivial_trivial in rA''.
  :w
     khave 
    have erA : rA'
    move => 
    destruct e'.
    subst.
    have eqe:e' =erefl.
    clearbody e'.
    rewrite transport_trivial_trivial.
    clearbody e'.
    have h := transport_trivial_trivial (A:=wfCtx (A::Γ)) (B:=Type) e {x:rΓ & rA x}.
    destruct h.
    rewrite transport_trivial_trivial.
    rewrite (transport_trivial (A:=wfCtx.
Goal True.
 (match (type of needed) with ?x => set (y:=x)end).
 simpl in y.
 P0 := fun c _ _ => P c -> Type

                         Γ A t u (semΓ : Type) (semA : semΓ -> Type) (semt :forall γ:semΓ, semA γ)
                         (semu :∀ γ:semΓ, semA γ) : semΓ -> Type
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
