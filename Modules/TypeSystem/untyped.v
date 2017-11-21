(* 
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** End:***
*)

Require Import Autosubst.Autosubst.


Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.


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

(* Fin Context.v *)

(* Examples/Poplmark.v *)
Notation "Gamma `_ x" := (dget Gamma x).
Notation "Gamma ``_ x" := (get Gamma x) (at level 3, x at level 2,
  left associativity, format "Gamma ``_ x").

Inductive term : Type :=
  | TeVar (x:var).

Inductive type : Type :=
| tyUnit
| tyAr : type -> term -> term -> type.

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.

Instance SubstLemmas_term : SubstLemmas term. derive. Qed.
Instance HSubst_term : HSubst term type. derive. Defined.

Class HSubstLemmas' (inner outer : Type)
  {Ids_inner : Ids inner} {Subst_inner : Subst inner}
  {HSubst_inner_outer : HSubst inner outer} :=
{
  hsubst_id' (s : outer) :
    s.|[ids : var -> inner] = s;
  hsubst_comp' (theta eta : var -> inner) (s : outer) :
    s.|[theta].|[eta] = s.|[theta >> eta]
}.
Instance HSubstLemmas_term : HSubstLemmas'(inner := term)(outer := type).
Admitted.
(*
Instance Ids_type : Ids type.
cbn.
red.
derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
Instance SubstLemmas_type : SubstLemmas type. derive. Qed.

Instance SubstHSubstComp_type_term : SubstHSubstComp type term. derive. Qed.
*)


Definition Ctx := list type.



Definition substs := list term.


Fixpoint subst_typ (σ : var -> term) (A:type) :=
  match A with
    tyUnit => tyUnit
  | tyAr A t u => tyAr (subst_typ σ A) (t.[σ]) (u.[ σ])
  end.
(* Definition subst_term (σ : substs) (t:term) := t.[get σ]. *)
(*
  match t with
    TeVar n => σ``_n
  end.
*)

(*
Fixpoint subst_typ (σ : substs) (A:type) :=
  match A with
    tyUnit => tyUnit
  | tyAr A t u => tyAr (subst_typ σ A) (subst_term σ t) (subst_term σ u)
  end.
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
Inductive ty : Ctx -> type -> term  -> Type :=
| ty_var0 Γ A : (A::Γ) |- (ids 0) :  (subst_typ (up ids) A)
| ty_termS Γ s A B : Γ |- s : A -> (B::Γ) |- s.[up ids] : (subst_typ (up ids) A)
where "Gamma |- s : A" := (ty Gamma A s).

Inductive wfTy (Γ:Ctx) : type -> Type :=
  | wfUnit : Γ |- tyUnit
  | wfAr A t u : Γ |- t : A -> Γ |- u : A -> Γ |- (tyAr A t u)
where "Gamma |- A" := (wfTy Gamma A).

Inductive ty_substs Δ : Ctx -> substs -> Type :=
| tysEmpty : ty_substs Δ nil nil
| tysNext Γ (A:type) t σ : ty_substs Δ Γ σ
                           -> wfTy Γ A
                           -> Δ |- t : subst_typ (get σ) A ->
                                     ty_substs Δ (A::Γ) (t::σ).


Set Bullet Behavior "Strict Subproofs".
(* Fixpoint ty_fix Γ t := *)
(*   match Γ with *)
(*     nil => None *)
(*   | A :: Γ' => *)
Lemma lemma8 Δ Γ A σ t (tyσ : ty_substs Δ Γ σ) (tyt : Γ |- t : A)
  : Δ |- (t.[get σ]) : (subst_typ (get σ) A).
  elim :Γ σ  /tyσ t tyt.
  - (* impossible *)
    intros;
    inversion tyt.
  - move =>  Γ Aσ tσ σ tyσ IH.
    move => wfAσ tytσ t.
    move => tyt.
    inversion tyt.
    subst.
    + cbn.
    induction tyt.
    + cbn.
    induction t as [n].
    + destruct n as [|n].
      * cbn.
        (* tyt me dit que Aσ = A *)
        (* ici je voudrais dire que subst_typ  _ A = A*)
        inversion tyt.
        -- subst.
           cbn.
           set A' := (A in Δ |- tσ : A).
           set A'' := (A in Δ |- tσ : A) in tytσ.
           suff :A' = A'' by congruence.
           subst A' A''.
           intros. rewrite x.
           congruence.
           move:tytσ.
           congr @ty. (_=_).
        congruence.
    cbn.
    +  
  cbn.k