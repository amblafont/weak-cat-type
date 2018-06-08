(* Set Primitive Projection makes the definition of the functional relation much faster ! *)
(*
Dans cette version, je fais la version paranoide pour la relation fonctionnelle
30 min de compilation !!
Ce qui est bizarre, c'est que je n'ai pas eu besoin de montrer que la syntaxe est hprop
 *)
(* wk_subTmm wk_subTym *)
Require Import ssreflect.
Require Import Modules.TypeSystem.FromHottLibPrimProj.Overture.
Require Import Modules.TypeSystem.FromHottLibPrimProj.PathGroupoids.
Require Import Modules.TypeSystem.FromHottLibPrimProj.Contractible.
Require Import Modules.TypeSystem.FromHottLibPrimProj.Trunc.
Require Import Modules.TypeSystem.FromHottLibPrimProj.Sigma.
Require Import Modules.TypeSystem.FromHottLibPrimProj.Prod.
Require Import Modules.TypeSystem.FromHottLibPrimProj.Equivalences.

(* fait des preuves moins dégueu que tauto ( teste h.1 h.2 h.1.1 h.1.2.2 etc.. )*)
Ltac get_from_hyp h :=
  exact h
  || let x := constr:(fst h) in get_from_hyp x
  || let x := constr:(snd h) in get_from_hyp x.

Ltac destruct_eqs h :=
  destruct (h^)
  (* || let x := constr:(fst h) in get_from_hyp' x *)
  (* || let x := constr:(snd h) in get_from_hyp' x *)
  || (let x := constr:(fst h) in destruct_eqs x)
  || (let x := constr:(snd h) in destruct_eqs x).

(* Definition test (x : nat * True) : nat := ltac:(get_from_hyp x). *)
(* From Modules Require Import stuff. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Dans cette version, isContr fait partie de l'inductif-inductif, et on a aussi
des isContr pour les termes/variables/types (afin de pouvoir faire la récurrence idoine
quand on définit la relation fonctionnelle sur les variables dans un contexte contractile).
*)





Notation "'Σ'  x .. y , P" := (sigT (fun x=> .. (sigT (fun y=> P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.

(* Class Is_contr (A : Type) := is_contr : Σ x , forall (y : A), x = y. *)
(* Class Is_hprop (A : Type) := is_hprop : forall (x y : A), Is_contr ( *)
(* Class Is_hset (A : Type) := is_hset : forall (x y : A), Is_hprop (x = y). *)
(* Instance hset_eq_hprop (A : Type) {sA : Is_hset A} (x y : A) :  Is_hprop (x  = y) := sA x y. *)

(* Definition ap {A B : Type} (f : A -> B) {x y : A} (e : x = y) : f x = f y := *)
(*   match e with eq_refl => eq_refl end. *)


Lemma transportb (A : Type) (x : A) (P : A -> Type) (y : A)(e : x = y)  (Py : P y) : P x.
Proof.
  by destruct e.
Defined.

Lemma transportb_dep (A : Type) (x : A) (P : A -> Type) (y : A) (e : x = y) (Py : P y) Z (e' : Z = transportb e Py)
      (Q : forall c, P c -> Type) (q : Q _ Py): Q _ Z.
  destruct e.
  exact (transportb (P := Q x) e' q).
Defined.
Definition  ap2 : forall (A B C : Type) (f : A -> B -> C) x x' y y' , x = y -> x' = y' -> f x x' = f y y'.
  destruct 1.
  destruct 1.
  reflexivity.
Defined.

Definition J A (x : A) (P : forall y, y = x -> Type) y (e : y = x) (Px : P x eq_refl) : P y e.
  by destruct e.
Defined.
Arguments J {A} {x} P {y} e _ .
Definition J' A (x : A) (P : forall y, x = y -> Type) y (e : x = y) (Px : P x eq_refl) : P y e.
  by destruct e.
Defined.
Arguments J {A} {x} P {y} e _ .
Arguments J' {A} {x} P {y} e _ .

Definition Empty_rect {P : Type} := False_rect P.

Infix "@" := (eq_trans) (at level 20).
(* Infix "@" := eq_trans (at level 60). *)

Inductive Conp :=
  nilp : Conp
| consp (Γ : Conp) (A : Typ)
with Typ :=
       starp (Γ : Conp)
     | arp  (Γ : Conp) (A : Typ)(t u : Tmp)
with Tmp :=
       vp (Γ : Conp) (A : Typ)(x : Varp)
     | coh (Γ : Conp)(Δ : Conp) (Δc : isContrp) (A : Typ) (Ac : isCTyp ) (σ : Subp)

           (* this dumt simplifies the statment of wk_subVarp (don't need to assume the wellfoundness of the
substitution/variable *)
     | dumt
with Varp :=
       | v0  (Γ : Conp) (A : Typ)
       | vS  (Γ : Conp) (A : Typ)(x : Varp) (B : Typ)
             (* dummy *)
       (* | vdum *)
with Subp :=
     | to_nilp (Γ : Conp)
     | to_consp (Γ : Conp) (Δ : Conp) (σ : Subp) (A : Typ) (t : Tmp)
with isContrp :=
       | isC_astarp
       | isC_consconsp (Γ : Conp) (Γc : isContrp)(T : Typ) (Tc : isCTyp) (z : Tmp) (zc : isCTmp)
with isCTyp :=
       | isC_starp (Γ : Conp) (Γc : isContrp)
       | isC_arp (Γ : Conp) (Γc : isContrp)(A : Typ) (Ac : isCTyp)
                 (t : Tmp) (tc : isCTmp)
                 (u : Tmp) (uc : isCTmp)
with isCTmp :=
       | isC_vp (Γ : Conp) (Γc : isContrp)(A : Typ) (Ac : isCTyp)(x : Varp) (xc : isCVarp)
       | isC_cohp (Γ : Conp)(Γc : isContrp)(Δ : Conp) (Δc : isContrp) (A : Typ)(Ac : isCTyp)
                  (σ : Subp) (σc : isCSubp)
                  (* simplifies the statment of subsubisCVarp *)
       | isC_dumt
with isCVarp :=
     | isC_vstarp 
     | isC_v0p (Γ : Conp) (Γc : isContrp)(T : Typ) (Tc : isCTyp) (z : Tmp) (zc : isCTmp)
     | isC_v1p (Γ : Conp) (Γc : isContrp)(T : Typ) (Tc : isCTyp) (z : Tmp) (zc : isCTmp)
     | isC_vSSp (Γ : Conp) (Γc : isContrp)(T : Typ) (Tc : isCTyp) (z : Tmp) (zc : isCTmp)
                (A : Typ) (Ac : isCTyp) (x : Varp) (xc : isCVarp)
with isCSubp :=
     | isC_to_astarp (Γ : Conp) (Γc : isContrp)(t : Tmp) (tc : isCTmp)
     | isC_to_consconsp (Γ : Conp) (Γc : isContrp)(Δ : Conp) (Δc : isContrp)(T : Typ) (Tc : isCTyp)
                        (z : Tmp) (zc : isCTmp)
                        (σ : Subp) (σc : isCSubp)
                        (t : Tmp) (tc : isCTmp)
                        (f : Tmp) (fc : isCTmp) .
       


Infix "▷" := consp (at level 68).
Notation "∙" := nilp.
(* Infix "▷S" := to_consp (at level 68). *)
Fixpoint wkTyp (Ex : Typ) (A : Typ) :=
  match A with
    starp Γ => starp (Γ ▷ Ex)
  | arp Γ A t u => arp (Γ ▷ Ex) (wkTyp Ex A) (wkTmp Ex t) (wkTmp Ex u)
  end
with  wkTmp (Ex : Typ) (t : Tmp) :=
        match t with
          vp Γ A x => vp (Γ ▷ Ex) (wkTyp Ex A) (vS Γ A x Ex)
        | coh Γ Δ Δc A Ac σ => coh (Γ ▷ Ex) Δ Δc A Ac (wkSubp Ex σ)
        | dumt => dumt
        end
with wkSubp (Ex : Typ) (σ : Subp) :=
       match σ with
         to_nilp Γ => to_nilp (Γ ▷ Ex)
       | to_consp Γ Δ σ A t => to_consp (Γ ▷ Ex) Δ (wkSubp Ex σ) A (wkTmp Ex t)
       end.

Definition arcons Γ A u : Typ := (arp (Γ ▷ A) (wkTyp A A) (vp (Γ ▷ A) (wkTyp A A) (v0 Γ A)) (wkTmp A u)).
Definition consconsp Γ A u : Conp := (Γ ▷ A) ▷ arcons Γ A u.

Definition wkwk {T} wk Γ Ex ux (x : T) :=
  wk (arcons Γ Ex ux) (wk Ex x ).

Definition wkwkTmp := wkwk wkTmp.
Definition wkwkTyp := wkwk wkTyp.
Definition wkwkSubp := wkwk wkSubp.

(* Definition wkwkVarp Γ Ex ux x : Varp := *)
(*   vS  (Γ ▷ Ex) (vS Γ )  (arcons Γ Ex ux) *)


Fixpoint wkisCTyp (Ex : Typ) (Exc : isCTyp) (u : Tmp)(uc : isCTmp) (Ac : isCTyp) :=
  match Ac with
    isC_starp Γ Γc => isC_starp (consconsp Γ Ex u) (isC_consconsp Γ Γc Ex Exc u uc)
  | isC_arp Γ Γc B Bc t1 t1c t2 t2c =>
    isC_arp (consconsp Γ Ex u) (isC_consconsp Γ Γc Ex Exc u uc)
            (wkwkTyp Γ Ex u B)
            (wkisCTyp Ex Exc u uc Bc )
            (wkwkTmp Γ Ex u t1)
            (wkisCTmp Ex Exc u uc t1c)
            (wkwkTmp Γ Ex u t2)
            (wkisCTmp Ex Exc u uc t2c)

  end
with wkisCTmp  (Ex : Typ) (Exc : isCTyp) (u : Tmp)(uc : isCTmp) (tc : isCTmp) :=
       match tc with
         isC_vp Γ Γc A Ac x xc =>
         isC_vp (consconsp Γ Ex u) (isC_consconsp Γ Γc Ex Exc u uc)
                (wkwkTyp Γ Ex u A)
                (wkisCTyp Ex Exc u uc Ac )
                (vS (Γ ▷ Ex) (wkTyp Ex A) (vS Γ A x Ex) (arcons Γ Ex u))
           (isC_vSSp Γ Γc Ex Exc u uc A Ac x xc)
        | isC_cohp Γ Γc Δ Δc A Ac σ σc => 
          isC_cohp (consconsp Γ Ex u) (isC_consconsp Γ Γc Ex Exc u uc)
                   Δ Δc A Ac 
                   (wkwkSubp Γ Ex u σ)
                   (wkisCSubp Ex Exc u uc σc)
        | isC_dumt => isC_dumt

       end
with wkisCSubp  (Ex : Typ) (Exc : isCTyp) (ux : Tmp)(uxc : isCTmp) (σc : isCSubp) :=
       match σc with
         isC_to_astarp Γ Γc t tc => 
         isC_to_astarp (consconsp Γ Ex ux) (isC_consconsp Γ Γc Ex Exc ux uxc)
           (wkwkTmp Γ Ex ux t)
            (wkisCTmp Ex Exc ux uxc tc)

       | isC_to_consconsp Γ Γc Δ Δc A Ac u uc σ σc t tc f fc =>
         isC_to_consconsp
           (consconsp Γ Ex ux) (isC_consconsp Γ Γc Ex Exc ux uxc)
           Δ Δc A Ac u uc
           (wkwkSubp Γ Ex ux σ)
           (wkisCSubp Ex Exc ux uxc σc)
           (wkwkTmp Γ Ex ux t)
           (wkisCTmp Ex Exc ux uxc tc)
           (wkwkTmp Γ Ex ux f)
           (wkisCTmp Ex Exc ux uxc fc)
       end.

Class Dummy (A : Type) := dummy : A.
Instance dummyConp : Dummy Conp := nilp.
Instance dummyTyp : Dummy Typ := starp dummy.
Instance dummyVarp : Dummy Varp := v0 dummy dummy.
(* Instance dummyTmp : Dummy Tmp := vp dummy dummy dummy. *)
Instance dummyTmp : Dummy Tmp := dumt.

(* E ⊢ σ : _ *)
Fixpoint subVarp (E : Conp) (σ : Subp) (x : Varp) : Tmp :=
  match x with
    v0 Γ A => if σ is to_consp E' Δ σ' A' t then t else  dummy
  | vS Γ A x B => if σ is to_consp E' Δ σ' B' t then subVarp E' σ' x else dummy
  end.
Fixpoint  subTmp  (E : Conp) (σ : Subp) (t : Tmp) :=
        match t with
          vp Γ A x => subVarp E σ x
        | coh Γ Δ Δc A Ac δ => coh E Δ Δc A Ac (subSubp E σ δ)
        | dumt => dumt
        end
          (* E ⊢ σ : ?1 et ?1 ⊢ δ : ?2 *)
with subSubp  (E : Conp) (σ : Subp) (δ : Subp) :=
       match δ with
         (* There is only one morphism to the empty context *)
         to_nilp Γ => to_nilp E
         (* Γ ⊢ (δ , t) : Δ , A  and  E ⊢ σ : Γ
           donc la composée donne E ⊢ (δ[σ], t[σ]) : Δ , A
          *)
       | to_consp Γ Δ δ A t =>
         to_consp E Δ (subSubp E σ δ) A (subTmp E σ t)
       end.

Fixpoint subTyp (E : Conp) (σ : Subp) (A : Typ) :=
  match A with
    starp Γ => starp E
  | arp Γ A t u => arp E (subTyp E σ A) (subTmp E σ t) (subTmp E σ u)
  end.

(* used for sub*w *)
Fixpoint subsubTyp G H σ δ A :
  subTyp G σ (subTyp H δ A) = subTyp G (subSubp G σ δ) A
  with subsubTmp G H σ δ t :
  subTmp G σ (subTmp H δ t) = subTmp G (subSubp G σ δ) t
  with subsubVarp G H σ δ x :
  subTmp G σ (subVarp H δ x) = subVarp G (subSubp G σ δ) x
  with subsubSubp G H σ δ ε :
  subSubp G σ (subSubp H δ ε) = subSubp G (subSubp G σ δ) ε.
Proof.
  - refine (
      match A with
        starp Γ => _
      | arp Γ A t u => _
      end).
    + reflexivity.
    + cbn.
      (* f_ap. *)
      congr arp.
      *  apply:subsubTyp.
      *  apply:subsubTmp.
      *  apply:subsubTmp.
  - refine (
        match t with
          vp Γ A x => _
        | coh Γ Δ Δc A Ac δ =>  _
        | dumt => _
        end); cbn.
    + by apply:subsubVarp.
    (* + f_ap. *)
    + f_equal.
      by apply:subsubSubp.
    + reflexivity.
  - refine ( match x with
         v0 Γ A => if δ is to_consp E' Δ σ' A' t then _ else _
       | vS Γ A x B => if δ is to_consp E' Δ σ' A' t then _ else _
             end); cbn.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + apply:subsubVarp.
  - refine (match ε with
         to_nilp Γ => _
       | to_consp Γ Δ ε A t => _
       end).
    + reflexivity.
    + cbn.
      (* f_ap. *)
      congr to_consp.
      * apply:subsubSubp.
      * apply:subsubTmp.
Defined.

(* When well typed, we have Ex = Ex'
However, we need the more general version to prove sub_cons_wkisCTyp
because different Ex do  come from different untyped subterms
 *)
Fixpoint sub_cons_wkTyp G H σ Ex Ex' σt A :
  subTyp G σ A = subTyp G (to_consp G H σ Ex σt) (wkTyp Ex' A)
with sub_cons_wkTmp G H σ Ex Ex' σt t:
  subTmp G σ t = subTmp G (to_consp G H σ Ex σt) (wkTmp Ex' t)
with sub_cons_wkSubp G H σ Ex Ex' σt δ :
  subSubp G σ δ = subSubp G (to_consp G H σ Ex σt) (wkSubp Ex' δ).
  Proof.
  - refine (
      match A with
        starp Γ => _
      | arp Γ A t u => _
      end); cbn.
    + reflexivity.
    + cbn.
      (* f_ap. *)
      congr arp.
      *  apply:sub_cons_wkTyp.
      *  apply:sub_cons_wkTmp.
      *  apply:sub_cons_wkTmp.
  - refine (
        match t with
          vp Γ A x => _
        | coh Γ Δ Δc A Ac δ =>  _
        | dumt => _
        end); cbn.
    + reflexivity.
    +
    (* f_ap. *)
      congr coh.
      by apply:sub_cons_wkSubp.
    + reflexivity.
  - refine (match δ with
         to_nilp Γ => _
       | to_consp Γ Δ δ A t => _
       end).
    + reflexivity.
    + cbn.
      (* f_ap. *)
      congr to_consp.
      *  apply:sub_cons_wkSubp.
      *  apply:sub_cons_wkTmp.
Defined.

  (*
Fixpoint sub_cons_wkTyp G H σ Ex σt A :
  subTyp G σ A = subTyp G (to_consp G H σ Ex σt) (wkTyp Ex A)
with sub_cons_wkTmp G H σ Ex σt t:
  subTmp G σ t = subTmp G (to_consp G H σ Ex σt) (wkTmp Ex t)
with sub_cons_wkSubp G H σ Ex σt δ :
  subSubp G σ δ = subSubp G (to_consp G H σ Ex σt) (wkSubp Ex δ).
Proof.
  - refine (
      match A with
        starp Γ => _
      | arp Γ A t u => _
      end); cbn.
    + reflexivity.
    + cbn.
      (* f_ap. *)
      congr arp.
      *  apply:sub_cons_wkTyp.
      *  apply:sub_cons_wkTmp.
      *  apply:sub_cons_wkTmp.
  - refine (
        match t with
          vp Γ A x => _
        | coh Γ Δ Δc A Ac δ =>  _
        | dumt => _
        end); cbn.
    + reflexivity.
    +
    (* f_ap. *)
      congr coh.
      by apply:sub_cons_wkSubp.
    + reflexivity.
  - refine (match δ with
         to_nilp Γ => _
       | to_consp Γ Δ δ A t => _
       end).
    + reflexivity.
    + cbn.
      (* f_ap. *)
      congr to_consp.
      *  apply:sub_cons_wkSubp.
      *  apply:sub_cons_wkTmp.
Defined.
*)

Fixpoint wk_subTyp 
         (G : Conp)
         (Ex : Typ)
         (* (Ew : Tyw Γ Ex) *)
         (* (Δ : Conp) *)
         (A : Typ)
         (σ : Subp)
         (* (Γw : Conw Δ) *)
  (* (Aw : Tyw Δ A) (σw : Subw Γ Δ σ) *)
  {struct A}: wkTyp Ex (subTyp G σ A) = subTyp (G ▷ Ex) (wkSubp Ex σ) A
with wk_subTmp 
         (G : Conp)
         (Ex : Typ)
         (* (Ew : Tyw Γ Ex) *)
         (* (Δ : Conp) *)
         (* (T : Typ) *)
         (t : Tmp)
         (σ : Subp)
         (* (Γw : Conw Δ) *)
         (* (Aw : Tyw Δ A) (σw : Subw Γ Δ σ) *)
           {struct t}
         : wkTmp Ex (subTmp G σ t) = subTmp (G ▷ Ex) (wkSubp Ex σ) t
(* I need the well formed judgement here *)
with wk_subVarp
         (G : Conp)
         (* (H : Conp) *)
         (Ex : Typ)
         (* (Ew : Tyw Γ Ex) *)
         (* (Δ : Conp) *)
         (* (T : Typ) *)
         (x : Varp)
         (σ : Subp)
         (* (Γw : Conw Δ) *)
         (* (Aw : Tyw Δ A) (σw : Subw Γ Δ σ) *)
           {struct x}
(*          : wkVarp Ex (subTmp G σ x) = subTmp (G ▷ Ex) (wkVarp Ex σ) x. *)
 :  wkTmp Ex (subVarp G σ x) = subVarp (G ▷ Ex) (wkSubp Ex σ) x

with wk_subSubp (G : Conp)
         (Ex : Typ)
         (δ : Subp)
         (σ : Subp)
  : wkSubp Ex (subSubp G δ σ) = subSubp (G ▷ Ex) (wkSubp Ex δ) σ.
Proof.
  -
    refine (
        match A with
          starp Γ => _
        | arp Γ A t u => _
        end).
    + reflexivity.
    + cbn.
      (* f_ap. *)
      congr arp.
      * apply wk_subTyp.
      * apply wk_subTmp.
      * apply wk_subTmp.
  - refine (
        match t with
          vp Γ A x => _
        | coh Γ Δ Δc A Ac σ =>  _
        | dumt => _
        end 
      ) ; last by reflexivity.
    + apply:wk_subVarp.
    + cbn.
      (* f_ap. *)
      congr coh.
      * apply:wk_subSubp.
  - refine ( match x with
         v0 Γ A => if σ is to_consp E' Δ σ' A' t then _ else _
       | vS Γ A x B => if σ is to_consp E' Δ σ' A' t then _ else _
             end).
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + cbn.
      apply:wk_subVarp.
  - refine (match σ with
         to_nilp Γ => _
       | to_consp Γ Δ σ A t => _
       end).
    + reflexivity.
    + cbn.
      (* f_ap. *)
      congr to_consp.
      * apply:wk_subSubp.
      * apply:wk_subTmp.
Defined.
(* Notation "∑" := @sigT. *)

Instance dummyisCVarp : Dummy isCVarp := isC_vstarp.
Instance dummyisContrp : Dummy isContrp := isC_astarp.
Instance dummyisCTyp : Dummy isCTyp := isC_starp (consp nilp (starp nilp)) dummy.
(* Instance dummyisCTmp : Dummy isCTmp := isC_vp (consp nilp (starp nilp)) dummy dummy dummy dummy dummy. *)
Instance dummyisCTmp : Dummy isCTmp := isC_dumt.
Fixpoint subisCVarp (E : Conp)(Ec : isContrp)(σ : Subp) (σc: isCSubp)(xc : isCVarp) : isCTmp :=
  match xc with 
  | isC_vstarp => if σc is isC_to_astarp Γ Γc t tc then tc else dummy
  | isC_v0p Γ Γc A Ac u uc =>
    if σc is isC_to_consconsp Γ Γc Δ Δc A Ac u uc δ δc t tc f fc then
      fc
    else
      dummy
  | isC_v1p Γ Γc A Ac u uc => 
    if σc is isC_to_consconsp Γ Γc Δ Δc A Ac u uc δ δc t tc f fc then
      tc
    else
      dummy
  | isC_vSSp Γ Γc A Ac u uc B Bc x xc  =>
    if σc is isC_to_consconsp Γ Γc Δ Δc A Ac u uc δ δc t tc f fc then
      subisCVarp E Ec δ δc xc
    else
      dummy
  end.
Fixpoint subisCTmp (E : Conp)(Ec : isContrp)(σ : Subp)(σc: isCSubp) (tc : isCTmp) : isCTmp :=
  match tc with
    isC_vp Γ Γc A Ac x xc => subisCVarp E Ec σ σc xc
  | isC_cohp Γ Γc Δ Δc A Ac δ δc =>
    isC_cohp E Ec Δ Δc A Ac (subSubp E σ δ) (subisCSubp E Ec σ σc δc)
  | isC_dumt => isC_dumt
  end
with subisCSubp (E : Conp) (Ec : isContrp) (σ : Subp)(σc: isCSubp) (δc: isCSubp) : isCSubp :=
       match δc with
         isC_to_astarp Γ Γc t tc => 
         isC_to_astarp E Ec (subTmp E σ t) (subisCTmp E Ec σ σc tc)
       | isC_to_consconsp Γ Γc Δ Δc A Ac u uc δ δc t tc f fc =>
         isC_to_consconsp E Ec Δ Δc A Ac u uc (subSubp E σ δ) (subisCSubp E Ec σ σc δc)
                          (subTmp E σ t)(subisCTmp E Ec σ σc tc)
                          (subTmp E σ f)(subisCTmp E Ec σ σc fc)
       end.
      
Fixpoint subisCTyp (E : Conp)(Ec : isContrp)(σ : Subp) (σc: isCSubp) (Ac : isCTyp) : isCTyp :=
  match Ac with
    isC_starp Γ Γc => isC_starp E Ec
  | isC_arp Γ Γc A Ac t tc u uc =>
    isC_arp E Ec (subTyp E σ A) (subisCTyp E Ec σ σc  Ac)
            (subTmp E σ t) (subisCTmp E Ec σ σc tc)
            (subTmp E σ u) (subisCTmp E Ec σ σc uc)
  end.


Fixpoint Conw (Γ : Conp) {struct Γ} : Type :=
       match Γ with
         nilp => True
       | Γ ▷ A => Conw Γ * Tyw Γ A
       end
with Tyw (G : Conp) (A : Typ) {struct A} : Type :=
  match A with
    starp Γ => ((Conw Γ) * (G = Γ))%type
  | arp Γ A t u => (Conw Γ * Tyw Γ A * Tmw Γ A t * Tmw Γ A u * (G = Γ))%type
  end
with  Tmw (G : Conp) (T : Typ) (t : Tmp) {struct t} := 
        match t with
          vp Γ A x => (Conw Γ * Tyw Γ A * (Varw Γ A x) * (G = Γ) * (T = A))%type
        | coh Γ Δ Δc A Ac σ =>
          (Conw Γ * Conw Δ * Tyw Δ A * Subw Γ Δ σ *
           isContrw Δ Δc * isCTyw Δ Δc A Ac *
           (G = Γ) * (T = subTyp Γ σ A))%type
        | dumt => False
        end 
with Varw (G : Conp) (T : Typ) (x : Varp) {struct x} := 
       match x with
         v0 Γ A => ( Conw Γ * Tyw Γ A * (G = Γ ▷ A) * (T = wkTyp A A))%type
       | vS Γ A x B => ( Conw Γ * Tyw Γ A * Varw Γ A x * Tyw Γ B * (G = Γ ▷ B) * (T = wkTyp B A))%type
       end
with Subw (G : Conp) (H : Conp) (σ : Subp) {struct σ} := 
       match σ with
         to_nilp Γ => (Conw Γ * (G = Γ) * (H = ∙))%type
       | to_consp Γ Δ σ A t =>
         (Conw Γ * Conw Δ * (Subw Γ Δ σ) * Tyw Δ A * Tmw Γ (subTyp Γ σ A) t * (G = Γ) * (H = Δ ▷ A) )%type
       end
with isContrw (G : Conp) (Γc : isContrp) {struct Γc} : Type :=
  match Γc with
  | isC_astarp => G = nilp ▷ (starp nilp) 
  | isC_consconsp Γ Γc A Ac u uc =>
    ((Conw Γ) * (Tyw Γ A) * (Tmw Γ A u ) *
    isContrw Γ Γc *
    isCTyw Γ Γc A Ac *
    isCTmw Γ Γc A Ac u uc *
    (G = (Γ ▷ A) ▷ (arp (Γ ▷ A) (wkTyp A A) (vp (Γ ▷ A) (wkTyp A A) (v0 Γ A)) (wkTmp A u)) ))%type
  end
with isCTyw (G : Conp) (Gc : isContrp) (T : Typ) (Tc : isCTyp) {struct Tc} : Type :=
  match Tc with
    isC_starp Γ Γc => (Conw Γ * isContrw Γ Γc * (G = Γ) * (Gc = Γc) * (T = starp Γ))%type
  | isC_arp Γ Γc A Ac t tc u uc =>
    (Conw Γ * Tyw Γ A * Tmw Γ A t * Tmw Γ A u *
     isContrw Γ Γc * isCTyw Γ Γc A Ac * isCTmw Γ Γc A Ac t tc * isCTmw Γ Γc A Ac u uc *
     (G = Γ) * (Gc = Γc) *
     (T = arp Γ A t u)
    )%type
  end
with  isCTmw (G : Conp)(Gc : isContrp) (T : Typ) (Tc : isCTyp) (t : Tmp) (tc : isCTmp) {struct tc} := 
        match tc with
          isC_vp Γ Γc A Ac x xc =>
          (Conw Γ * Tyw Γ A * (Varw Γ A x) *
           isContrw Γ Γc *
           isCTyw Γ Γc A Ac *
           isCVarw Γ Γc A Ac x xc *
           (G = Γ) * (Gc = Γc) * (T = A) * (Tc = Ac) * (t = vp Γ A x))%type
        | isC_cohp Γ Γc Δ Δc A Ac σ σc =>
          (Conw Γ * Conw Δ * Tyw Δ A * Subw Γ Δ σ *
           isContrw Δ Δc *
           isContrw Γ Γc *
           isCTyw Δ Δc A Ac *
           isCSubw Γ Γc Δ Δc σ σc *
           (G = Γ) * (Gc = Γc) * (T = subTyp Γ σ A) * (Tc = subisCTyp Γ Γc σ σc Ac) * (t = coh Γ Δ Δc A Ac σ)
          )%type
        | isC_dumt => False
        end 
with isCVarw (G : Conp) (Gc : isContrp) (T : Typ)(Tc : isCTyp)  (y : Varp) (yc : isCVarp ) {struct yc}   := 
       match yc with
       | isC_vstarp =>
         (
           (G = (consp nilp (starp nilp))) *
           (Gc = isC_astarp) *
           (T = starp (consp nilp (starp nilp))) *
           (Tc = isC_starp (consp nilp (starp nilp)) isC_astarp) *
           (y = v0 nilp (starp nilp))
         )%type
       | isC_v0p Γ Γc A Ac u uc =>
         ((Conw Γ) * (Tyw Γ A) * (Tmw Γ A u ) *
          isContrw Γ Γc *
          isCTyw Γ Γc A Ac *
          isCTmw Γ Γc A Ac u uc *
          (G = consconsp Γ A u) *
          (Gc = isC_consconsp Γ Γc A Ac u uc) *
          (T = wkTyp (arcons Γ A u) (arcons Γ A u)) *
          (* I use G and Gc instead of their real values because it is shorter *)
          (Tc = isC_arp G Gc
                        (wkwkTyp Γ A u A)
                        (wkisCTyp A Ac u uc Ac)
                        (vp G (wkwkTyp Γ A u A) (vS (Γ ▷ A) (wkTyp A A) (v0 Γ A ) (arcons Γ A u)))
                        (isC_vp G Gc A Ac
                                (vS (Γ ▷ A) (wkTyp A A) (v0 Γ A ) (arcons Γ A u))
                                (isC_v1p Γ Γc A Ac u uc))
                        (wkwkTmp Γ A u u)
                        (wkisCTmp A Ac u uc uc)
                         ) *
            (* TODO wkisCTyp *)
          (y = v0 (Γ ▷ A) (arcons Γ A u))
         )%type
       | isC_v1p Γ Γc A Ac u uc =>
         ((Conw Γ) * (Tyw Γ A) * (Tmw Γ A u ) *
          isContrw Γ Γc *
          isCTyw Γ Γc A Ac *
          isCTmw Γ Γc A Ac u uc *
          (G = consconsp Γ A u) *
          (Gc = isC_consconsp Γ Γc A Ac u uc) *
          (T = wkwkTyp Γ A u A ) *
          (Tc = wkisCTyp A Ac u uc Ac) *
          (y = vS (Γ ▷ A) (wkTyp A A) (v0 Γ A) (arcons Γ A u))
         )%type
       | isC_vSSp Γ Γc A Ac u uc B Bc x xc  =>
         ((Conw Γ) * (Tyw Γ A) * (Tmw Γ A u ) * (Tyw Γ B) * (Varw Γ B x) *
          isContrw Γ Γc *
          isCTyw Γ Γc A Ac *
          isCTmw Γ Γc A Ac u uc *
          isCTyw Γ Γc B Bc *
          isCVarw Γ Γc B Bc x xc *
          (G = consconsp Γ A u) *
          (Gc = isC_consconsp Γ Γc A Ac u uc) *
          (T = wkwkTyp Γ A u B) *
          (Tc = wkisCTyp A Ac u uc Bc) *
          (y = vS (Γ ▷ A) (wkTyp A A) (vS Γ B x A)
                  (arcons Γ A u))
         )%type
       end
with isCSubw (G : Conp) (Gc: isContrp) (H : Conp)(Hc : isContrp) (s : Subp) (sc : isCSubp) {struct sc} := 
       match sc with
         isC_to_astarp Γ Γc t tc => 
         (
           Conw Γ *
           isContrw Γ Γc *
           Tmw Γ (starp Γ) t *
           isCTmw Γ Γc (starp Γ) (isC_starp Γ Γc) t tc *
           (G = Γ) * (Gc = Γc) *
           (H = consp nilp (starp nilp)) * (Hc = isC_astarp) *
           (s = to_consp Γ nilp (to_nilp Γ) (starp nilp) t)
         )%type
       | isC_to_consconsp Γ Γc Δ Δc A Ac u uc σ σc t tc f fc =>
         let Aσ := subTyp Γ σ A in
         let Aσc := subisCTyp Γ Γc σ σc Ac in
         let uσ := subTmp Γ σ u in
         let uσc := subisCTmp Γ Γc σ σc uc in
         (Conw Γ * (Conw Δ) * (Tyw Δ A) * (Tmw Δ A u ) *
           (Tmw Γ (subTyp Γ σ A) t) * (Tmw Γ (arp Γ (subTyp Γ σ A) t (subTmp Γ σ u)) f) *
           (Subw Γ Δ σ) *
          isContrw Γ Γc *
          isContrw Δ Δc *
          isCTyw Δ Δc A Ac *
          isCTmw Δ Δc A Ac u uc *
          isCTmw Γ Γc Aσ Aσc t tc *
          isCTmw Γ Γc (arp Γ Aσ t uσ)
                 (isC_arp Γ Γc Aσ Aσc t tc uσ uσc )
                 f fc *
          isCSubw Γ Γc Δ Δc σ σc  *
          (G = Γ) * (Gc = Γc) *
          (H = consconsp Δ A u)*
          (Hc = isC_consconsp Δ Δc A Ac u uc) *
          (s = to_consp Γ (Δ ▷ A)
                        (to_consp Γ Δ σ A t)
                        (arcons Δ A u)
                        f
         ))%type
       end.


Fixpoint wkTyw (G : Conp) (Ex : Typ) (Ew : Tyw G Ex) (A : Typ) (Aw : Tyw G A) {struct A} : Tyw (G ▷ Ex) (wkTyp Ex A)
  with wkTmw (G : Conp) (Ex : Typ) (Ew : Tyw G Ex) (T : Typ) (t : Tmp )(tw : Tmw G T t) {struct t} :
          Tmw (G ▷ Ex) (wkTyp Ex T) (wkTmp Ex t)
  with wkSubw (G H : Conp) (Ex : Typ) (Ew : Tyw G Ex) (σ : Subp) (σw : Subw G H σ) {struct σ} :
          Subw (G ▷ Ex) H (wkSubp Ex σ).
Proof.
  - move:Aw.
    refine (
        match A with
          starp Γ => _
        | arp Γ A t u => _
        end); cbn => Aw; destruct_eqs Aw; repeat split; try get_from_hyp Aw || easy.
    * by apply wkTyw; assumption|| get_from_hyp Aw.
    * by apply:wkTmw ; assumption || get_from_hyp Aw.
    * by apply:wkTmw ; assumption || get_from_hyp Aw.
  - move:tw.
    refine (
        match t with
          vp Γ A x => _
        | coh Γ Δ Δc A Ac σ =>  _
        | dumt => fun x => Empty_rect _
                   end); last by exact x. 
    all: cbn => tw; (repeat destruct_eqs tw); repeat split; try get_from_hyp tw || easy.
    * apply wkTyw; assumption|| get_from_hyp tw.
    * apply wkSubw; assumption|| get_from_hyp tw.
    * apply wk_subTyp.
  - move:σw.
    refine (match σ with
         to_nilp Γ => _
       | to_consp Γ Δ σ A t => _
       end); cbn => σw; (repeat destruct_eqs σw); repeat split; try get_from_hyp σw || easy.
    * by apply:wkSubw; assumption || get_from_hyp σw.
    * apply:(transport (fun x => Tmw (Γ ▷ Ex) x _)); first by apply:wk_subTyp.
      apply:wkTmw; assumption || get_from_hyp σw.
Defined.

Definition Ty_Con_w (Γ : Conp) (A : Typ) (Aw : Tyw Γ A ) : Conw Γ.
  move:Aw.
  destruct A ; simpl => Aw;  apply:(transport Conw (_^)); get_from_hyp  Aw.
Defined.

Definition Tm_Con_w (Γ : Conp) (A : Typ) t (tw : Tmw Γ A t) : Conw Γ.
  - move:tw.
    destruct t ; simpl => tw; (by apply:Empty_rect) || apply:(transport Conw (_^)) ; get_from_hyp  tw .
Defined.

Definition Var_Con_w (Γ : Conp) (A : Typ) x (xw : Varw Γ A x ) : Conw Γ.
   move:xw.
   destruct x ; simpl => xw;  apply:(transport Conw (_^)); try get_from_hyp xw;
                          simpl; split; get_from_hyp xw.
Defined.
Definition Sub_Con_w (Γ Δ : Conp) (σ : Subp)  (σw : Subw Γ Δ σ ) : Conw Γ.
   move:σw.
   destruct σ ; simpl => σw;  apply:(transport Conw (_^)); try get_from_hyp σw.
Defined.


Definition Var_Ty_w (Γ : Conp) (A : Typ) x (xw : Varw Γ A x ) : Tyw Γ A.
   move:xw.
   destruct x ; simpl => xw.
   + repeat destruct_eqs xw.
     apply :wkTyw; get_from_hyp xw.
   + repeat destruct_eqs xw.
     apply :wkTyw; get_from_hyp xw.
Defined.

Definition
  wkVarw (G : Conp) (Ex : Typ) (Ew : Tyw G Ex) (T : Typ) (x : Varp )(xw : Varw G T x)  :
          Varw (G ▷ Ex) (wkTyp Ex T) (vS G T x Ex).
  repeat split => //.
  by apply :Var_Con_w; eassumption.
    by apply :Var_Ty_w; eassumption.
Defined.


(* Used to define subTyr *)
Fixpoint subTyw (G H : Conp) (Gw : Conw G) (σ : Subp) (σw : Subw G H σ) (A : Typ) (Aw : Tyw H A) {struct A} :
   Tyw G (subTyp G σ A)
  with subTmw (G H : Conp) (Gw : Conw G)(σ : Subp) (σw : Subw G H σ) (T : Typ) (t : Tmp )(tw : Tmw H T t) {struct t} :
          Tmw G (subTyp G σ T) (subTmp G σ t)
  with subVarw (G H : Conp)(Gw : Conw G) (σ : Subp) (σw : Subw G H σ) (T : Typ) (x : Varp )(xw : Varw H T x) {struct x} :
         Tmw G (subTyp G σ T) (subVarp G σ x)
  with subSubw (G H : Conp) (Gw : Conw G)(σ : Subp) (σw : Subw G H σ) (E : Conp) (δ : Subp) (δw : Subw H E δ) {struct δ} :
          Subw G E (subSubp G σ δ) .
Proof.
  - move:Aw.
    refine (
        match A with
          starp Γ => _
        | arp Γ A t u => _
        end); cbn => Aw.
    + easy.
    + destruct_eqs Aw.
      repeat split ;  try (get_from_hyp Aw ||  easy).
      * by apply:(subTyw _ _ Gw _ σw); get_from_hyp Aw.
      * by apply:(subTmw _ _ Gw _ σw); get_from_hyp Aw.
      * by apply:(subTmw _ _ Gw _ σw); get_from_hyp Aw.
  - move:tw.
    refine (
        match t with
          vp Γ A x => _
        | coh Γ Δ Δc A Ac δ =>  _
        | dumt => fun tw => Empty_rect _
                   end); cbn; last by exact.
    all: move => /= tw; repeat destruct_eqs tw.
    + (apply:subVarw;  try (get_from_hyp tw)) => //. 
    + repeat split ;  try (get_from_hyp tw ||  easy).

      * by apply :(subSubw _ _ Gw _ σw _ _ _); get_from_hyp tw.
      * apply:subsubTyp.
  - move:σw xw.
    refine ( match x with
         v0 Γ A => if σ is to_consp E' Δ σ' A' t then _ else _
       | vS Γ A x B => if σ is to_consp E' Δ σ' A' t then _ else _
             end); cbn.
    + intros σw xw.
      move:(snd σw).
      (* repeat (destruct_eqs σw). *)
      move:(snd (fst xw)).
      congruence.
    + move => σw xw.
       repeat destruct_eqs σw.
       have eA : Δ ▷ A' = Γ ▷ A by get_from_hyp xw.
       case:eA => ??; subst.
       (* { *)
       (*   have  *)
       (*     congruence. *)
       (* repeat destruct_eqs xw. *)
      apply :(transport( fun x => Tmw E' x _)); last by get_from_hyp σw.
       repeat destruct_eqs xw.
      apply: sub_cons_wkTyp.
    + move => σw xw.
       repeat destruct_eqs σw.
       have : (∙ = Γ ▷ B) by get_from_hyp xw.
      discriminate.
    + move => σw xw.
       repeat destruct_eqs σw.
       have eA : Δ ▷ A' = Γ ▷ B by get_from_hyp xw.
       case:eA => ??; subst.
       repeat destruct_eqs xw.
      apply :(transport( fun x => Tmw E' x _)); first by apply sub_cons_wkTyp.
      apply :subVarw; get_from_hyp σw || get_from_hyp xw.

  - move:δw.
    refine (match δ with
         to_nilp Γ => _
       | to_consp Γ Δ δ A t => _
       end); cbn.
    + case => _ ?.
      by split.
    + move => σr.
      repeat destruct_eqs σr.
      (* (repeat case) => Γw Δw δw Aw tw eG eH. *)
      repeat split => //; try get_from_hyp σr. 
      * apply:subSubw.
        -- eassumption.
        -- eassumption.
        -- get_from_hyp σr.
      * apply:(transport ( fun x => Tmw G x _)) ; first by eapply subsubTyp.
        apply: (subTmw _ _ _ _ _ _ _ ).
        -- assumption.
        -- eassumption.
        -- get_from_hyp σr.
Defined.


Require Import Coq.Program.Tactics.

Class Model :=
  {
    Conm : Type ;
    Tym : forall (Γ : Conm) , Type;
    Tmm : forall (Γ : Conm) (A : Tym Γ), Type ;
    Varm : forall (Γ : Conm) (A : Tym Γ), Type ;
    Subm : forall (Γ Δ : Conm) , Type ;

    isContrm : forall (Γ : Conm) , Type ;

    isCTym : forall (Γ : Conm) (Γc : isContrm Γ) (A : Tym Γ) , Type;
    isCTmm : forall (Γ : Conm) (Γc : isContrm Γ) (A : Tym Γ)(Ac : isCTym Γc A)(t : Tmm A) , Type;
    isCVarm : forall (Γ : Conm) (Γc : isContrm Γ) (A : Tym Γ)(Ac : isCTym Γc A)(x : Varm A) , Type;
    isCSubm : forall (Γ Δ : Conm) (Γc : isContrm Γ)(Δc : isContrm Δ)(σ : Subm Γ Δ) , Type;

    (**  substitutions *)

    subTym : forall (Γ Δ : Conm)(σ : Subm Γ Δ)(A : Tym Δ), Tym Γ ;
    subTmm : forall (Γ Δ : Conm)(σ : Subm Γ Δ)(A : Tym Δ)(t : Tmm A), Tmm (subTym σ A) ;
    (* subVarm : forall (Γ Δ : Conm)(σ : Subm Γ Δ)(A : Tym Δ)(x : Varm A), Tmm (subTym σ A) ; *)
    subSubm :forall (Γ Δ : Conm)(σ : Subm Γ Δ)(Y : Conm) (δ : Subm Δ Y) , Subm Γ Y ; 


    (* context *)
    nilm : Conm;
    consm : forall (Γ : Conm) (A : Tym Γ), Conm;

    (* weakening *)
    wkTym : forall Γ (Ex A : Tym Γ), Tym (consm Ex) ;
    wkTmm : forall Γ (Ex A : Tym Γ) (t : Tmm A), Tmm (wkTym Ex A) ;
    wkSubm : forall Γ (Ex  : Tym Γ) Δ (σ : Subm Γ Δ) , Subm (consm Ex) Δ ;

    (* types *)
    starm : forall Γ, Tym Γ;
    arm : forall Γ (A : Tym Γ) (t u : Tmm A), Tym Γ ;


    (* terms *)
    vam : forall Γ (A : Tym Γ) (x : Varm A), Tmm A ;
    (* cohm : forall Γ Δ (Δc : isContrm Δ) (σ : Subm Γ Δ) (A : Tym Δ)(Ac : isCTym Δc A) , Tmm (subTym σ A) ; *)
    (* no need for having the substitution embedded with cohm *)
    cohm : forall Δ (Δc : isContrm Δ)  (A : Tym Δ)(Ac : isCTym Δc A) , Tmm A ;

    (* variables *)
    v0m : forall Γ (A : Tym Γ), Varm (wkTym A A) ;
    vSm : forall Γ (A : Tym Γ)(x : Varm A)(Ex : Tym Γ), Varm (wkTym Ex A) ;

    (* substitutions *)
    to_nilm : forall Γ, Subm Γ nilm ;
    to_consm : forall Γ Δ (σ : Subm Γ Δ) (A : Tym Δ) (t : Tmm (subTym σ A)), Subm Γ (consm A);


    (** equalities for weakening *)
    (** computation rules about weakening *)

    (* types *)
    wk_starm : forall Γ (A : Tym Γ), wkTym A (starm Γ) = starm (consm  A);
    wk_arm : forall Γ (Ex A : Tym Γ) (t u : Tmm A),  wkTym Ex (arm t u) = arm (wkTmm Ex t) (wkTmm Ex u) ;

    (* terms *)
    wk_vam : forall Γ (Ex : Tym Γ)(A : Tym Γ)(x : Varm A), wkTmm Ex (vam x) = vam (vSm x Ex );

    wk_subTym : forall Γ (Ex : Tym Γ)(Δ: Conm) (σ : Subm Γ Δ)(A : Tym Δ),
        wkTym Ex (subTym σ A) = subTym (wkSubm Ex σ) A ;
    wk_subTmm : forall Γ (Ex : Tym Γ)(Δ: Conm) (σ : Subm Γ Δ)(A : Tym Δ)(t : Tmm A),
        wkTmm Ex (subTmm σ t) = (wk_subTym Ex σ A) ^ # (subTmm (wkSubm Ex σ) t );

    (* One should ask for unicity of to_nilm instead of just stability by weakening
     *)
    wk_tonilm : forall Γ (Ex : Tym Γ) , wkSubm Ex (to_nilm Γ) = to_nilm _; 
    wk_to_consm : forall Γ (Ex : Tym Γ) Δ (σ : Subm Γ Δ)  (A : Tym Δ) (t : Tmm (subTym σ A)),
        wkSubm Ex (to_consm t) = to_consm (σ := wkSubm Ex σ)
                                          (transport (Tmm (Γ :=consm  Ex)) (wk_subTym Ex σ A) (wkTmm Ex t) );




    (** Equalities about substitution *)
  (* subTmm (to_consm t) (wkTmm T z) = ?Goal0 *)
    sub_cons_wkTym : forall Γ Δ (σ : Subm Γ Δ) (Ex : Tym Δ )(t : Tmm (subTym σ Ex)) 
                        (A : Tym Δ) , subTym (to_consm t) (wkTym Ex A) =  subTym σ A ;

    sub_cons_wkTmm : forall Γ Δ (σ : Subm Γ Δ) (Ex : Tym Δ )(t : Tmm (subTym σ Ex))
                       (A : Tym Δ) (z : Tmm A), subTmm (to_consm t) (wkTmm Ex z) =
                                                transportb (sub_cons_wkTym t A) (subTmm σ z) ;

    subsubTym : forall Γ Δ Y (σ : Subm Γ Δ)(δ : Subm Δ Y) (A : Tym Y),
        subTym σ (subTym δ A) = subTym (subSubm σ δ) A ;

    subsubTmm : forall Γ Δ Y (σ : Subm Γ Δ)(δ : Subm Δ Y) (A : Tym Y) (t : Tmm A),
        subTmm σ (subTmm δ t) = (subsubTym σ δ A)^ # subTmm (subSubm σ δ) t ;

  (*     ((σm.1; subTym (σm.2).2 (subTym p1 p8)); subTmm (σm.2).2 (subTmm p1 (cohm p4))) = *)
  (* ((σm.1; subTym (subSubm (σm.2).2 p1) p8); subTmm (subSubm (σm.2).2 p1) (cohm p4)) *)

    (* computation rules about substitutions *)
    (** Preservation by substitution *)
    sub_starm : forall Γ Δ (σ : Subm Γ Δ), subTym σ (starm _) = starm _ ;
    sub_arm : forall Γ Δ (σ : Subm Γ Δ)(A : Tym Δ)(t u : Tmm A), subTym σ (arm t u) =
                                                          arm (subTmm σ t)(subTmm σ u);

    sub_cons_v0m : forall Γ Δ (σ : Subm Γ Δ) (Ex : Tym Δ )(t : Tmm (subTym σ Ex)),
        (subTmm (to_consm t) (vam (v0m Ex))) = transportb (sub_cons_wkTym t Ex) t ;

    sub_cons_vSm : forall Γ Δ (σ : Subm Γ Δ) (Ex : Tym Δ )(t : Tmm (subTym σ Ex))
                     (A : Tym Δ)(x : Varm A),
        (subTmm (to_consm t) (vam (vSm x Ex))) = transportb (sub_cons_wkTym t A) (subTmm σ (vam x)) ;

    sub_to_consm : forall Γ Δ (σ : Subm Γ Δ) Y (δ : Subm Δ Y) (A : Tym Y) (t : Tmm (subTym δ A)),
                     subSubm σ (to_consm t) = to_consm (transport (Tmm (Γ:=Γ)) (subsubTym σ δ A) (subTmm σ t)) ;

    (* One should ask for unicity of to_nilm instead of just stability by substitution
     *)
    sub_tonilm : forall Γ Δ (σ : Subm Γ Δ), subSubm σ (to_nilm Δ) = to_nilm Γ; 

    (* contractible *)
    isC_astarm :  isContrm (consm (starm nilm));
    isC_consconsm : forall (Γ : Conm) Γc (T : Tym Γ) (Tc : isCTym Γc T)
                         (z : Tmm T) (zc : isCTmm Tc z),
        isContrm (consm (Γ := (consm T))
                        (arm (vam (v0m T)) (wkTmm _ z)));

    (* TYpes in contractible contexts *)
    isC_starm : forall (Γ : Conm) (Γc : isContrm Γ), isCTym Γc (starm Γ);
    isC_arm : forall (Γ : Conm) (Γc : isContrm Γ)(A : Tym Γ) (Ac : isCTym Γc A)
               (t : Tmm A)(tc : isCTmm Ac t)
               (u : Tmm A)(uc : isCTmm Ac u),
        isCTym Γc (arm t u);

    (* weakening in contractible contexts *)

    isCwkwkTym :  forall (Γ : Conm) Γc (T : Tym Γ) (Tc : isCTym Γc T)
                    (z : Tmm T) (zc : isCTmm Tc z)(A : Tym Γ) (Ac : isCTym Γc A),
        isCTym (isC_consconsm zc) (wkTym _ (wkTym _ A)) ;


    isCwkwkTmm :  forall (Γ : Conm) Γc (T : Tym Γ) (Tc : isCTym Γc T)
                    (z : Tmm T) (zc : isCTmm Tc z)(A : Tym Γ) (Ac : isCTym Γc A)
                     (t : Tmm A) (tc : isCTmm Ac t),
        isCTmm (isCwkwkTym zc Ac) (wkTmm _ (wkTmm _ t)) ;

    (* Substitution in constractible contexts *)
    subisCTym : forall (Γ Δ : Conm) (Γc : isContrm Γ)(Δc : isContrm Δ)(σ : Subm Γ Δ) (σc : isCSubm Γc Δc σ)
                 (A : Tym Δ) (Ac : isCTym Δc A), isCTym Γc (subTym σ A) ;
    subisCTmm : forall (Γ Δ : Conm) (Γc : isContrm Γ)(Δc : isContrm Δ)(σ : Subm Γ Δ) (σc : isCSubm Γc Δc σ)
                  (A : Tym Δ) (Ac : isCTym Δc A)
                  (t : Tmm A) (tc : isCTmm Ac t) , isCTmm (subisCTym σc Ac) (subTmm σ t) ;
 

    (* terms in contractible contexts *)

    isC_vm : forall (Γ : Conm)(Γc : isContrm Γ)(A : Tym Γ) (Ac : isCTym Γc A)(x : Varm A)(xc : isCVarm Ac x),
        isCTmm Ac (vam x) ;

    isC_cohm : forall (Δ : Conm) (Δc : isContrm Δ) (A : Tym Δ)
               (Ac : isCTym Δc A), isCTmm Ac (cohm Ac) ;



    (* variables in contractible contexts *)
    isC_vstarm : isCVarm (isC_starm isC_astarm)
                        (transport ( Varm (Γ := (consm (starm nilm)))) (wk_starm (starm nilm)) (v0m _)) ;
    isC_v1m : forall (Γ : Conm) Γc (T : Tym Γ) (Tc : isCTym Γc T)
               (z : Tmm T) (zc : isCTmm Tc z),
        isCVarm (isCwkwkTym zc Tc) (vSm (v0m _) _) ;

    isC_v0m :  forall (Γ : Conm) Γc (T : Tym Γ) (Tc : isCTym Γc T)
               (z : Tmm T) (zc : isCTmm Tc z),
        isCVarm (isC_arm (isC_vm (isC_v1m zc)) (isCwkwkTmm zc zc))
                (transport ( Varm (Γ := (consm (Γ := (consm  T)) (arm (A := (wkTym  T T)) (vam   (v0m  T)) 
                                                                          (wkTmm  T z))))  )
                           ((wk_arm _ _ _ ) @ (ap (fun x => arm x _) (wk_vam _ _) ) )
                           (v0m _)) ;
    isC_vSSm : forall (Γ : Conm) Γc (T : Tym Γ) (Tc : isCTym Γc T)
               (z : Tmm T) (zc : isCTmm Tc z)(A : Tym Γ) (Ac : isCTym Γc A) (x : Varm A)(xc : isCVarm Ac x),
        isCVarm (isCwkwkTym zc Ac) (vSm (vSm x _) _) ;

    (* substitutions between contractible contexts *)
    isC_to_astarm : forall (Γ : Conm) Γc  (t : Tmm (starm Γ)) (tc : isCTmm (isC_starm Γc) t) ,
        isCSubm Γc isC_astarm  (to_consm (σ := (to_nilm _))
                                       (transportb (sub_starm _) t)
                              ) ;

    isC_to_consconsm :
      forall (Γ : Conm) Γc
                       (Δ : Conm) Δc
                       (σ : Subm Γ Δ) (σc : isCSubm Γc Δc σ)
                       (T : Tym Δ) (Tc : isCTym Δc T)
                       (z : Tmm T) (zc : isCTmm Tc z)
                       (t : Tmm (subTym σ T)) (tc : isCTmm (subisCTym σc Tc) t) 
                       (f : Tmm (arm t (subTmm σ z) ))
                       (fc : isCTmm (isC_arm tc (subisCTmm σc zc))  f) , 
        isCSubm Γc (isC_consconsm zc)
                (to_consm (σ := (to_consm t))
                          (transportb
                             (sub_arm (to_consm t) (vam (v0m T)) (wkTmm T z)
                                      @ (ap2 (arm (A:=subTym (to_consm t) (wkTym T T))) (sub_cons_v0m t) (sub_cons_wkTmm t z)
                                             @ J (fun y e => arm (A := y) (transportb e t) (transportb e (subTmm σ z)) = arm t (subTmm σ z))(sub_cons_wkTym t T) eq_refl))
                             f))
      











    }.


Lemma transportb_dep2 (A : Type) (x : A) (P P' : A -> Type) (y : A) (e : x = y) (Py : P y)(Py' : P' y) Z1
      Z2
      (e'1 : Z1 = transportb e Py)
      (e'2 : Z2 = transportb e Py')
      (Q : forall c, P c -> P' c -> Type) (q : Q _ Py Py'): Q _ Z1 Z2.
Proof.
  destruct e.
  cbn in e'1,e'2.
  destruct e'1,e'2.
  apply:q.
Defined.

(*
Definition transportb_dep_var :
  (A : Type) (x : A) (P P' : A -> Type) (y : A) (e : x = y) (Py : P y)(Py' : P' y) Z1
             Z2
             (e'1 : Z1 = transportb e Py)
             (e'2 : Z2 = transportb e Py')
             (Q : forall c, P c -> P' c -> Type) (q : Q _ Py Py')
             (Q2 : forall c, P c -> Type) (q2 : Q _ Py)
             q2'
             (eq2 : q2' = transportb_dep e'1 q2)
             (eTc : q = transportb_dep2 e'2 e'1 (transportb eq3 z))
  : Q _ Z1 Z2.
  eG : Gm = consm (starm nilm)
  eT : Tm = transportb eG (wkTym (starm nilm) (starm nilm))
  eGc : Gc = transportb eG isC_astarm
  eq : qm = transportb_dep eT (v0m (starm nilm))
  eTc : Tc = transportb_dep2 eGc eT (transportb (wk_starm (starm nilm)) (isC_starm isC_astarm))
  ============================
  isCVarm (isC_starm isC_astarm) (transport (wk_starm (starm nilm)) (v0m (starm nilm))) -> isCVarm Tc qm
*)

Section rec.
Context (m : Model).


(* Definition J  (A : Type) (x : A) (P : A -> Type) : P x -> forall y : A, x = y -> P y := *)
(*   eq_rect x P. *)
Definition transport_dep (A : Type) (x : A) (P : A -> Type) (y : A) (e : x = y) (Px : P x)  
      (Q : forall c, P c -> Type) (q : Q _ Px): Q _ (e # Px).
  by destruct e.
Defined.

  (* Axiom myadmit : forall A, A. *)
  (* Declare Implicit Tactic (apply myadmit). *)
(* Primitive projections make isC* definitions fast *)
Fixpoint Con_r (Γp : Conp ) (Γw : Conw Γp) (Gm : Conm) {struct Γp} : Type 
with Ty_r (Γp : Conp)(Ap : Typ) (Aw : Tyw Γp Ap) (GTm : Σ Gm, Tym Gm) {struct Ap} : Type
with Tm_r  (Γp : Conp)(Ap : Typ)(tp : Tmp) (tw : Tmw Γp Ap tp) (GTpm : Σ GTm, Tmm GTm.2) {struct tp} : Type
with Var_r  (Γp : Conp)(Ap : Typ)(xp : Varp) (xw : Varw Γp Ap xp) (GTpm : Σ GTm, Varm GTm.2) {struct xp} : Type
with Sub_r  (Γp Δp : Conp)(σp : Subp) (σw : Subw Γp Δp σp) (GHsm : Σ (Gm Hm : Conm), Subm Gm Hm) {struct σp} : Type
with isContr_r (Γp : Conp) (Γc : isContrp) (Γcw : isContrw Γp Γc)
               (Gmc : Σ Gm, isContrm Gm)
                  {struct Γc} : Type
with isCTy_r (Γp : Conp) Γc 
             (Ap : Typ) Ac (Aw : isCTyw Γp Γc Ap Ac)
             (Gmc : Σ Gmc Tm, isCTym Gmc.2 Tm)
             {struct Ac} : Type
with isCTm_r (Γp : Conp) Γc  
              (Ap : Typ) Ac (tp : Tmp) tc (tcw : isCTmw Γp Γc Ap Ac tp tc)
              (GTpmc : Σ (GTmc : Σ Gmc Tm, isCTym Gmc.2 Tm) pm, isCTmm GTmc.2.2 pm)
               {struct tc} : Type
with isCVar_r (Γp : Conp)  Γc  
               (Ap : Typ) Ac (xp : Varp) xc (xcw : isCVarw Γp Γc Ap Ac  xp xc)
               (GTqmc : Σ (GTmc : Σ Gmc Tm, isCTym Gmc.2 Tm) qm, isCVarm GTmc.2.2 qm)
               {struct xc} : Type
with isCSub_r  (Γp : Conp) Γc
               (Δp : Conp) Δc
               (σp : Subp ) σc
               (σcw : isCSubw Γp Γc Δp Δc σp σc)
               (GHsmc : Σ Gmc Hmc sm , isCSubm Gmc.2 Hmc.2 sm)
               {struct σc} : Type.
(* with Sub_r  (Γp Δp : Conp)(σp : Subp) (σw : Subw Γp Δp σp) (Gm Hm : Conm)(sm : Subm Gm Hm) {struct σp} : Type. *)
- move:Γw.
  unshelve refine (match Γp with
            nilp => fun _ => Gm = nilm
          | consp Γp Ap => fun Gw =>
                            (Σ (ΓArm : Σ ΓAm, (Ty_r Γp Ap _ ΓAm))
                               (* paranoid stuff *)
                               (Γmr : Σ Γm , Con_r Γp _ Γm)
                               (eΓ : ΓArm.1.1 = Γmr.1)
                             ,
                             
                            (Gm = consm (ΓArm.1.2) ) 
         )%type
          end
         ).
  all:cbn in Gw; get_from_hyp Gw.

- move:Aw.
  unshelve simple refine (
      match Ap with
        starp Γ => (fun Tw => (Σ (Γmr : Σ Γm , Con_r Γ _ Γm),  (GTm = ( Γmr.1 ; starm _ ))%type))
      | arp Γ A t u => fun Tw =>
                        (Σ 
                           (tmr : (Σ ΓAtm, (Tm_r Γ A t _ ΓAtm)))
                           (umr : (Σ ΓAum, (Tm_r Γ A u _ ΓAum)))
                           (* paranoid stuff *)
                           (Γmr : Σ Γm, Con_r Γ _ Γm)
                           (Amr : Σ Am, Ty_r Γ A _ Am)
                           (eqΓ : Amr.1.1 = Γmr.1)
                           (eqAt : tmr.1.1 = Amr.1)
                           (eqAu : umr.1.1 = Amr.1)
                            ,
                            (GTm = (_ ; arm (eqAt @ eqAu^ # tmr.1.2) (  umr.1.2)))
                        )%type
      end).
  all:clear -Tw; cbn in Tw; get_from_hyp Tw.

- move:tw.
  Ltac get_from_some_hyp :=
    match goal with
      h : _ |- _ => get_from_hyp h
    end.
          (* get_from_some_hyp. *)
   unshelve refine (
       match tp with
         vp Γ A x => fun tw => Σ (ΓTxmr : Σ ΓTxm , (Var_r Γ A x _ ΓTxm))

                             (* paranoid  stuff *)
                             (Γmr : Σ Γm , Con_r Γ _ Γm)
                             (Amr : Σ Am , Ty_r Γ A _ Am)
                             (eq_Γ : Amr.1.1 = Γmr.1)
                             (eq_A : ΓTxmr.1.1 = Amr.1)
                           , (GTpm = (ΓTxmr.1.1 ; vam ΓTxmr.1.2) )%type
       | coh Γ Δ Δcp A Acp δ =>  fun tw =>
                                  (Σ (σmr : Σ σm, (Sub_r Γ Δ δ _ σm))  (Amrc : Σ Am, (isCTy_r Δ Δcp A Acp _ Am))
                                     (eqΔ : σmr.1.2.1 = Amrc.1.1.1)
                                     (* paranoid stuff *)
                                     (Δmr : Σ Δm , Con_r Δ _ Δm)
                                     (Γmr : Σ Γm , Con_r Γ _ Γm)
                                     (Amr : Σ Am , Ty_r Δ A _ Am)
                                     (eqΓσ_par : σmr.1.1 = Γmr.1)
                                     (eqΔ_par : Amr.1.1 = Δmr.1 )
                                     (eqA_par : Amr.1 = (Amrc.1.1.1 ; Amrc.1.2.1))
                                     (* already by eqΔ , eqA_par and eqΔ_par *)
                                     (* (eqΔσ_par : σmr.1.2.1 = Δmr.1) *)
                                   ,
                                   (GTpm = ((σmr.1.1 ; _) ;
                                            subTmm (eqΔ # σmr.1.2.2) (cohm (Δc := _) Amrc.1.2.2)))
                                   
                                  )%type
       | dumt => fun tw => Empty_rect _
       end).
   all:get_from_some_hyp.
   all:cbn in tw; get_from_hyp tw.

- move:xw.
  unshelve refine
           ( match xp with
               v0 Γ A => fun qw =>
                          (Σ (ΓAmr : Σ ΓAm , Ty_r Γ A _ ΓAm)
                           (* paranoid stuff *)
                             (Γmr : Σ Γm , Con_r Γ _ Γm)
                             (eΓ : ΓAmr.1.1 = Γmr.1)
                           ,
                           (GTpm = ((consm ΓAmr.1.2 ; _) ; v0m ΓAmr.1.2)))
             | vS Γ A x Ex =>
               fun qw => (
                   Σ (ΓAxmr : Σ ΓAxm , Var_r Γ A x _ ΓAxm)
                     (ΓExmr : Σ ΓExm, Ty_r Γ Ex _ ΓExm)
                     (ΓExp : Σ Exm , ΓExmr.1 = (_ ; Exm))
                     (* (eΓ : ΓAxmr.1.1.1 = ΓExmr.1.1) *)
                   (* paranoid stuff *)
                     (* (Γmr : Σ Γm , Con_r Γ _ Γm) *)
                     (* (Amr : Σ ΓAm, Ty_r Γ A _ ΓAm) *)
                     (* (eΓA_par : Amr.1.1 = Γmr.1) *)
                     (* (eAx_par : ΓAxmr.1.1 = Amr.1) *)
                     (* already known *)
                     (* (eΓEx_par : Exmr.1.1 = Γmr.1) *)
                     
                   ,
                   GTpm = ((consm ( ΓExp.1) ; _) ; vSm ΓAxmr.1.2 _)
                 )

           end);cbn in qw; get_from_hyp qw.
  

- move :σw.
  unshelve refine (match σp with
            to_nilp Γ => fun sw =>
                          (Σ (Γmr : Σ Γm, Con_r Γ _ Γm),
                           GHsm = (Γmr.1 ; nilm ; to_nilm _))
          | to_consp Γ Δ σ A t =>
            fun sw =>
              (Σ (σmr : (Σ σm , Sub_r Γ Δ σ _ σm))
                 (Amr : (Σ Am , Ty_r Δ A _ Am))
                 (tmr : (Σ tm , Tm_r Γ (subTyp Γ σ A) t _ tm))
                 (Γm := tmr.1.1.1)
                 (Δm := Amr.1.1)
                 (σmp : (Σ σm, σmr.1 = (Γm ; Δm ; σm)))
                 (tmp : (Σ tm, (tmr.1.1.2 ; tmr.1.2) = ((subTym σmp.1 Amr.1.2) ; tm)))
               ,
               (GHsm = (_ ; _ ; to_consm (tmp.1))) 
               
              )
                                   
          end) ; cbn in sw ; get_from_hyp sw.
  (* now contractible stuff *)
- revert Γcw.
  exact (
   match Γc as Γc0 return (isContrw Γp Γc0 -> Type) with
  | isC_astarp =>  fun Gcw => Gmc = (consm (starm nilm) ; isC_astarm) 
  | isC_consconsp Γ Γc A Ac u uc =>
    fun Gcw =>
      (
        Σ (umcr : Σ umc,  isCTm_r  Γ Γc A Ac u uc ((ltac: (cbn in Gcw; get_from_hyp Gcw )) :   isCTmw Γ Γc A Ac u uc)  umc),
        Gmc =
        (consm 
               (arm 
                  (A := wkTym umcr.1.1.2.1 umcr.1.1.2.1)
                  (vam
                     (Γ := consm (Γ := umcr.1.1.1.1) umcr.1.1.2.1)
                     (v0m umcr.1.1.2.1))
                  (wkTmm
                     (((umcr.1).1).2).1
                     ((umcr.1).2).1)) ;
         isC_consconsm umcr.1.2.2)
      )
  end). 

- move:Aw.
  simple refine (
      match Ac with
        isC_starp Γ Γc => (fun Tw =>
                            (Σ (Γmcr : Σ Γmc , isContr_r Γ Γc _ Γmc),
                             Gmc = (Γmcr.1 ; _ ; isC_starm _)))
      | isC_arp Γ Γc A Ac t tc u uc =>
        fun Tw =>
          (Σ (tmcr : Σ tmc , isCTm_r Γ Γc A Ac t tc _ tmc)
             (umcr : Σ umc , isCTm_r Γ Γc A Ac u uc _ umc)
             (Amcr := tmcr.1.1)
             (umpc : Σ umc, umcr.1 = (Amcr ; umc)) ,
           Gmc = (_ ; _ ; isC_arm tmcr.1.2.2 umpc.1.2))
      end).
  all: cbn in Tw ;get_from_hyp Tw.

- move : tcw.

   unshelve simple eapply (
       match tc with
         isC_vp Γ Γc A Ac x xc =>
         fun tcw => (Σ (xmcr : Σ xmc , isCVar_r Γ Γc A Ac x xc _ xmc) ,
                  GTpmc = (xmcr.1.1 ; _  ;  isC_vm xmcr.1.2.2)
                            )
       | isC_cohp Γ Γc Δ Δc A Ac σ σc =>

         fun tcw =>
           (Σ (Γmcr : Σ Γmc, isContr_r Γ Γc _ Γmc)
              (Amcr : Σ Amc , isCTy_r Δ Δc A Ac _ Amc)
              (σmcr : Σ σmc , isCSub_r Γ Γc Δ Δc σ σc _ σmc)

              (σmcp : Σ σmc, σmcr.1 = (Γmcr.1 ; Amcr.1.1 ; σmc))
            ,
            GTpmc = (
              (Γmcr.1 ; _ ; subisCTym σmcp.1.2 Amcr.1.2.2) ;  _  ;  (subisCTmm _ (isC_cohm _)) ) 
            )
        | isC_dumt => (fun tcw => (Empty_rect _) )
       end) ; last first.
   exact tcw.
   all:  (cbn in tcw ; get_from_hyp  tcw).

- move:xcw.
  unshelve refine
  (match xc with
  | isC_vstarp => fun qw => 
                   (* these holes are inferred *)
                   GTqmc =  ( ((_ ; isC_astarm) ; (_ ; isC_starm _ )) ; _ ; isC_vstarm)
  | isC_v0p Γ Γc A Ac u uc =>
    fun qw =>
      (Σ (umcr : Σ umc, isCTm_r Γ Γc A Ac u uc _ umc),
       GTqmc = (((_ ;  _) ; (_ ; _)); _ ; isC_v0m umcr.1.2.2)
        )
  | isC_v1p Γ Γc A Ac u uc => 
    fun qw => 
      (Σ (umcr : Σ umc, isCTm_r Γ Γc A Ac u uc _ umc),
       GTqmc = (((_ ;  _) ; (_ ; _)); _ ; isC_v1m umcr.1.2.2)
        )

  | isC_vSSp Γ Γc A Ac u uc B Bc x xc  =>
    fun qw => 
      (Σ (umcr : Σ umc, isCTm_r Γ Γc A Ac u uc _ umc)
         (xmcr : Σ xmc, isCVar_r Γ Γc B Bc x xc _ xmc)
         (xmcp : Σ Bmc xmc, xmcr.1 = ((umcr.1.1.1 ; Bmc) ; xmc))
         (* (xmcp : Σ Bxmc , (xmcr.1.1.1 ; xmcr.1.1.2 ; xmcr.1.2) = (umcr.1.1.1 ; Bxmc)) *)
         (* (eΓ : umcr.1.1.1 = xmcr.1.1.1) *)
       ,
       GTqmc =
            (((_ ; isC_consconsm umcr.1.2.2);
              (_ ; isCwkwkTym umcr.1.2.2 xmcp.1.2)) ;
             (_ ; isC_vSSm umcr.1.2.2 xmcp.2.1.2))
      )
    end) ; cbn in qw; try get_from_hyp qw.

- move:σcw.
  unshelve refine (
       match σc with
       | isC_to_astarp Γ Γc t tc => 
         fun sw =>
           (Σ (tmcr : Σ tmc ,  isCTm_r Γ Γc (starp Γ) (isC_starp Γ Γc) t tc _ tmc)
              (starmc := (starm tmcr.1.1.1.1 ; isC_starm tmcr.1.1.1.2))
              (tmcp : Σ tmc,
                      (tmcr.1.1.2 ; tmcr.1.2) = existT (fun x => sigT (isCTmm (A := x.1) x.2)) starmc tmc ),
                      
            GHsmc = (tmcr.1.1.1 ; (_ ; isC_astarm) ; _ ;
                     isC_to_astarm tmcp.1.2)
           )
       | isC_to_consconsp Γ Γc Δ Δc A Ac u uc σ σc t tc f fc =>
            fun sw => 
         let Aσ := subTyp Γ σ A in
         let Aσc := subisCTyp Γ Γc σ σc Ac in
         let uσ := subTmp Γ σ u in
         let uσc := subisCTmp Γ Γc σ σc uc in
         (
           Σ (umac : sigT (@isCTm_r  Δ Δc A Ac u uc _ ))
            (σmcr : Σ σmc , isCSub_r Γ Γc Δ Δc σ σc _ σmc)
            (tmcr : Σ tmc , isCTm_r Γ Γc Aσ Aσc t tc _ tmc)
            (fmcr : Σ fmc , isCTm_r Γ Γc
                                    (arp Γ Aσ t uσ)
                                    (isC_arp Γ Γc Aσ Aσc t tc uσ uσc )
                                    f fc _ fmc)
            (umc := umac.1.2)
            (Δmc := umac.1.1.1)
            (Amc := umac.1.1.2)
            (Γmc := σmcr.1.1)
            (σmeq : Σ σm, σmcr.1.2 = (Δmc ; σm))
             (σmc := σmeq.1)
             (tmeq : Σ tm, tmcr.1 = ((Γmc ; _ ; subisCTym σmc.2 Amc.2) ; tm ))
             (tmc := tmeq.1)
             (fmeq : Σ fm, fmcr.1 = ((Γmc ; _ ; isC_arm tmc.2 (subisCTmm σmc.2 umc.2)) ; fm ))
             (fmc := fmeq.1),
             GHsmc = (Γmc ; (_ ; isC_consconsm umc.2) ; _ ; isC_to_consconsm fmc.2 )
           )

              

              
                
         
       end
    ) ; cbn in sw;  try get_from_hyp sw.
  (* (tmcr.1.1.2 ; tmcr.1.2) *)
  

  
Defined.


Context {sCon : IsHSet Conm}{sTy: forall Γ, IsHSet (Tym Γ)}
        {sContrm : forall Γ, IsHSet (isContrm Γ)}
        (* TODO : comprendre pourquoi c'est nécessaire (je crois que c'est pour isCTy_r la flèche)  *)
        {sCTy : forall Γ Γc A, IsHSet (isCTym (Γ := Γ) Γc A)} .

Ltac swap_sig := (etransitivity; last by apply:equiv_sigma_symm);
      cbn;
      apply:equiv_functor_sigma_id;
      intros ?.

(* TODO move this into lib coqhott *)
  Lemma
equiv_sigma_assoc' :
forall (A : Type) (P : A -> Type) (Q : forall a, P a -> Type), (Σ (a : A) (p : P a), Q a p) <~> (Σ y, Q y.1 y.2).
    intros.
    apply:(equiv_sigma_assoc P (fun x => Q x.1 x.2)).
    Defined.

(* Definition test : Is_hprop (Σ Gm : Conm, Gm = nilm) := _. *)
(* refine _. *)
Ltac hset_hprop := match goal with |- IsHProp (@eq ?A ?x ?y)  => refine ((_ : IsHSet A) x y) end.
Ltac generate_sigma_goals :=
  (apply @trunc_succ; (refine ( contr_basedpaths' _) || refine ( contr_basedpaths _))) ||
  (unshelve eapply @trunc_sigma ; cbn ; intros; [|generate_sigma_goals]).

Ltac hp_r_solve' :=
  intros;
   (by apply:Empty_rect) ||
   ((eapply trunc_equiv'; first by repeat swap_sig; apply:equiv_idmap) ;
     generate_sigma_goals; 
     (* easy uses the induction hypthesis *)
     try (
        easy || by hset_hprop  
     )
       ).
(*
     repeat ( (apply @trunc_succ; refine ( contr_basedpaths' _)) ||
              (unshelve eapply @trunc_sigma ; cbn ; intros; [
                 (* try easy *)
                 (* (easy || hset_hprop || idtac) *)
                |]
               (* try (apply @trunc_succ;  refine ( contr_basedpaths _)) *)


            ))
                   (* try refine ((_ : IsHSet _) _ _) )) *)
   ]
         ).
*)
Ltac hp_r_solve := hp_r_solve'.
                   (* ; (try easy);( try hset_hprop). *)


  (* + unshelve eapply @trunc_sigma ; cbn ; intros. *)
  (*   eapply trunc_equiv'. *)
  (*   * etransitivity; last first. *)
  (*     -- eapply equiv_functor_sigma_id => ?;  apply:equiv_path_sigma. *)
  (*     -- simpl. *)
  (*        swap_sig. *)

(* the relation is hprop *)
  (* ? <-> Σ a ; aze = (_ ; _ ; .. ; a)
   becomes  
    Σ ....  a, aze.2.2... .2 = a
*)
  Ltac rightmost_sigmaequiv :=
    repeat (etransitivity; [ |
    (etransitivity; last by eapply equiv_functor_sigma_id => ? /=; apply:equiv_path_sigma);
    simpl;
    apply equiv_sigma_symm => /= 
                   ];
    simpl;
    (try simpl; eapply equiv_functor_sigma_id => ? /=));
    apply equiv_idmap.
  (* solves HProp (Σ a ; aze = (_ ; _ ; .. ; a)) *)
Ltac fuck :=
  (
    eapply trunc_equiv';
    [ rightmost_sigmaequiv
    | 
    ]; simpl; generate_sigma_goals; try hset_hprop
  ).
Fixpoint Con_r_hp (Γp : Conp ) (Γw : Conw Γp)  {struct Γp} :
  IsHProp (sigT ( Con_r Γw  ))
with Ty_r_hp (Γp : Conp)(Ap : Typ) (Aw : Tyw Γp Ap) {struct Ap} :
       IsHProp (sigT ( Ty_r  Aw ))
with Tm_r_hp  (Γp : Conp)(Ap : Typ)(tp : Tmp) (tw : Tmw Γp Ap tp) {struct tp} :
       IsHProp (sigT ( Tm_r tw ))  
  with Var_r_hp  (Γp : Conp)(Ap : Typ)(xp : Varp) (xw : Varw Γp Ap xp){struct xp}
       : IsHProp (sigT ( Var_r xw )) 
  with Sub_r_hp  (Γp Δp : Conp)(σp : Subp) (σw : Subw Γp Δp σp){struct σp}
       : IsHProp (sigT ( Sub_r σw )) 
  with isContr_r_hp (Γp : Conp) (Γc : isContrp) (Γcw : isContrw Γp Γc){struct Γc}
       : IsHProp (sigT ( isContr_r Γcw )) 
  with isCTy_r_hp (Γp : Conp) Γc (Ap : Typ) Ac (Aw : isCTyw Γp Γc Ap Ac){struct Ac}
       : IsHProp (sigT ( isCTy_r Aw )) 
  with isCTm_r_hp (Γp : Conp) Γc (Ap : Typ) Ac (tp : Tmp) tc (tcw : isCTmw Γp Γc Ap Ac tp tc){struct tc}
       : IsHProp (sigT ( isCTm_r tcw )) 
  with isCVar_r_hp (Γp : Conp) Γc (Ap : Typ) Ac (xp : Varp) xc (xcw : isCVarw Γp Γc Ap Ac xp xc){struct xc}
       : IsHProp (sigT ( isCVar_r xcw )) 
  with isCSub_r_hp  (Γp : Conp) Γc (Δp : Conp) Δc (σp : Subp ) σc (σcw : isCSubw Γp Γc Δp Δc σp σc){struct σc}
       : IsHProp (sigT ( isCSub_r σcw )) .

  - case:Γp Γw => /=; hp_r_solve.
    
(* *****************



Types



******************* *)
- case:Ap Aw => /=; hp_r_solve; hset_hprop.
      (* *****************



Termes



******************* *)
- case:tp tw => /= ; hp_r_solve.
(* *****************



Variables



******************* *)
- case:xp xw => /=; hp_r_solve.

fuck.


(* *****************



SUbstitutions



******************* *)
- case:σp σw => /=;hp_r_solve; fuck.

- case:Γc Γcw => /=; hp_r_solve.

- case:Ac Aw => /= ; hp_r_solve; fuck.
- case:tc tcw => /=; hp_r_solve; fuck.
- case:xc xcw => /= ; hp_r_solve.
    eapply trunc_equiv'.
    {
      etransitivity; last first.
      - apply: equiv_functor_sigma_id => ? /=.
        rightmost_sigmaequiv.
      - symmetry.
        apply:equiv_sigma_assoc'.
    }
    simpl.
    generate_sigma_goals.
    fuck.
- case:σc σcw => /= ; hp_r_solve; fuck.

Defined.
End rec.

Fixpoint Conw_hp Γ : IsHProp (Conw Γ)
with Tyw_hp Γ A : IsHProp (Tyw Γ A)
with Tmw_hp Γ A t : IsHProp (Tmw Γ A t)
with Subw_hp Γ Δ σ  : IsHProp (Subw Γ Δ σ)
with isContrw_hp Γ Γc   : IsHProp (isContrw Γ Γc)
with isCTmw_hp Γ Γc A Ac t tc  : IsHProp (isCTmw Γ Γc A Ac t tc).
Admitted.


Existing Instance Conw_hp .
Existing Instance Tyw_hp.
Existing Instance Tmw_hp.
Existing Instance Subw_hp.
Existing Instance isContrw_hp.
Existing Instance isCTmw_hp.
