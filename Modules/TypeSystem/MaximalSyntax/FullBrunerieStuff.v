
Require Import ssreflect.
Require Import Modules.TypeSystem.FromHottLibPrimProj.Overture.
Require Import Modules.TypeSystem.FromHottLibPrimProj.PathGroupoids.
Require Import Modules.TypeSystem.FromHottLibPrimProj.Contractible.
Require Import Modules.TypeSystem.FromHottLibPrimProj.Trunc.
Require Import Modules.TypeSystem.FromHottLibPrimProj.Sigma.
Require Import Modules.TypeSystem.FromHottLibPrimProj.Prod.
Require Import Modules.TypeSystem.FromHottLibPrimProj.Equivalences.
Require Import Modules.TypeSystem.MaximalSyntax.FullBruneriePrimProj.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac get_from_hyp' h :=

  exact h 
  (* || let x := constr:(fst h) in get_from_hyp' x *)
  (* || let x := constr:(snd h) in get_from_hyp' x *)
  || (let x := constr:( h.1) in get_from_hyp' x)
  || (let x := constr:( h.2) in get_from_hyp' x).
Ltac sigma_eassumption :=
  match goal with
    h: _ |- _ => get_from_hyp' h
  end.
Ltac find_orig_tm t :=
  match t with
    ?x.1 =>   find_orig_tm x
  | ?x.2 => find_orig_tm x
  | _ => t
  end.
Ltac case_by_eq  :=
  match goal with
    h : ?x.1 = _ |- _ =>
    let t := find_orig_tm x in
    destruct t
  | h : ?x.2 = _ |- _ => let t:=  find_orig_tm x in destruct t
  end.
Definition sigT_rect' (A : Type) (P : A -> Type) (P0 : (Σ x : A , P x) -> Type)
      (h : (forall (x : A) (p : P x), P0 ( x ; p))) (  s : (Σ x : A , P x)): P0 s := h s.1 s.2.
 (* TODO : utiliser cette tactique et cette manière de faire dans sbRel, wkRel *)
Ltac better_recursive_destruct_sigma :=
  repeat (refine (sigT_rect' _); simpl; intro); intros; repeat ( subst; simpl in *; try case_by_eq).

Ltac replace_hp :=
  match goal with
    |- ?h _ ?y => eapply (transport (fun x => h x y) (path_ishprop _ _))
  end.

Definition sigT_rect (A : Type) (P : A -> Type) (P0 : (Σ x : A , P x) -> Type)
      (h : (forall (x : A) (p : P x), P0 ( x ; p))) (  s : (Σ x : A , P x)): P0 s := h s.1 s.2.
  
Definition sigT_path_rect (A : Type) (P : A -> Type)(u v : sigT P) (Q : u = v -> Type)
           (h : (forall (e1 : u.1 = v.1) (e2 : e1 # u.2 = v.2), Q (path_sigma _ _ _  e1 e2))) (  e : u = v) : Q e
   :=   transport Q (eta_path_sigma e) (h e ..1 e ..2).

Ltac recursive_destruct_sigma :=
         (repeat ((repeat refine (sigT_rect _)) ; simpl; (repeat refine (sigT_path_rect _) );  intro));
       simpl in *; repeat (subst; simpl in * ).

Definition path_consp Γ Γ' A A' (eC : Γ = Γ') (eA : A = A') : Γ ▷A = Γ' ▷ A' :=
  ap (consp Γ) eA @ ap (fun x => consp x _) eC.

Definition pr1_path_consp Γ Γ' A A' (e : Γ ▷ A = Γ' ▷ A') : Γ = Γ' :=
  match e with eq_refl => eq_refl end.
Definition pr2_path_consp Γ Γ' A A' (e : Γ ▷ A = Γ' ▷ A') : A = A' :=
  match e with eq_refl => eq_refl end.

Definition eta_path_consp  Γ Γ' A A'  (e : Γ ▷A = Γ' ▷ A' ) : path_consp (pr1_path_consp e) (pr2_path_consp e) = e :=
  match e as p in _ = c return
        match c as c return _ = c -> Type with
          C ▷ B => fun p => path_consp (pr1_path_consp p) (pr2_path_consp p) = p

        | ∙ => fun p => IDProp
        end
          p
  with eq_refl => eq_refl end.
Ltac moveL_transport_V_tac h :=
  match type of h with
    transport ?P ?e ?x = ?y => move:(moveL_transport_V P e x y h)
  end.



(* TODO : déplacer ça dans FullBrunerie *)




Definition pr1_path'  (A : Type) (P : A -> Type) u v (u' : P u) (v' : P v) :
       (u ; u') = (v ; v') -> u = v := pr1_path.
Section rec.
Context (m : Model).


Context {sCon : IsHSet Conm}{sTy: forall Γ, IsHSet (Tym Γ)}
        {sContrm : forall Γ, IsHSet (isContrm Γ)}
        {sCTy : forall Γ Γc A, IsHSet (isCTym (Γ := Γ) Γc A)} .

Definition path_Con_r (Γp : Conp) (Γw : Conw Γp)(Γw' : Conw Γp)
           Γm Γm' (Γr : Con_r Γw Γm)(Γr' : Con_r Γw' Γm') : Γm = Γm'.
  eassert (h := path_ishprop (H := Con_r_hp (Γw := Γw)) (Γm ; Γr) (_ ; _)).
  eapply  (pr1_path h).
  Unshelve.
  replace_hp; eassumption.
Defined.

Definition path_Ty_r (Γp : Conp) Ap (Aw : Tyw Γp Ap)(Aw' : Tyw Γp Ap)
           Am Am' (Ar : Ty_r Aw Am)(Γr' : Ty_r Aw' Am') : Am = Am'.
  eassert (h := path_ishprop (H := Ty_r_hp (Aw := Aw)) (Am ; Ar) (_ ; _)).
  eapply  (pr1_path h).
  Unshelve.
  replace_hp; eassumption.
Defined.

Definition path_isContr_r (Γp : Conp) (Γc : isContrp) (Γw Γw' : isContrw Γp Γc)
           Γm Γm' (Γr : isContr_r Γw Γm)(Γr' : isContr_r Γw' Γm') : Γm = Γm'.
  eassert (h := path_ishprop (H := isContr_r_hp (Γcw := Γw)) (Γm ; Γr) (_ ; _)).
  eapply  (pr1_path h).
  Unshelve.
  replace_hp; eassumption.
Defined.

End rec.


