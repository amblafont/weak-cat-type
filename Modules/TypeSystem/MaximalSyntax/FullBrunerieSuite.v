
Require Import ssreflect.
Require Import Modules.TypeSystem.FromHottLibPrimProj.Overture.
Require Import Modules.TypeSystem.FromHottLibPrimProj.PathGroupoids.
Require Import Modules.TypeSystem.FromHottLibPrimProj.Contractible.
Require Import Modules.TypeSystem.FromHottLibPrimProj.Trunc.
Require Import Modules.TypeSystem.FromHottLibPrimProj.Sigma.
Require Import Modules.TypeSystem.FromHottLibPrimProj.Prod.
Require Import Modules.TypeSystem.FromHottLibPrimProj.Equivalences.
Require Import Modules.TypeSystem.MaximalSyntax.FullBruneriePrimProj.
(* Require Import Modules.TypeSystem.MaximalSyntax.FullBrunerieSbRel. *)
Require Import Modules.TypeSystem.MaximalSyntax.FullBrunerieStuff.

(* Require Import Modules.TypeSystem.MaximalSyntax.FullBrunerieWkRel. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* This is required to show subisCTyw *)
(* MAYBE ALL THIS STUFF iS USELESS in that case I can remove isC_dumt *)
Fixpoint subsubisCTyp E Ec Γ Γc σ σc δ δc Ac :
  subisCTyp E Ec σ σc (subisCTyp Γ Γc δ δc Ac) = subisCTyp E Ec (subSubp E σ δ) (subisCSubp E Ec σ σc δc) Ac
  with subsubisCTmp  E Ec Γ Γc σ σc δ δc tc :
  subisCTmp E Ec σ σc (subisCTmp Γ Γc δ δc tc) = subisCTmp E Ec (subSubp E σ δ) (subisCSubp E Ec σ σc δc) tc
  with subsubisCVarp  E Ec Γ Γc σ σc δ δc xc :
  subisCTmp E Ec σ σc (subisCVarp Γ Γc δ δc xc) = subisCVarp E Ec (subSubp E σ δ) (subisCSubp E Ec σ σc δc) xc
  with subsubisCSubp  E Ec Γ Γc σ σc δ δc  εc :
         subisCSubp E Ec σ σc (subisCSubp Γ Γc δ δc εc) =
         subisCSubp E Ec (subSubp E σ δ) (subisCSubp E Ec σ σc δc) εc.

  - destruct Ac => /=; first by reflexivity.
    f_ap; apply subsubTyp || apply subsubTmp.
  - destruct tc => /=; try easy.
    f_ap; apply subsubSubp.
  - destruct xc => /=; destruct δc => /=; try reflexivity.
    easy.
  - destruct εc => /=; f_ap; apply subsubTmp || apply subsubSubp.
Defined.

(* this is required to show subisCTyw *)
Fixpoint sub_cons_wkisCTyp Γ Γc Δ Δc δ δc A Ac u uc t tc f fc Bc :
  subisCTyp Γ Γc δ δc Bc =
  subisCTyp Γ Γc (to_consp Γ (Δ ▷ A) (to_consp Γ Δ δ A t) (arcons Δ A u) f)
            (isC_to_consconsp Γ Γc Δ Δc A Ac u uc δ δc t tc f fc) (wkisCTyp A Ac u uc Bc)
with sub_cons_wkisCTmp  Γ Γc Δ Δc δ δc A Ac u uc t tc f fc zc :
  subisCTmp Γ Γc δ δc zc =
  subisCTmp Γ Γc (to_consp Γ (Δ ▷ A) (to_consp Γ Δ δ A t) (arcons Δ A u) f)
            (isC_to_consconsp Γ Γc Δ Δc A Ac u uc δ δc t tc f fc) (wkisCTmp A Ac u uc zc)
with sub_cons_wkisCSubp  Γ Γc Δ Δc δ δc A Ac u uc t tc f fc σc :
       subisCSubp Γ Γc δ δc σc =
  subisCSubp Γ Γc (to_consp Γ (Δ ▷ A) (to_consp Γ Δ δ A t) (arcons Δ A u) f)
    (isC_to_consconsp Γ Γc Δ Δc A Ac u uc δ δc t tc f fc) (wkisCSubp A Ac u uc σc).

Proof.
  - destruct Bc => /=.
    + reflexivity.
    + f_ap; etransitivity; eapply sub_cons_wkTyp|| eapply sub_cons_wkTmp.
  - destruct zc => /=; try reflexivity.
    + f_ap.
      etransitivity; eapply sub_cons_wkSubp|| eapply sub_cons_wkSubp.
  - destruct σc => /=.
    + f_ap.
      etransitivity; eapply sub_cons_wkTmp|| eapply sub_cons_wkTmp.
    + f_ap; etransitivity; eapply sub_cons_wkSubp|| eapply sub_cons_wkTmp.
Defined.



(* This is requried to show subisCTyr *)
Fixpoint subisCTyw (E : Conp)(Ew : Conw E)(Ec : isContrp)(Ecw : isContrw E Ec) (H : Conp) Hc (σ : Subp) (σw : Subw E H σ) (σc: isCSubp) (σcw : isCSubw E Ec H Hc σ σc)
          (A : Typ)(Ac : isCTyp) (Aw : isCTyw H Hc A Ac)
          {struct Ac} : isCTyw E Ec (subTyp E σ A) (subisCTyp E Ec σ σc Ac)
with subisCTmw (E : Conp)(Ew : Conw E)(Ec : isContrp)(Ecw : isContrw E Ec) (H : Conp) Hc (σ : Subp) (σw : Subw E H σ)(σc: isCSubp) (σcw : isCSubw E Ec H Hc σ σc)
                (A : Typ) Ac t tc  (tw : isCTmw H Hc A Ac t tc) {struct tc} :
        isCTmw E Ec (subTyp E σ A) (subisCTyp E Ec σ σc Ac) (subTmp E σ t) (subisCTmp E Ec σ σc tc)
with subisCVarw (E : Conp)(Ew : Conw E)(Ec : isContrp)(Ecw : isContrw E Ec) (H : Conp) Hc (σ : Subp) (σw : Subw E H σ)(σc: isCSubp) (σcw : isCSubw E Ec H Hc σ σc)
                (A : Typ) Ac x xc  (xw : isCVarw H Hc A Ac x xc) {struct xc} : isCTmw E Ec (subTyp E σ A)
                                                                                      (subisCTyp E Ec σ σc Ac)
                                                                                      (subVarp E σ x) (subisCVarp E Ec σ σc xc)
with subisCSubw  (E : Conp)(Ew : Conw E)(Ec : isContrp)(Ecw : isContrw E Ec) (H : Conp) Hc (σ : Subp) (σw : Subw E H σ)(σc: isCSubp) (σcw : isCSubw E Ec H Hc σ σc)
                  (G : Conp) Gc (δ : Subp) (δc: isCSubp) (δcw : isCSubw H Hc G Gc δ δc) {struct δc} :
        isCSubw E Ec G Gc (subSubp E σ δ) (subisCSubp E Ec σ σc δc).
- move:Aw.
refine         (match Ac with
                isC_starp Γ Γc => fun Aw => _
              | isC_arp Γ Γc A Ac t tc u uc => fun Aw => _
                end); simpl; simpl in Aw; repeat destruct_eqs Aw.
+ repeat split; try assumption || get_from_hyp Aw.
+ repeat split; try assumption || get_from_hyp Aw.
  all:(apply :subTyw || apply :subTmw || apply:subisCTyw || apply:subisCTmw ); eassumption || get_from_hyp Aw.
- move:tw.
  refine(
       match tc with
         isC_vp Γ Γc A Ac x xc => fun tw => _
       | isC_cohp Γ Γc Δ Δc A Ac δ δc => fun tw => _
       | isC_dumt => fun  tw => Empty_rect _
       end); simpl; simpl in tw; last by exact tw.
  all:repeat destruct_eqs tw.
  + eapply subisCVarw; get_from_hyp tw || eassumption.
  + repeat split; try assumption || get_from_hyp tw.
    * apply:subSubw; eassumption || get_from_hyp tw.
    * apply:subisCSubw; eassumption || get_from_hyp tw.
    * apply:subsubTyp.
    * apply:subsubisCTyp.
- move:σw σcw xw.
  refine(
             match xc with 
             | isC_vstarp => if σc is isC_to_astarp Γ Γc t tc then
                              fun σw σcw xw =>  _
                            else 
                              fun σw σcw xw => Empty_rect _
             | isC_v0p Γ' Γc' A' Ac' u' uc' =>
               if σc is isC_to_consconsp Γ Γc Δ Δc A Ac u uc δ δc t tc f fc then
                 fun σw σcw xw =>  _
               else
                 fun σw σcw xw => Empty_rect _
             | isC_v1p Γ' Γc' A' Ac' u' uc' => 
               if σc is isC_to_consconsp Γ Γc Δ Δc A Ac u uc δ δc t tc f fc then
                 fun σw σcw xw =>  _
               else
                 fun σw σcw xw => Empty_rect _
             | isC_vSSp Γ' Γc' A' Ac' u' uc' B Bc x xc  =>
               if σc is isC_to_consconsp Γ Γc Δ Δc A Ac u uc δ δc t tc f fc then
                 fun σw σcw xw =>   _
               else
                 fun σw σcw xw => Empty_rect _
             end);move => /= ; simpl in σw ,σcw, xw.
  1: by repeat destruct_eqs xw; repeat destruct_eqs σcw; simpl; get_from_hyp σcw.

  all: (eassert (h1 : Hc = _) ; first by get_from_hyp xw);
    (eassert (h2 : Hc = _) ; first by get_from_hyp σcw);
    move:(h1^ @ h2); try discriminate. 
  all:case ;intros; subst => /=.
  (* all:case  => ?? _ _ _ _ _ _ _ _ hu {h1 h2}; subst => /=. *)
  + eassert (hf : isCTmw _ _ _ _ _ fc) ; first by get_from_hyp σcw.
    repeat destruct_eqs xw => /=.
    repeat destruct_eqs σcw=> /=.
    move:hf.
    apply:(transport (fun x => x)).
    f_ap;f_ap; try (etransitivity; (eapply sub_cons_wkTyp || eapply sub_cons_wkTmp)).
    * apply sub_cons_wkisCTyp.
    * apply sub_cons_wkisCTmp.
  + eassert (hf : isCTmw _ _ _ _ _ tc) ; first by get_from_hyp σcw.
    repeat destruct_eqs xw => /=.
    repeat destruct_eqs σcw=> /=.
    move:hf.
    apply:(transport (fun x => x)).
    f_ap; try (etransitivity; (eapply sub_cons_wkTyp || eapply sub_cons_wkTmp)).
    by apply sub_cons_wkisCTyp.
  + eassert (hc : isCVarw _ _ _ _ _ xc); first by get_from_hyp xw. 
    repeat destruct_eqs xw .
    repeat destruct_eqs σcw.
    simpl.
    rewrite -!sub_cons_wkTyp -sub_cons_wkisCTyp.
    apply:subisCVarw; try eassumption || get_from_hyp σcw.
- move: δcw.
          refine (   match δc with
         isC_to_astarp Γ Γc t tc => 
         _
       | isC_to_consconsp Γ Γc Δ Δc A Ac u uc δ δc t tc f fc =>
         _
             end) ; move => /= δcw.
  + repeat destruct_eqs δcw.
    repeat split;try  get_from_hyp δcw ||  assumption.
    * apply:(subTmw _ _ (T := starp _)); get_from_hyp δcw || eassumption.
    * apply:(subisCTmw _ _ _ _ _ _ _ _ _ _  (starp _) (isC_starp _ _ )) ; get_from_hyp δcw || eassumption.
  + repeat destruct_eqs δcw.
    repeat split;try  get_from_hyp δcw ||  assumption.
    * erewrite <- subsubTyp.
      apply:subTmw; get_from_hyp δcw || eassumption.
    * apply:(transport (fun x => Tmw E x _)); last first.
      -- apply:subTmw; get_from_hyp δcw || eassumption.
      -- simpl. f_ap;[apply:subsubTyp|apply:subsubTmp].
    * apply:subSubw; get_from_hyp δcw || eassumption.
    * erewrite <- subsubTyp.
      erewrite <- subsubisCTyp.
      unshelve (apply:subisCTmw; get_from_hyp δcw || eassumption).
    * erewrite <- subsubTyp , <- subsubTmp, <- subsubisCTyp, <- subsubisCTmp.
      (apply:(subisCTmw _ _ _ _ _ _ _ _ _ _ (arp _ _  _ _)(isC_arp _ _ _ _ _ _ _ _)) ; get_from_hyp δcw || eassumption).
    * apply:subisCSubw; get_from_hyp δcw || eassumption.
Defined.

(*
Fixpoint subisCTyr (m : Model) (Γp Δp : Conp) Γw Γc Γcw Δc  σp σw σc (σcw : isCSubw Γp Γc Δp Δc σp σc)
         Γmc Δmc σm σmc 
         (* Γm (Γmc : isContrm Γm) Δm (Δmc : isContrm Δm)(σm : Subm Γm Δm) (σcm : isCSubm Γm Δm σm) *)
         (σcmr : isCSub_r σcw (Γmc ; Δmc ; (σm ;σmc)))
           (Ap : Typ)(Ac : isCTyp)  (Acw : isCTyw Δp Δc Ap Ac) (Am : Tym Δmc.1)
           (Amc : isCTym Δmc.2 Am)
           (Amr : isCTy_r Acw (Δmc ; Am ; Amc))
           {struct Ac} :
  isCTy_r (subisCTyw Γw Γcw σw σcw Acw) (Γmc; subTym σm Am; subisCTym σmc Amc)
with subisCTmr (m : Model) (Γp Δp : Conp) Γw Γc Γcw Δc (* (Γcw : isContrw Γp Γc) *) σp σw σc (σcw : isCSubw Γp Γc Δp Δc σp σc)
         σcm
         (* Γm (Γmc : isContrm Γm) Δm (Δmc : isContrm Δm)(σm : Subm Γm Δm) (σcm : isCSubm Γm Δm σm) *)
         (σcmr : isCSub_r σcw σcm)
           (Ap : Typ)Ac (tp : Tmp)(tc : isCTmp)  (tcw : isCTmw Δp Δc Ap Ac tp tc) (Am : Tym σcm.2.1.1) 
           (Amc : isCTym σcm.2.1.2 Am)
           tm tmc
           (tmr : isCTm_r tcw ((σcm.2.1 ; Am ; Amc) ; tm ; tmc))
           {struct tc} :
       isCTm_r (subisCTmw Γw Γcw σw σcw tcw) ((σcm.1; subTym ((σcm.2).2).1 Am; subisCTym ((σcm.2).2).2 Amc) ; _ ;
                  subisCTmm σcm.2.2.2 tmc).
  apply myadmit.
  apply myadmit.
  Defined.
*)
  (* isCTy_r ?Goal11 ((σmcr.1).1; subTym (σmeq.1).1 (((umcr.1).1).2).1; subisCTym (σmeq.1).2 (((umcr.1).1).2).2) *)
Axiom myadmit : forall A, A.
Fixpoint subisCTyr (m : Model) (Γp Δp : Conp) Γc Δc  σp σc (σcw : isCSubw Γp Γc Δp Δc σp σc)
         Γmc Δmc σm σmc 
         (* Γm (Γmc : isContrm Γm) Δm (Δmc : isContrm Δm)(σm : Subm Γm Δm) (σcm : isCSubm Γm Δm σm) *)
         (σcmr : isCSub_r σcw (Γmc ; Δmc ; (σm ;σmc)))
           (Ap : Typ)(Ac : isCTyp)  (Acw : isCTyw Δp Δc Ap Ac) (Am : Tym Δmc.1)
           (Acσw : isCTyw Γp Γc (subTyp Γp σp Ap) (subisCTyp Γp Γc σp σc Ac ))
           (Amc : isCTym Δmc.2 Am)
           (Amr : isCTy_r Acw (Δmc ; Am ; Amc))
           {struct Ac} :
  isCTy_r Acσw (Γmc; subTym σm Am; subisCTym σmc Amc)
with subisCTmr (m : Model) (Γp Δp : Conp) Γc Δc (* (Γcw : isContrw Γp Γc) *) σp σc (σcw : isCSubw Γp Γc Δp Δc σp σc)
         σcm
         (* Γm (Γmc : isContrm Γm) Δm (Δmc : isContrm Δm)(σm : Subm Γm Δm) (σcm : isCSubm Γm Δm σm) *)
         (σcmr : isCSub_r σcw σcm)
           (Ap : Typ)Ac 
           
           (tp : Tmp)(tc : isCTmp)  (tcw : isCTmw Δp Δc Ap Ac tp tc) (Am : Tym σcm.2.1.1) 
           (tcσw : isCTmw Γp Γc (subTyp Γp σp Ap) (subisCTyp Γp Γc σp σc Ac ) (subTmp Γp σp tp) (subisCTmp Γp Γc σp σc tc ))
           (Amc : isCTym σcm.2.1.2 Am)
           tm tmc
           (tmr : isCTm_r tcw ((σcm.2.1 ; Am ; Amc) ; tm ; tmc))
           {struct tc} :
       isCTm_r tcσw ((σcm.1; subTym ((σcm.2).2).1 Am; subisCTym ((σcm.2).2).2 Amc) ; _ ;
                  subisCTmm σcm.2.2.2 tmc).
  apply myadmit.
  apply myadmit.
  Defined.

(*
Fixpoint subisCTyr (m : Model) (Γp Δp : Conp)  Γc Δc  σp σc (σcw : isCSubw Γp Γc Δp Δc σp σc)
         σcm
         (* Γm (Γmc : isContrm Γm) Δm (Δmc : isContrm Δm)(σm : Subm Γm Δm) (σcm : isCSubm Γm Δm σm) *)
         (σcmr : isCSub_r σcw σcm)
           (Ap : Typ)(Ac : isCTyp)  (Acw : isCTyw Δp Δc Ap Ac) (Am : Tym σcm.2.1.1) 
           (Acσw : isCTyw Γp Γc (subTyp Γp σp Ap) (subisCTyp Γp Γc σp σc Ac ))
           (Amc : isCTym σcm.2.1.2 Am)
           (Amr : isCTy_r Acw (σcm.2.1 ; Am ; Amc))
           {struct Ac} :
  isCTy_r Acσw (σcm.1; subTym ((σcm.2).2).1 Am; subisCTym ((σcm.2).2).2 Amc)
with subisCTmr (m : Model) (Γp Δp : Conp) Γc Δc (* (Γcw : isContrw Γp Γc) *) σp σc (σcw : isCSubw Γp Γc Δp Δc σp σc)
         σcm
         (* Γm (Γmc : isContrm Γm) Δm (Δmc : isContrm Δm)(σm : Subm Γm Δm) (σcm : isCSubm Γm Δm σm) *)
         (σcmr : isCSub_r σcw σcm)
           (Ap : Typ)Ac (tp : Tmp)(tc : isCTmp)  (tcw : isCTmw Δp Δc Ap Ac tp tc) (Am : Tym σcm.2.1.1) 
           (tcσw : isCTmw Γp Γc (subTyp Γp σp Ap) (subisCTyp Γp Γc σp σc Ac ) (subTmp Γp σp tp) (subisCTmp Γp Γc σp σc tc ))
           (Amc : isCTym σcm.2.1.2 Am)
           tm tmc
           (tmr : isCTm_r tcw ((σcm.2.1 ; Am ; Amc) ; tm ; tmc))
           {struct tc} :
       isCTm_r tcσw ((σcm.1; subTym ((σcm.2).2).1 Am; subisCTym ((σcm.2).2).2 Amc) ; _ ;
                  subisCTmm σcm.2.2.2 tmc).
  apply myadmit.
  apply myadmit.
  Defined.
*)
Ltac try_rewrite h :=
  rewrite h  || (let x := constr:( h.2) in try_rewrite x) ||(let x := constr:( h.1) in try_rewrite x).
Ltac solve_all_r_gen :=
  simpl;intros Hw Hr;
  repeat (destruct_eqs Hw);
  simpl;
   match goal with |- ?Syn_r _ _ =>
                    apply:(transport (Syn_r _) _^) ;
                      [ try by repeat try_rewrite Hr => /= | ] ;
                      replace_hp;
                      try get_from_hyp' Hr
    end.

(* TODO : foutre ça dans stuff *)
(*
Ltac recursive_destruct_sigma :=
         (repeat ((repeat refine (sigT_rect _)) ; simpl; (repeat refine (sigT_path_rect _) );  intro));
       simpl in *; repeat (subst; simpl in * ).


Ltac get_from_hyp' h :=

  exact h 
  (* || let x := constr:(fst h) in get_from_hyp' x *)
  (* || let x := constr:(snd h) in get_from_hyp' x *)
  || (let x := constr:( h.1) in get_from_hyp' x)
  || (let x := constr:( h.2) in get_from_hyp' x).

Ltac try_rewrite h :=
  rewrite h  || (let x := constr:( h.2) in try_rewrite x) ||(let x := constr:( h.1) in try_rewrite x).
*)

Section rec.
Context (m : Model).


Context {sCon : IsHSet Conm}{sTy: forall Γ, IsHSet (Tym Γ)}
        {sContrm : forall Γ, IsHSet (isContrm Γ)}
        {sCTy : forall Γ Γc A, IsHSet (isCTym (Γ := Γ) Γc A)} .


(* Ltac solve_all_r_debut := *)
(*   simpl; intros Hw Hr; *)
(*   match goal with |- context [?e ^] => destruct (e ^) end ; *)

(* We need a tacti notation otherwise having a constr as an argument does not work *)
(* Tactic Notation "solve_all_r_gen" constr(Sr) := *)
  (* cbn; *)

(* Ltac solve_all_r := let x := constr:(Con_r) in solve_all_r_gen x. *)
Ltac solve_all_r  := by solve_all_r_gen.
(*
Ltac solve_all_r :=
  simpl;intros Hw Hr;
  (* repeat (destruct_eqs Hw); *)
  repeat (destruct_eqs Hw);
  cbn;



apply:(transport (Con_r _) _^) ;
  [ by repeat try_rewrite Hr => /= | ] ;
  apply : (transport (fun z => Con_r z _) (path_ishprop _ _));
  get_from_hyp' Hr.
  (* cbn; *)

*)
(*   apply:(transport (fun z => Con_r _ z) _^) ; *)
(* [ by repeat try_rewrite Hr => /= | by (get_from_hyp' Hr)]. *)


  (* solve_all_r_corps Hr. *)

(* maybe useless :  I can use HProp-itude in Tm_Con_r *)
(*

Definition Ty_Con_r (Γp : Conp)  (Ap : Typ) (Aw : Tyw Γp Ap) Am (Amr : Ty_r Aw Am) : Con_r (Ty_Con_w Aw) Am.1.
- move:Aw Amr.
  destruct Ap; solve_all_r.
Defined.
  (*
  unshelve simple refine (
      match Ap with
        starp Γ => _
      | arp Γ A t u => _
      end); simpl => Aw Ar.
  + set e := (e in e^); destruct e; cbn.
    apply:(transport (fun z => Con_r _ z.1) _^); get_from_hyp' Ar.
  +set e := (e in e^); destruct e; cbn.
   apply:(transport (fun z => Con_r _ z) _^); last by get_from_hyp' Ar.
   by repeat try_rewrite Ar => /=.
*)

Definition Tm_Con_r (Γp : Conp)  (Ap : Typ) (tp : Tmp) (tw : Tmw Γp Ap tp) tm (tmr : Tm_r tw tm) :
   Con_r (Tm_Con_w tw) tm.1.1.
- move:tw tmr.
  destruct tp; last by intro; apply:Empty_rect.
  all:solve_all_r.
Defined.

Definition Var_Con_r (Γp : Conp)  (Ap : Typ) (xp : Varp) (xw : Varw Γp Ap xp) xm (xmr : Var_r xw xm) :
   Con_r (Var_Con_w xw) xm.1.1.
- move:xw xmr.
   destruct xp => /=.
  + move => xw hr.
    destruct (_^).
    simpl.
    repeat (try_rewrite hr => /=).
    unshelve eexists;  first by eexists; get_from_hyp' hr.
    unshelve eexists;  first by eexists; get_from_hyp' hr.
    simpl.
    by split;repeat try_rewrite hr.
  + move => xw hr.
    destruct (_^) => /=.
    unshelve eexists;  first by eexists; get_from_hyp' hr.
    unshelve eexists;  first by eexists; get_from_hyp' hr.
    simpls.
    repeat try_rewrite hr.
    simpl.
    set e := (e in e^).
    split; last first.
    * by destruct (e^).
    * simpl.
      rewrite -e.
      by repeat try_rewrite hr.
Defined.
*)
(* Tactic Notation "test_tac" constr(x) := *)
(*   Ltac test_tac x := *)
(*   eapply  ((fun a => a) x). *)
(*   (* apply z. *) *)

(* Ltac solve_all_r_gen' x := *)
(*   simpl;intros Hw Hr; *)
(*   (* repeat (destruct_eqs Hw); *) *)
(*   repeat (destruct_eqs Hw); *)
(*   cbn; *)


(* apply:(transport (x _) _^) ; *)
(*   [ by repeat try_rewrite Hr => /= | ] ; *)
(*   eapply   (transport (fun z => x z _) (path_ishprop _ _)); *)
(*   get_from_hyp' Hr. *)

(* Ltac test_again x := *)
(* eapply (transport (x _ _ _) (_ ^)) . *)

Definition Ty_Con_r (Γp : Conp) (Γw: Conw Γp) (Ap : Typ) (Aw : Tyw Γp Ap) Am (Amr : Ty_r Aw Am) : Con_r Γw Am.1.
- move:Aw Amr.
  (* test_tac (fun (A : Type) (y : A) => y). *)
  (* constr:(idmap). *)
  destruct Ap; solve_all_r.
  (* simpl;intros Hw Hr; *)
  (* (* repeat (destruct_eqs Hw); *) *)
  (* repeat (destruct_eqs Hw); *)
  (* cbn. *)
  (* test_again (@Con_r _ _). *)
Defined.
  (*
  unshelve simple refine (
      match Ap with
        starp Γ => _
      | arp Γ A t u => _
      end); simpl => Aw Ar.
  + set e := (e in e^); destruct e; cbn.
    apply:(transport (fun z => Con_r _ z.1) _^); get_from_hyp' Ar.
  +set e := (e in e^); destruct e; cbn.
   apply:(transport (fun z => Con_r _ z) _^); last by get_from_hyp' Ar.
   by repeat try_rewrite Ar => /=.
*)

Definition Tm_Con_r (Γp : Conp) (Γw : Conw Γp) (Ap : Typ) (tp : Tmp) (tw : Tmw Γp Ap tp) tm (tmr : Tm_r tw tm) :
   Con_r Γw tm.1.1.
- move:tw tmr.
  destruct tp; last by intro; apply:Empty_rect.
  all:solve_all_r.
Defined.

Ltac case_by_eq  :=
  match goal with
    h : ?x.1 = _ |- _ =>
    let t := find_orig_tm x in
    destruct t
  | h : ?x.2 = _ |- _ =>
    let t:=  find_orig_tm x in destruct t
  | h : Σ _, _ = _ |- _ => destruct h
  end.
Ltac case_by_eq_end := repeat (case_by_eq ; simpl in * ; subst ;simpl in * ).
Ltac better_recursive_destruct_sigma :=
  repeat (refine (sigT_rect' _); simpl; intro); intros; case_by_eq_end.

Fixpoint Var_Con_r (Γp : Conp) (Γw : Conw Γp) (Ap : Typ) (xp : Varp) (xw : Varw Γp Ap xp) xm (xmr : Var_r xw xm) {struct xp} :
   Con_r Γw xm.1.1.
- move:xw xmr.
   destruct xp => /=.
  +
    (* solve_all_r_gen. *)
    move => xw hr.
    repeat (destruct_eqs xw).
    simpl.
    repeat (try_rewrite hr => /=).
    simpl in hr.
    unshelve eexists ; first by eexists; replace_hp; get_from_hyp' hr.
    unshelve eexists ; first by eexists; replace_hp; get_from_hyp' hr.
    (* unshelve eexists ; first by eexists; eapply (transport (fun z => _ z _) (path_ishprop _ _)); get_from_hyp' hr. *)
    (* unshelve eexists ; first by eexists; eapply (transport (fun z => _ z _) (path_ishprop _ _)); get_from_hyp' hr. *)
    simpl.
    by split;repeat try_rewrite hr.
  + move => xw .
    repeat (destruct_eqs xw).
    better_recursive_destruct_sigma.

    unshelve eexists ; first by eexists; replace_hp; sigma_eassumption.
    simpl.
    refine ((_ ; _) ; eq_refl ; eq_refl) => /=.
    apply:Var_Con_r.
    refine (_.2).
Defined.


Definition Sub_Con2_r Γp Δp (Δw : Conw Δp) σp (σw: Subw Γp Δp σp) σm (σmr : Sub_r σw σm) :
  Con_r Δw σm.2.1.
  - move :σw σmr.
    destruct σp =>//=.
    + intros.
      repeat destruct_eqs σw.
      by repeat try_rewrite σmr.
    + simpl;intros Hw Hr;
        repeat (destruct_eqs Hw);
        simpl.
      move:Hr.
      (* repeat (refine (sigT_rect' _); simpl; intro); intros. *)
      (* subst. *)
      better_recursive_destruct_sigma.
      simpl in *.
      (* repeat try_rewrite Hr=> /=. *)
      unshelve eexists ; first by eexists ; replace_hp; sigma_eassumption.
      simpl.
      refine ((_ ; _) ; eq_refl ; eq_refl) => /=.
      apply :Ty_Con_r.
      refine (_.2).
Defined.
Fixpoint Sub_Con1_r Γp Δp (Γw : Conw Γp) σp (σw: Subw Γp Δp σp) σm (σmr : Sub_r σw σm) {struct σp} :
  Con_r Γw σm.1.
  - move :σw σmr.
    destruct σp =>//=; first by solve_all_r.
    + intro σw.
      intro hr.
      unshelve erewrite (_ : σm.1 = _); try get_from_hyp' hr; last first.
      * repeat destruct_eqs σw.
       apply:Sub_Con1_r.
        get_from_hyp' hr.
      * by repeat try_rewrite hr.
Defined.

Fixpoint subTy_r  (Γp Δp : Conp) σp (σw  : Subw Γp Δp σp)
         Γm Δm σm 
         (σcmr : Sub_r σw (Γm ; Δm ; σm))
           (Ap : Typ)  (Aw : Tyw Δp Ap )(Awσ : Tyw Γp (subTyp Γp σp Ap)) (Am : Tym Δm)
           (Amr : Ty_r Aw (Δm ; Am))
           {struct Ap} :
  Ty_r Awσ (Γm; subTym σm Am).
Admitted.

Fixpoint wkTy_r(Γp : Conp) (Exp : Typ)(Exw : Tyw Γp Exp)
         (Γm : Conm) (Γmr : Con_r (Ty_Con_w Exw) Γm)
         (Exm : Tym Γm) (Exmr : Ty_r Exw (_ ; Exm))

         (Ap : Typ) (Aw : Tyw Γp Ap)(wkAw: Tyw (Γp ▷ Exp) (wkTyp Exp Ap))
           Am (Amr : Ty_r Aw (Γm ; Am))
           {struct Ap}
  : Ty_r wkAw (_ ; wkTym Exm Am ).
Admitted.

Definition Tm_Ty_r (Γp : Conp)  (Ap : Typ) (Aw : Tyw Γp Ap) (tp : Tmp) (tw : Tmw Γp Ap tp) tm (tmr : Tm_r tw tm) :
   Ty_r Aw tm.1.
- move:tw tmr.
  destruct tp; last by intro; apply:Empty_rect.
  + solve_all_r.
  + move => /= tw.
    repeat destruct_eqs tw.
    better_recursive_destruct_sigma.
    apply:subTy_r; eassumption.
Defined.

Ltac realevar x :=
  let T := fresh in
  let xx := fresh x in
  evar (T : Type); evar (xx : T).
Fixpoint Var_Ty_r (Γp : Conp)  (Ap : Typ) (Aw : Tyw Γp Ap) (xp : Varp) (xw : Varw Γp Ap xp) xm (xmr : Var_r xw xm) {struct xp} :
   Ty_r Aw xm.1.
- move:xw xmr.
  destruct xp.
  + move => /= xw.
    repeat destruct_eqs xw.
    better_recursive_destruct_sigma.
    apply:wkTy_r.
    * apply:(Ty_Con_r _ (Am := (_ ; _))); eassumption.
    * eassumption.
    * eassumption.
  + move => /= xw.
    repeat destruct_eqs xw.
    better_recursive_destruct_sigma.
    apply:wkTy_r.
    * eapply( Ty_Con_r _ (Am := (x.1.1.1 ; pr1))).  eassumption.
    * eassumption.
    * apply:Var_Ty_r.
      refine (_.2).
      Unshelve.
      get_from_hyp xw.
Defined.

Definition isCTy_Ty_r Γp Γc (Ap : Typ) (Aw: Tyw Γp Ap)Ac (Acw : isCTyw Γp Γc Ap Ac) Amc (Amcr : isCTy_r Acw Amc) :
  Ty_r Aw (_ ; Amc.2.1).
  move:Acw Amcr.
  destruct Ac.
  + move => //= Hw Hr.
    unshelve erewrite (_ : Amc = _);[|get_from_hyp' Hr|].
    repeat destruct_eqs Hw => //=.
    unshelve eexists; [exists Hr.1.1.1|] => /=.
    (* isContr_Con_r *)
    * apply myadmit.
    * reflexivity.
  + move => /= hw Hr.
    unshelve erewrite (_ : Amc = _);[|get_from_hyp' Hr|] => /=.
    repeat destruct_eqs hw => /=.
    simpl in Hr.
    (* isCTm_Tm_r
isCTy_Ty_r
     *)
Admitted.

Definition isCVar_isContr_r  Γp Γc (Γcw : isContrw Γp Γc) (Ap : Typ) Ac xp xc  (xcw : isCVarw Γp Γc Ap Ac xp xc) xmc (xmcr : isCVar_r xcw xmc) :
  isContr_r Γcw xmc.1.1.
  - move:xcw xmcr.
    destruct xc => /= hw; repeat destruct_eqs hw.
    {by move => -> //=. }
    all: better_recursive_destruct_sigma;
      (unshelve eexists; first by eexists; replace_hp; sigma_eassumption); simpl in *; subst; simpl in *;
        reflexivity.
Defined.

Definition isCTm_isContr_r  Γp Γc (Γcw : isContrw Γp Γc) (Ap : Typ) Ac tp tc  (tcw : isCTmw Γp Γc Ap Ac tp tc) tmc (tmcr : isCTm_r tcw tmc)  :
  isContr_r Γcw tmc.1.1.
    -
  move:tcw tmcr.
  destruct tc; move => /= hw;
   repeat destruct_eqs hw => /=;
  better_recursive_destruct_sigma; subst.
  + apply:isCVar_isContr_r.
    apply pr2.
  + replace_hp; sigma_eassumption.
  + by apply:Empty_rect.
Defined.
Definition isCTy_isContr_r  Γp Γc (Ap : Typ) Ac (Acw : isCTyw Γp Γc Ap Ac) (Γcw : isContrw Γp Γc)Amc (Amcr : isCTy_r Acw Amc) :
  isContr_r Γcw Amc.1.
  move:Acw Amcr.
  destruct Ac.
  + simpl.
    unshelve solve_all_r_gen.
  + unshelve solve_all_r_gen ; first by assumption.
    eapply isCTm_isContr_r.
      apply pr2.
Defined.

Definition isCTy_isContrp (Ac : isCTyp) : isContrp.
by destruct Ac => //=.
Defined.



Definition isCSub_isContr2p (σc : isCSubp) : isContrp :=
  match σc with
    isC_to_astarp _ _ _ _ => isC_astarp
  | isC_to_consconsp _ _ Δp Δc A Ac u uc σ σc t tc f fc =>
    isC_consconsp Δp Δc A Ac u uc
  end.


Definition isCSub_isContr2_r  Γp Γc Δp Δc σp σc (σcw : isCSubw Γp Γc Δp Δc σp σc) (Δcw : isContrw Δp Δc)σmc (σmcr : isCSub_r σcw σmc) : isContr_r Δcw σmc.2.1.
  move:σcw σmcr.
  destruct σc.
  + move => /= hw Hr.
    repeat destruct_eqs hw => /=.
    simpl in Hr.
    move:Hr.
    by better_recursive_destruct_sigma.

  +  move => /= hw.
     repeat destruct_eqs hw => /=.
     better_recursive_destruct_sigma.
     unshelve eexists; first by eexists; replace_hp; sigma_eassumption.
     simpl.
     reflexivity.
Defined.
Definition isCSub_isContr1_r  Γp Γc Δp Δc σp σc (σcw : isCSubw Γp Γc Δp Δc σp σc) (Γcw : isContrw Γp Γc)σmc (σmcr : isCSub_r σcw σmc) : isContr_r Γcw σmc.1.
  move:σcw σmcr.
  destruct σc.
  + move => /= hw Hr.
    repeat destruct_eqs hw => /=.
    simpl in Hr.
    move:Hr.
    better_recursive_destruct_sigma; subst.
    apply:isCTm_isContr_r.
    refine _.2.

  +  move => /= hw.
     repeat destruct_eqs hw => /=.
     better_recursive_destruct_sigma.
     replace_hp.
     eapply isCTm_isContr_r in pr3.
     exact:pr3.
     Unshelve.
     get_from_hyp hw.
Defined.

Ltac realeexists x :=
  let xx := fresh x in
  (* let T := fresh x in *)
  refine (let xx := _ in (xx; _)).
Fixpoint wkisCTy_r(Γp : Conp) Γc (Γw :isContrw Γp Γc)(Exp : Typ)Exc(Exw : isCTyw Γp Γc Exp Exc) ux uxc
         (uxw : isCTmw Γp Γc Exp Exc ux uxc)
         Γm  (Γmr : isContr_r Γw Γm)
         Exm  (Exmr : isCTy_r Exw (_ ; Exm))
         uxcm (uxcmr : isCTm_r uxw ((Γm ; Exm) ; uxcm))

         (Ap : Typ) Ac (Aw : isCTyw Γp Γc Ap Ac)(wkAw: isCTyw (consconsp Γp Exp ux)
                                                              (isC_consconsp Γp Γc Exp Exc ux uxc)
                                                              (wkwkTyp Γp Exp ux Ap)
                                                              (wkisCTyp Exp Exc ux uxc Ac))
           Amc (Amr : isCTy_r Aw (Γm ; Amc))
           {struct Ac}
  : isCTy_r wkAw ((_ ; isC_consconsm uxcm.2) ; _ ; isCwkwkTym uxcm.2 Amc.2 )
    with 
wkisCTm_r(Γp : Conp) Γc (Γw :isContrw Γp Γc)(Exp : Typ)Exc(Exw : isCTyw Γp Γc Exp Exc) ux uxc
         (uxw : isCTmw Γp Γc Exp Exc ux uxc)
         Γm  (Γmr : isContr_r Γw Γm)
         Exm  (Exmr : isCTy_r Exw (_ ; Exm))
         uxcm (uxcmr : isCTm_r uxw ((Γm ; Exm) ; uxcm))

         (Ap : Typ) Ac tp tc
         (*
         (Aw : isCTyw Γp Γc Ap Ac)(wkAw: isCTyw (consconsp Γp Exp ux)
                                                              (isC_consconsp Γp Γc Exp Exc ux uxc)
                                                              (wkwkTyp Γp Exp ux Ap)
                                                              (wkisCTyp Exp Exc ux uxc Ac))
*)
         (tw : isCTmw Γp Γc Ap Ac tp tc)(wktw: isCTmw (consconsp Γp Exp ux)
                                                              (isC_consconsp Γp Γc Exp Exc ux uxc)
                                                              (wkwkTyp Γp Exp ux Ap)
                                                              (wkisCTyp Exp Exc ux uxc Ac)
                                                              (wkwkTmp Γp Exp ux tp)
                                                              (wkisCTmp Exp Exc ux uxc tc)
                                        )
           Am tmc (tmr : isCTm_r tw ((Γm ; Am) ; tmc))
           {struct tc}
  : isCTm_r wktw (((_ ; isC_consconsm uxcm.2) ; _ ; isCwkwkTym uxcm.2 Am.2) ; _ ; isCwkwkTmm uxcm.2 tmc.2 ).
Admitted.
Fixpoint isCVar_isCTy_r  Γp Γc  (Ap : Typ) Ac (Acw : isCTyw Γp Γc Ap Ac) xp xc  (xcw : isCVarw Γp Γc Ap Ac xp xc) xmc (xmcr : isCVar_r xcw xmc) {struct xc} :
  isCTy_r Acw xmc.1
    with
isCTm_isCTy_r  Γp Γc  (Ap : Typ) Ac (Acw : isCTyw Γp Γc Ap Ac) tp tc  (tcw : isCTmw Γp Γc Ap Ac tp tc) tmc (tmcr : isCTm_r tcw tmc) {struct tc} :
  isCTy_r Acw tmc.1.
  - move: xcw xmcr.
    destruct xc => hw; simpl in hw.
    + 
      repeat destruct_eqs hw.
      simpl.
      better_recursive_destruct_sigma.
      subst.
      unshelve eexists; first by eexists; reflexivity.
      reflexivity.
    + repeat destruct_eqs hw => /=; better_recursive_destruct_sigma; subst.
      simpl.
      (* set xcm := (x in isC_vm x). *)
      (* set Gm := consm _. *)
      (* TODO : trouver une meilleure façon de faire ceci
         je mets des '_' jusqu'à ce que dans le but final, on ait des ?Goal5 directement
         et  pas des ?Goal.1 ou .2, ce qui permet par réflexivité de déterminer ces evars 
       *)
      unshelve realeexists tmcr.
      {
        refine (_ ; _ ; eq_refl).
        refine (_ ; _ ; eq_refl).
        eexists.
        replace_hp.
        exact x.2.
      }
      simpl in *.
      unshelve realeexists umcr.

{

  eexists.
  unshelve (apply:wkisCTm_r; last first; try (clear tmcr; sigma_eassumption)).
  all:try get_from_hyp hw.
  all: try sigma_eassumption.
  apply:isCTm_isCTy_r.
  refine _.2.
  apply:isCTm_isContr_r.
  refine _.2.
}
simpl.
refine ((_ ; eq_refl) ; eq_refl).
    + repeat destruct_eqs hw => /=; better_recursive_destruct_sigma; subst => /=.
      apply:wkisCTy_r; try (apply :isCTm_isContr_r || apply:isCTm_isCTy_r) ; apply:pr2.
    + repeat destruct_eqs hw => /=; better_recursive_destruct_sigma; subst => /=.
      apply:wkisCTy_r; try (apply :isCTm_isContr_r || apply:isCTm_isCTy_r); try apply:pr2.
      apply:(transport (fun x => isCTy_r _ x)).
      apply:pr1_path'; sigma_eassumption.
      apply:isCVar_isCTy_r.
      refine (_.2).
      Unshelve.
      all:intros;try get_from_hyp hw.


  - move: tcw tmcr.
    destruct tc => /= tw.
    + repeat destruct_eqs tw.
      better_recursive_destruct_sigma; subst => /=.
      apply:isCVar_isCTy_r.
      sigma_eassumption.
    + repeat destruct_eqs tw.
      better_recursive_destruct_sigma; subst => /=.
      apply:subisCTyr;sigma_eassumption.
      + by apply:Empty_rect.
        (* COq is too slow : TODO : explicit more the relation to prevent the fixpoint *)
Admitted.

(* the order is important : If I put Ty_Con_r before Tm_Con_r it fails because it
applies Ty_Con_r when Tm_Con_r should be applied
 *)
Definition isContr_Con_r Γp Γc  (Γw: Conw Γp) (Γcw : isContrw Γp Γc) Γmc (Γmcr : isContr_r Γcw Γmc) :
  Con_r Γw Γmc.1.
  Admitted.

Definition path_isCTy_r (Γp : Conp) Γc Ap Ac  (Aw : isCTyw Γp Γc Ap Ac)
           Am Am' (Ar : isCTy_r Aw Am)(Ar' : isCTy_r Aw Am') : Am = Am'.
  eassert (h := path_ishprop  (Am ; Ar) (_ ; _)).
  eapply  (pr1_path h).
  Unshelve.
  apply:isCTy_r_hp.
  assumption.
  (* replace_hp;  eassumption. *)
Defined.
 (* TODO : tester avec un seul Aw au lieu de deux Aw' *)
(*
Definition path_isCTy_r (Γp : Conp) Ap Ac  (Aw Aw' : isCTyw Γp Ap Ac)
           Am Am' (Ar : isCTy_r Aw Am)(Ar' : isCTy_r Aw' Am') : Am = Am'.
  eassert (h := path_ishprop  (Am ; Ar) (_ ; _)).
  eapply  (pr1_path h).
  Unshelve.
  apply:isCTy_r_hp.
  replace_hp;  eassumption.
Defined.
*)
Definition path_isCTm_r (Γp : Conp) Γc Ap Ac tp tc  (tw  : isCTmw Γp Γc Ap Ac tp tc)
           tm tm' (tr : isCTm_r tw tm)(tr' : isCTm_r tw tm') : tm = tm'.
  eassert (h := path_ishprop  (tm ; tr) (_ ; _)).
  eapply  (pr1_path h).
  Unshelve.
  apply:isCTm_r_hp.
  assumption.
  (* replace_hp;  eassumption. *)
Defined.

Hint Resolve Tm_Con_r : same_r.
Hint Resolve Var_Con_r : same_r.
Hint Resolve Ty_Con_r : same_r.
Hint Resolve Sub_Con2_r : same_r.
Hint Resolve Sub_Con1_r : same_r.
Hint Resolve isContr_Con_r : same_r.
Hint Resolve isCTm_isContr_r : same_r.
Hint Resolve isCVar_isContr_r : same_r.
Hint Resolve isCTy_isContr_r : same_r.
Hint Resolve isCSub_isContr1_r : same_r.
Hint Resolve isCSub_isContr2_r : same_r.
Hint Resolve Tm_Ty_r : same_r.
Hint Resolve Var_Ty_r : same_r.
Hint Resolve isCTy_Ty_r : same_r.
Hint Resolve isCTm_isCTy_r : same_r.
Hint Extern 0 => by apply:pr2 : same_r.

Hint Resolve path_Ty_r path_isCTy_r path_isContr_r path_Con_r path_isCTm_r : same_r.




Fixpoint Con_r_part (Γp : Conp ) (Γw : Conw Γp)  {struct Γp} :
   sigT ( Con_r Γw  )
with Ty_r_part (Γp : Conp)(Γw : Conw Γp)(Ap : Typ)(Aw : Tyw Γp Ap)
               Γm (Γmr : Con_r Γw Γm )
               {struct Ap} :
        (sigT (fun Am => Ty_r Aw (Γm ; Am) ))
  with Tm_r_part  (Γp : Conp)
       (Ap : Typ)(Aw : Tyw Γp Ap)
       (tp : Tmp) (tw : Tmw Γp Ap tp)
       ΓAm (ΓAmr : Ty_r Aw ΓAm)
       {struct tp} :
        (sigT (fun tm => Tm_r tw (ΓAm ; tm) ))  
  with Var_r_part  (Γp : Conp)
       (Ap : Typ)(Aw : Tyw Γp Ap)
       (xp : Varp) (xw : Varw Γp Ap xp)
       ΓAm (ΓAmr : Ty_r Aw ΓAm)
       {struct xp} :
        (sigT (fun xm => Var_r xw (ΓAm ; xm) ))  .
  Abort.

  (*
  with Var_r_part  (Γp : Conp)(Ap : Typ)(xp : Varp) (xw : Varw Γp Ap xp){struct xp}
       :  (sigT ( Var_r xw )) 
  with Sub_r_part  (Γp Δp : Conp)(σp : Subp) (σw : Subw Γp Δp σp){struct σp}
       :  (sigT ( Sub_r σw )) 
  with isContr_r_part (Γp : Conp) (Γc : isContrp) (Γcw : isContrw Γp Γc){struct Γc}
       :  (sigT ( isContr_r Γcw )) 
  with isCTy_r_part (Γp : Conp) Γc (Ap : Typ) Ac (Aw : isCTyw Γp Γc Ap Ac){struct Ac}
       :  (sigT ( isCTy_r Aw )) 
  with isCTm_r_part (Γp : Conp) Γc (Ap : Typ)Ac (tp : Tmp) tc (tcw : isCTmw Γp Γc Ap Ac tp tc){struct tc}
       :  (sigT ( isCTm_r tcw )) 
  with isCVar_r_part (Γp : Conp) Γc (Ap : Typ)Ac (xp : Varp) xc (xcw : isCVarw Γp Γc Ap Ac xp xc){struct xc}
       :  (sigT ( isCVar_r xcw )) 
  with isCSub_r_part  (Γp : Conp) Γc (Δp : Conp) Δc(σp : Subp ) σc (σcw : isCSubw Γp Γc Δp Δc σp σc){struct σc}
       :  (sigT ( isCSub_r σcw )) .
*)

Definition Ty_r_part (Γp : Conp)(Γw : Conw Γp)(Ap : Typ)(Aw : Tyw Γp Ap)
               Γm (Γmr : Con_r Γw Γm ) 
               (Amr : sigT (Ty_r Aw))
                : 
        (sigT (fun Am => Ty_r Aw (Γm ; Am) )).
Proof.
  simpl.
  pattern Γm.
  apply:transport; last by eexists; exact Amr.2.
  unshelve eauto with same_r.
   assumption.
Defined.
Definition isCSub_r_part (Γp : Conp) Γc (Δp : Conp) Δc(σp : Subp ) σc (σcw : isCSubw Γp Γc Δp Δc σp σc)
          (Γcw : isContrw Γp Γc)
          (Δcw : isContrw Δp Δc)
          Γm Δm (Γr : isContr_r  Γcw Γm) (Δr : isContr_r  Δcw Δm)
          (σmr : sigT (isCSub_r σcw))
  :
  sigT (fun σm => isCSub_r σcw (Γm ; Δm ; σm)).
Proof.
  simpl.
  pattern Γm.
  apply:transport; last first.
  {
  pattern Δm.
  apply:transport; last first.
  - eexists. exact: σmr.2.
  - unshelve eauto with same_r; assumption.
  }
   unshelve eauto with same_r; assumption.
Defined.


Lemma pr2_path' (A : Type) (hsA : IsHSet A) (P : A -> Type)
      (u : A) (u' : P u) (v' : P u): (u; u') = (u; v') -> u' = v'.
Proof.
  intro h.
  assert (h' := pr2_path h).
  etransitivity; last by exact h'.
  simpl.
  unshelve erewrite  (_ : h..1 = eq_refl) => //=.
  apply path_ishprop.
Defined.

Fixpoint Con_r_total (Γp : Conp ) (Γw : Conw Γp)  {struct Γp} :
   sigT ( Con_r Γw  )
with Ty_r_total (Γp : Conp)(Ap : Typ) (Aw : Tyw Γp Ap) {struct Ap} :
        (sigT ( Ty_r  Aw ))
with Tm_r_total  (Γp : Conp)(Ap : Typ)(tp : Tmp) (tw : Tmw Γp Ap tp) {struct tp} :
        (sigT ( Tm_r tw ))  
  with Var_r_total  (Γp : Conp)(Ap : Typ)(xp : Varp) (xw : Varw Γp Ap xp){struct xp}
       :  (sigT ( Var_r xw )) 
  with Sub_r_total  (Γp Δp : Conp)(σp : Subp) (σw : Subw Γp Δp σp){struct σp}
       :  (sigT ( Sub_r σw )) 
  with isContr_r_total (Γp : Conp) (Γc : isContrp) (Γcw : isContrw Γp Γc){struct Γc}
       :  (sigT ( isContr_r Γcw )) 
  with isCTy_r_total (Γp : Conp) Γc (Ap : Typ) Ac (Aw : isCTyw Γp Γc Ap Ac){struct Ac}
       :  (sigT ( isCTy_r Aw )) 
  with isCTm_r_total (Γp : Conp) Γc (Ap : Typ)Ac (tp : Tmp) tc (tcw : isCTmw Γp Γc Ap Ac tp tc){struct tc}
       :  (sigT ( isCTm_r tcw )) 
  with isCVar_r_total (Γp : Conp) Γc (Ap : Typ)Ac (xp : Varp) xc (xcw : isCVarw Γp Γc Ap Ac xp xc){struct xc}
       :  (sigT ( isCVar_r xcw )) 
  with isCSub_r_total  (Γp : Conp) Γc (Δp : Conp) Δc(σp : Subp ) σc (σcw : isCSubw Γp Γc Δp Δc σp σc){struct σc}
       :  (sigT ( isCSub_r σcw )) .
  Focus 10.
  {
- move:σcw; destruct σc as [|Γ Γc' Δ Δc' A Ac u uc σ σc t tc f fc] => /= hw.
  + eexists; repeat (unshelve refine (let x := _ in (x ; _)); first by (easy || ( unshelve eauto with same_r; try get_from_hyp hw))).
    unshelve eexists.
    {
      eexists.
      unshelve eapply path_sigma  ; simpl; last by reflexivity.
      eapply (pr2_path' _  (P := fun z => Σ Tm : Tym z.1, isCTym z.2 Tm)(u := x.1.1.1)).
      
      apply:path_isCTy_r.
      - apply:isCTm_isCTy_r.
        apply pr2.
      - simpl.
        refine ((_ ; _) ; eq_refl).
        apply :isCTm_isContr_r; apply pr2.
    }
    unshelve reflexivity.
  + repeat destruct_eqs hw => /=.
    eexists.
    (* unshelve refine ((_ ; _ ; _ ; _ ; _ ; (_ ; _ ;  _ ; eq_refl))); last first. *)
    unshelve realeexists umcr; first by easy.
    unshelve realeexists σmcr; first by easy.
    unshelve realeexists tmcr; first by easy.
    unshelve realeexists fmcr; first by easy.
    (* clearbody umcr σmcr tmcr fmcr. *)

    unshelve realeexists σmeq; last first.
    unshelve realeexists tmeq; last first.
    unshelve realeexists fmeq; last first.
    subst σmeq tmeq fmeq.
    reflexivity.
    Ltac exists_sigma_mod_hp :=
              unshelve eexists; first by
        eexists;
        replace_hp;
        sigma_eassumption.
    all:try clearbody umcr σmcr tmcr fmcr.

    {
      clearbody σmeq tmeq.
      case_by_eq_end.
      (* or just apply:path_isCTm_r ?? *)
      eexists.
      unshelve eapply path_sigma  ; simpl; last by reflexivity.

      apply:path_isCTy_r.
      * apply: isCTm_isCTy_r.
        apply pr2.
      * simpl.
        exists_sigma_mod_hp.
        simpl.
              unshelve eexists.
        eexists.
         { unshelve apply :subisCTmr; try get_from_hyp hw; try sigma_eassumption. }
         simpl.
         refine ((_ ; eq_refl) ; eq_refl).
    }
    {
      clearbody σmeq.
      case_by_eq_end.
      eexists.
      unshelve eapply path_sigma  ; simpl; last by reflexivity.
      simpl.
      apply:path_isCTy_r.
      * apply: isCTm_isCTy_r.
        apply pr2.
      *  unshelve apply :subisCTyr; try get_from_hyp hw; try sigma_eassumption.
          apply:isCTm_isCTy_r; apply pr2.
    }
    {
      eexists.
      unshelve eapply path_sigma  ; simpl; last by reflexivity.
      eauto with same_r.
    }
  }
  Unfocus.
- move:Γw.
  unshelve refine (match Γp with
            nilp => fun Gw => (nilm ; _ )
          | consp Γp Ap => fun Gw =>
                            (consm (Ty_r_total Γp Ap _).1.2; _)

                   end
                  ); cbn in Gw; try get_from_hyp  Gw; simpl.
  all: repeat (unshelve eexists; first by (easy || ( unshelve eauto with same_r; get_from_hyp Gw))); reflexivity.
- move:Aw; destruct Ap => /= Aw;eexists.
  all: repeat (unshelve eexists; first by (easy || ( unshelve eauto with same_r; get_from_hyp Aw))); reflexivity.
- move:tw; destruct tp => /= tw ; last by apply:Empty_rect.
  all:eexists; repeat (unshelve eexists; first by (easy || ( unshelve eauto with same_r; get_from_hyp tw))) ; try reflexivity.
- move:xw; destruct xp => /= hw.
  all:eexists; repeat (unshelve eexists; first by (easy || ( unshelve eauto with same_r; get_from_hyp hw))); try reflexivity.
  repeat destruct_eqs hw.
  unshelve (eexists; last by reflexivity).
  eexists.
  (* TODO généraliser cette preuve *)
  unshelve eapply  path_sigma; simpl; last by reflexivity.
  {
    simpl.
    eauto with same_r.
    }
- move:σw; destruct σp => /= hw.
  all:eexists; repeat (unshelve eexists; first by (easy || ( unshelve eauto with same_r; get_from_hyp hw))).
  + reflexivity.
  + 
    unshelve realeexists σmp; last first.
    unshelve realeexists tmp; last first.
    reflexivity.
    {
      clearbody σmp.
      case_by_eq_end.
      eexists.
      unshelve eapply path_sigma ; simpl; last by reflexivity.
      {
        (* set x := (x in x = _). *)
        eapply  pr2_path'.
        refine _.
        
        apply:path_Ty_r.
        +  solve_Ty_r; apply pr2.
        +  apply:subTy_r; last by apply pr2.
           eassumption.
        
        }
    }
    {
      eexists.
      unshelve eapply path_sigma ; simpl.
      {
        (* there should not be unshelved goals here.. *)
        (* TODO: eauto with same_r does not induce hidden goals *)
        unshelve eauto with same_r.
        all:try get_from_hyp hw.
        shelve .
      }
      {
        unshelve eapply path_sigma ; simpl; last by reflexivity.
        simpl.
        apply:path_Con_r; last by solve_Con_r; apply pr2.
        simpl.
        destruct (path_Con_r _ _).
        solve_Con_r ;apply pr2.
      }
    }
    

- move:Γcw; destruct Γc => /= hw.
  all:eexists; repeat (unshelve eexists; first by (easy || ( unshelve eauto with same_r; get_from_hyp hw))); reflexivity.
- move:Aw; destruct Ac => /= hw.
  all:eexists; repeat (unshelve eexists; first by (easy || ( unshelve eauto with same_r; try get_from_hyp hw)));try reflexivity.
  unshelve eexists; last by reflexivity.
  (* TODO généraliser cette preuve *)
  eexists.
  unshelve eapply  path_sigma; simpl; last by reflexivity.
  {
    simpl.
    eauto with same_r.
    }

- move:tcw; destruct tc => /= hw.
  all:eexists; repeat (unshelve eexists; first by (easy || ( unshelve eauto with same_r; try get_from_hyp hw))); try reflexivity.
  unshelve eexists; last by reflexivity.
  (* TODO généraliser cette preuve *)
  eexists.
  unshelve eapply  path_sigma.
  {
    simpl.
    eauto with same_r.
    }
  unshelve eapply  path_sigma.
  {
    simpl.
    apply :path_isContr_r; last by solve_isContr_r; apply pr2.
    simpl.
    destruct (path_isContr_r  _ _) => /=.
    solve_isContr_r; apply pr2.
  }
  simpl.
  reflexivity.
  by apply:Empty_rect.
  by apply:Empty_rect.
- move:xcw; destruct xc => /= hw.
  all:eexists; repeat (unshelve eexists; first by (easy || ( unshelve eauto with same_r; try get_from_hyp hw))); try reflexivity.
  simpl.
  unshelve eexists; last by reflexivity.
  (* TODO généraliser cette preuve *)
  eexists.
  eexists.
  unshelve eapply  path_sigma; simpl.
  unshelve eapply  path_sigma; simpl; last by reflexivity.
  {
    unshelve eauto with same_r; get_from_hyp hw.
  }
  simpl.
  reflexivity.
Defined.