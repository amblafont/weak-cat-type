(* -*- coq-prog-name: "coqtop"; -*- *)

(* ici on n'utilise pas autosubst qui de toute manière ne marche pas pour
les types mutuellement inductifs *)
(* Je pack les interprétations dans un record pour la relation fonctionnelle *)
(* coqc -q -Q "WeakOmegaCat" WeakOmegaCat WeakOmegaCat/TypeSystem/libhomot.v *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* différences par rapport au papier :

Γ ⊢ B dans weakening des Tmes

Γ ⊢ dans la substitution du contexte vide

TODO :  remplacer la r_gle Γ,x:A ⊢ en prémisse par Γ ⊢ A

*)



Require Import EqdepFacts.
Require Import Coq.Logic.JMeq.
Require Import ssreflect ssrfun ssrbool .
From Modules Require Import libhomot lib brunerietype.
(* From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq. *)
Set Bullet Behavior "Strict Subproofs".




(* sinon je ne peux plus faire de ltac
*)
Ltac clear_hprop :=
  match goal with
  | x : WC ?C, x' : WC ?C |- _ =>
    destruct (WC_hp x x')
  | x : WTy ?C ?A, x' : WTy ?C ?A |- _ =>
    destruct (WTy_hp x x')
  | x : Wtm ?C ?A ?t, x' : Wtm ?C ?A ?t |- _ =>
    destruct (WTm_hp x x')
  | x : WVar ?C ?A ?t, x' : WVar ?C ?A ?t |- _ =>
    destruct (WVar_hp x x')
  | x : WS ?C ?A ?t, x' : WS ?C ?A ?t |- _ =>
    destruct (WS_hp x x')
  end.

(* Définir ce qu'est un type globulaire qui est un omega groupoide *)
(*
Record omega_groupoid :=
  mkGroup
    { s_C : forall {Γ : Con}  (wΓ : wC Γ) ,  Type ;
      s_T : forall {Γ : Con} {A : Ty} (wΓ : wC Γ) (wA : wTy Γ A), s_C wΓ -> Type;
      s_tm : forall {Γ : Con} {A : Ty}{ t : Tm} (wΓ : wC Γ) (wA : wTy Γ A) (wt : wtm Γ A t)
                (γ : s_C wΓ), s_T wA γ }.
*)

(* Require Import Coq.Logic.JMeq. *)

(* Notation "x ≅ y" := (eq_dep x y)  (at level 70). *)

Section OmegaGroupoid.
  Variable (T : Type).
  Hypothesis (fibT : Fib T).

(* en utilisant uip *)
(* Notation "x ≅ y :> P" := (eq_dep _ P _  x _ y) (at level 70, y at next level, no associativity). *)

Record rC :=
  mkRC { C_TY : Type ;
         C_fib : Fib C_TY;
         idA :  T -> C_TY;
         JA : forall (P : C_TY -> Type)
                (fibP : (forall (δ : C_TY), Fib (P δ)))
                (d : forall (a : T) , P(idA a))
                (δ :  C_TY ) , P δ ;
        JA_idA : forall (P : C_TY -> Type)
          ( fibP : forall (δ :  C_TY ) , Fib (P δ) )
          (d : forall (a : T) , P(idA a))
          (a : T) ,
          JA fibP d (idA a) = d a

       }.

Lemma rCeq (x y : rC)
      (e : C_TY x = C_TY y)
      (ef : C_fib x ≅ C_fib y )
      (* (eidA : forall(a:T), (idA x a ≅ idA y a)) *)
      (eidA :  (idA x  ≅ idA y ))
      (eJA : @JA x ≅ @JA y )
      (* (eJA : forall P P' fibP fibP' d d' δ δ', *)
      (*     P ≅ P' -> fibP ≅ fibP' -> d ≅ d' -> δ ≅ δ' -> *)
      (*     @JA x P fibP d δ ≅ @JA y P' fibP' d' δ') *)
  : x = y.
  destruct x,y; simpl in *.
  destruct e.
  have e: idA0 = idA1.
  {
    (* apply:funext => a. *)
    apply JMeq_eq.
    apply:eidA.
  }
  subst.
  clear e.
  have e: JA0 = JA1.
  {
    (* repeat (apply:funext ; intros). *)
    intros.
    apply JMeq_eq.
    now apply:eJA.
  }
  subst.
  clear e.
  have e: JA_idA0 = JA_idA1.
  {
    repeat (apply:funext ; intros).
    apply:uip.
  }
  now subst.
  Qed.



Record rT (Γ : rC) :=
  mkRTy { T_TY : C_TY Γ  -> Type;
          iA : forall (a : T) , T_TY (idA Γ a) ;
          T_fib : forall (γ : _) , Fib (T_TY γ)
        }.

Lemma rTeq (C C' : rC) (x : rT C) (y : rT C') :
  C = C' ->
  (forall γ γ', γ ≅ γ' -> T_TY x γ ≅ T_TY y γ') ->
    (forall a, iA x a ≅ iA y a)  ->
    (forall γ γ', γ ≅ γ' -> T_fib x γ ≅ T_fib y γ')
  -> x ≅ y.
(* Lemma rTeq (C C' : rC) (x : rT C) (y : rT C') : *)
(*   C = C' -> *)
(*   ( T_TY x  ≅ T_TY y ) -> *)
(*     ( iA x  ≅ iA y )  -> *)
(*     ( T_fib x  ≅ T_fib y )  *)
(*   -> x ≅ y. *)
  intros.
  subst.
  destruct x,y; simpl in *.
  have e : T_TY0 = T_TY1.
  {
    repeat (apply:funext ; intros).
    apply:JMeq_eq.
    auto.
  }
  subst.
  (* clear e. *)
  have e : iA0 = iA1.
  {
    repeat (apply:funext ; intros).
    apply:JMeq_eq.
    auto.
  }
  subst.
  (* clear e. *)
  have e : T_fib0 = T_fib1.
  {
    repeat (apply:funext ; intros).
    apply:JMeq_eq.
    auto.
  }
  subst.
  reflexivity.

Qed.

Record rS (Γ Δ : rC ) :=
  mkRS { S : C_TY Γ -> C_TY Δ;
         sb_idA : forall (a : T) , S (idA Γ a) = idA Δ a }.

Lemma rSeq (C C' D D' : rC) (x : rS C D) (y : rS C' D') :
  C = C' -> D = D' ->
  (forall γ γ', γ ≅ γ' -> S x γ ≅ S y γ') ->
   x ≅ y.
  intros.
  subst.
  destruct x,y; simpl in *.
  have e : S0 = S1.
  {
    repeat (apply:funext ; intros).
    apply:JMeq_eq.
    auto.
  }
  subst.
  have e : sb_idA0 = sb_idA1.
  {
    repeat (apply:funext ; intros).
    apply:uip.
  }
  subst.
  reflexivity.
Qed.


Record rtm {Γ : rC} (A : rT Γ) :=
  mkRt { t_t : forall (γ : _) , T_TY A γ;
         eq_iA : forall (a : T) , t_t (idA Γ a) = iA A a }.

Lemma rtmeq (C C' : rC) (A : rT C) (A' : rT C') (x : rtm A) (y : rtm A') :
      ( C = C') -> (A ≅ A') -> (forall γ γ', γ ≅ γ' -> t_t x γ ≅ t_t y γ') -> x ≅ y.
  intros.
  subst.
  destruct x,y; simpl in *.
  apply JMeq_eq in H0.
  subst.
  have e : t_t0 = t_t1.
  {
    repeat (apply:funext ; intros).
    apply:JMeq_eq.
    auto.
  }
  subst.
  have e : eq_iA0 = eq_iA1.
  {
    repeat (apply:funext ; intros).
    apply:uip.
  }
  now subst.
Qed.






Definition r_rl_ext 
         (sΓ : rC) (sA : rT sΓ) (su : rtm sA) : rC.
  unshelve refine (
               {| C_TY := { γ : { a : C_TY sΓ & T_TY sA a } & γ..2 =h t_t su γ..1} ;
            C_fib := _;
            idA := fun a => idA sΓ a ,Σ
                                     (* iA sA a ,Σ _; *)
                                     t_t su (idA sΓ a) ,Σ reflh _;
            JA := _;
            JA_idA := _
         |}).
  cbn.
  (* Fin de idA *)
  (* - rewrite (eq_iA su a). *)
  (*   apply reflh. *)
  -
    intros P fibP d γzu.
    destruct γzu as [[γ z] f].
    set (fibP' :=  ((fun y e => fibP ((γ ,Σ y) ,Σ e)))).
    cbn in fibP'.
    cbn in d.
    refine (Jh (T_fib sA γ) fibP'
                  (JA (r := sΓ)
                      (fun δ => fibP (δ ,Σ t_t su δ ,Σ reflh _)  )
                      (* (fun δ => fibP (δ ,Σ _ δ ,Σ  _)  )  *)
                      d γ
                  )
                  f
                ).
    (* exact d. *)

  - repeat apply sigma_Fib.
    + apply C_fib.
    + apply T_fib.
    + intro a.
      apply eq_Fib.
      apply : T_fib.
  -  intros P fibP d a.
     cbn.
     etrans.
     apply : βJh.
     apply : JA_idA.
Defined.

Definition r_rl_ar 
             (sΓ : rC) (sA : rT sΓ) (st : rtm sA)(su : rtm sA) : rT sΓ.
  unshelve refine (
             {| T_TY := fun γ => t_t st γ =h t_t su γ;
                T_fib := fun γ => eq_Fib (T_fib sA γ ) _ _ ;
                iA := _ |}
         ).
  - intro a.
    rewrite (eq_iA st) (eq_iA su).
    apply reflh.
Defined.

Definition r_rl_astar : rC :=
                    {| C_TY := T;
                     C_fib := fibT ;
                     idA := id;
                     JA := fun P fibP d δ => d δ;
                     JA_idA := fun P fibP d a => erefl
                  |}.

Definition r_rl_star {Γ : rC} : rT Γ :=
                {| T_TY := fun _ => T;
                 T_fib := fun _ => fibT;
                 iA := id |}.

Definition r_rl_vstar   : rtm (Γ := r_rl_astar) r_rl_star :=
  {| t_t := fun (x : (C_TY r_rl_astar)) => (x : T_TY r_rl_star _); eq_iA := fun a => erefl |}.

Definition r_sbT (Γ Δ : rC)(σ : rS Γ Δ) (A : rT Δ)  : rT Γ.
  refine ({| T_TY := fun x => T_TY A (S σ x);
            T_fib := fun x => T_fib A (S σ x); 
            iA := _  |}).
  (* iA *)
  intro a.
  rewrite  (sb_idA σ a).
  exact  ( iA A a).
Defined.

Definition r_sbS (Γ Δ E : rC)(σ : rS Γ Δ)(δ : rS Δ E)   : rS Γ E.
  refine ({| S := fun x => (S δ (S σ x)) |}).
  intro a.
  rewrite sb_idA.
  apply:sb_idA.
Defined.

Lemma J {A : Type} (x : A) (P : forall (y : A) (w : y = x) , Type) : P x erefl ->
                                                                forall (y : A)(w : y = x) , P y w.
   now destruct w.
Defined.
Lemma J_r {A : Type} (x : A) (P : forall (y : A) (w : x = y) , Type) : P x erefl ->
                                                                forall (y : A)(w : x = y) , P y w.
   now destruct w.
Defined.

Definition r_sbt (Γ Δ : rC)(σ : rS Γ Δ) (A : rT Δ) (t : rtm A)  : rtm (r_sbT σ A).
  refine ({| t_t := fun x => (t_t t (S σ x) : T_TY (r_sbT σ A) _);
             eq_iA := _ |}).
  (* iA *)
  intro a.
  cbn.
  pattern (S σ (idA Γ a)) ,(sb_idA σ a).
  apply J.
  exact  (eq_iA t a).
Defined.

(* TODO remplacer ça par une utilisation adéquate de  r_sbT *)
Definition r_wkT (sΓ : rC)(sA : rT sΓ)(su : rtm sA)(sB : rT sΓ) :
   rT (r_rl_ext su) :=
                  {| T_TY := fun (γzu : C_TY (r_rl_ext su)) => T_TY sB (γzu ..1..1);
                 T_fib := fun γzu => T_fib sB (γzu ..1..1);
                 iA := iA sB |}.


(* TODO remplacer ça en utilisan r_sbt *)
Definition r_wkt 
               (sΓ : rC) (sA : rT sΓ) (su : rtm sA)(sB : rT sΓ)(sx : rtm sB)
                :
  rtm (r_wkT su sB) :=
      {| t_t := fun (x : (C_TY (r_rl_ext su))) =>
                   (t_t sx x..1..1 : T_TY (r_wkT su sB) x)
          ; eq_iA := eq_iA sx |}.

Definition r_wkS (sΓ : rC)(sA : rT sΓ)(su : rtm sA) sΔ (sσ : rS sΓ sΔ) :
  rS (r_rl_ext su) sΔ :=
  {| S := fun γ : C_TY (r_rl_ext su) => S sσ (γ ..1) ..1;
     sb_idA := [eta sb_idA sσ] |}.


Definition r_rl_v1  (sΓ : rC) (sA : rT sΓ) (su : rtm sA) : rtm (r_wkT su sA) :=
  ({| t_t := fun (x :C_TY (r_rl_ext su)) => (x..1..2 : T_TY (r_wkT su sA) x)
             ; eq_iA := eq_iA su |}).
 
Definition r_rl_v0  (sΓ : rC) (sA : rT sΓ) (su : rtm sA) :
  rtm (r_rl_ar (r_rl_v1 su) (r_wkt su su)).
  refine ({| t_t := fun (x :C_TY (r_rl_ext su)) =>
               (x..2 : T_TY (r_rl_ar (r_rl_v1 su) (r_wkt su su)) x)
             ; eq_iA := _ |}).
  intro a.
  cbn.
  case (eq_iA su a).
  reflexivity.
Defined.

Definition r_rl_coh (sΓ : rC) (sΔ : rC) (sB : rT sΔ) (sσ : rS sΓ sΔ) : 
  rtm (r_sbT sσ sB).
  refine ( {| t_t := fun γ : C_TY sΓ =>
                       (JA (T_fib sB) (iA sB) (S sσ γ) : T_TY (r_sbT sσ sB) _);
              eq_iA := _ |}).
  intro a.
  cbn.
  pattern (S sσ (idA sΓ a)) ,(sb_idA sσ a).
  apply J.
  apply : JA_idA.
Defined.

                  
Definition r_rl_to_star (sΓ : rC) (st : rtm (Γ := sΓ) r_rl_star) :
  rS sΓ r_rl_astar :=
   ({| S := fun γ => (t_t st γ : C_TY r_rl_astar) ;  sb_idA :=  eq_iA st |}).





(* TODO supprimer ce lemme et remplacer l'énoncé des lemmes dont l'utilisation
nécessite ce lemme
 *)
Lemma eq_rect_inv (A : Type) (x : A) (P : A -> Type)  (y : A) (w : x= y) Py :
  @eq_rect A x P (@eq_rect A y P Py x (esym w)) y w = Py.
Proof.
  by destruct w.
Qed.

Definition r_rl_to_ext 
                    (sΓ : rC) (sΔ : rC)(sA : rT sΔ) (su : rtm sA)
                    (sσ : rS sΓ sΔ) (sa : rtm (r_sbT sσ sA))
                    (sf :  rtm (r_rl_ar sa (r_sbt sσ su))) : rS sΓ ( r_rl_ext su).
  refine ( {| S := fun γ : C_TY sΓ => ((S sσ γ,Σ t_t sa γ),Σ t_t sf γ : C_TY (r_rl_ext su));
              sb_idA := _ |}).
  intro a.
  cbn.
  (* cbn. *)
  (* rewrite (eq_iA sf a). *)
  (* cbn. *)
  (* rewrite (eq_iA su a). *)
  apply eq_sigT_sig_eq.
  unshelve econstructor; [apply eq_sigT_sig_eq; unshelve econstructor|].
  -  apply (sb_idA sσ).
  - 
    (* rewrite (eq_iA sa)(eq_iA su). *)
    pattern (t_t sa (idA sΓ a)),(eq_iA sa a).
    apply:J.
    pattern (t_t su (idA sΔ a)),(eq_iA su a).
    apply:J.
    cbn.
    pattern (S sσ (idA sΓ a)), (sb_idA sσ a).
    apply:J.
    reflexivity.
  - cbn.
    rewrite (eq_iA sf).
    cbn.
    apply JMeq_eq.
    apply:JMeq_trans.
    + match goal with
        |   [ |-   eq_rect ?x ?P ?Px ?y ?w ≅ _]  => apply: (@JMeq_eq_rect _ x P Px y w)
          end.
    + apply:JMeq_trans; first by apply:JMeq_eq_rect_r.
      apply:JMeq_trans; first by  apply:JMeq_eq_rect_r.
      rewrite (eq_iA su).
      pattern ( S sσ (idA sΓ a)),(sb_idA sσ a).
      now apply:J.
Defined.


(* pack record *)
Record pT :=
  mkpT {
      pT_C : rC;
      pT_T : rT pT_C
    }.

Record pTm :=
  mkpt {
      pt_C : rC;
      pt_T : rT pt_C;
      pt_t : rtm pt_T
      }.

Record pS :=
  mkpS {
      pS_C1 : rC;
      pS_C2 : rC;
      pS_S : rS pS_C1 pS_C2
      }.

Arguments mkpT [sΓ] _ : rename.
Arguments mkpt [sΓ] [sA] _ : rename.
Arguments mkpS [sΓ] [sΔ] _ : rename.

(* Spécification de la fonction qu'on veut définir *)
(* TODO : peeut etre donner une définition plus spécifique du weakening plut$pt
que d'utiliser les subtitutions *)
(* Rétrospectivement, c'était pas uen bone idée d'imposer la forme du jugement
de typage, notamment pour les variables, les termes
Par exemple, pour rl_ext, ca aurait pu mieux se passer avec
    rl_C (Γ := ext Γ A u) wΓe
         (r_rl_ext  su)
*)
Inductive rl_C : forall (Γ : Con) (wΓ : WC Γ), rC -> Type :=
  rl_astar : rl_C (Γ := astar) w_astar r_rl_astar
| rl_ext (Γ : Con)  (A : Ty) (u : Tm)
         (wΓ : WC Γ) (wA : Γ ⊢ A) (wu : Γ ⊢ u : A)
         (sΓ : rC) (sA : rT sΓ) (su : rtm sA) :
    rl_C wΓ sΓ -> rl_T wΓ wA (mkpT sA) -> rl_t wΓ wA wu (mkpt su) ->
    rl_C (Γ := ext Γ A u) (w_ext wΓ wA wu )
         (r_rl_ext  su)

         
with rl_T : forall (Γ : Con) (A : _) (wΓ : WC Γ)  (wA : Γ ⊢ A)  , pT  -> Type :=
       rl_star (Γ : Con) (wΓ : WC Γ) (sΓ : rC ) : rl_C wΓ sΓ ->
         rl_T wΓ  (A := star) (w_star wΓ) (mkpT (sΓ := sΓ) r_rl_star)
     | rl_ar (Γ : Con) (A : _) (t u : Tm)
             (wΓ : WC Γ) (wA : Γ ⊢ A) (wt : Γ ⊢ t : A) (wu : Γ ⊢ u : A)
             (sΓ : rC) (sA : rT sΓ) (st : rtm sA)(su : rtm sA) :
         rl_C wΓ sΓ -> rl_T wΓ wA (mkpT sA) -> rl_t wΓ wA wt (mkpt st)
         -> rl_t wΓ wA wu (mkpt su) ->
         rl_T wΓ (A := ar A t u) (w_ar wA wt wu) (mkpT (sΓ := sΓ) (r_rl_ar st su))

with rl_t : forall (Γ : Con)  (A : _) (t : Tm)
              (wΓ : WC Γ)(wA : Γ ⊢ A) (wt : Γ ⊢ t : A)
              , pTm -> Type :=
     | rl_va  (Γ : Con)  (A : _) (x : Var)
              (wΓ : WC Γ)(wA : Γ ⊢ A) (wx : WVar Γ A x)
              (sΓ : rC) (sA : rT sΓ) (sx : rtm sA) :
         (* rl_C wΓ sΓ -> rl_T wΓ wA sA -> *)
         rl_V wΓ wA wx (mkpt sx) -> 
         rl_t wΓ wA (w_va wx) (mkpt sx)
     | rl_coh (Γ : Con)     (Δ : Con) (B : Ty) (σ : sub)
              (wΓ : WC Γ) (wΔ : WC Δ) (wB : Δ ⊢ B)(wBσ : Γ ⊢ B.[σ]T)
              (wσ : Γ ⊢ σ ⇒ Δ)
             (sΓ : rC) (sΔ : rC) (sB : rT sΔ) (sσ : rS sΓ sΔ)  :
             rl_C wΓ sΓ -> rl_C wΔ sΔ -> rl_T wΔ wB (mkpT sB) ->
             rl_S wΓ wΔ wσ (mkpS sσ) ->
             rl_t (A := B .[ σ ]T) (t := coh Δ B σ)  wΓ wBσ (w_coh wΔ wB  wσ (* wBσ *))
                  (mkpt (sA := r_sbT sσ sB) (r_rl_coh sB sσ))


with rl_V :  forall (Γ : Con)  (A : Ty) (x : Var)
               (wΓ : WC Γ)(wA : Γ ⊢ A) (wx : WVar Γ A x), pTm -> Type :=
    | rl_vstar :
         rl_V (Γ := astar) (A := star) (x :=  vstar) w_astar (w_star w_astar) w_vstar
              (mkpt (sΓ := r_rl_astar) (sA := r_rl_star) r_rl_vstar)
    | rl_vwk (Γ : Con)  (A : Ty) (u : Tm) (B : Ty) (x : Var)
             (wΓ : WC Γ) (wA : Γ ⊢ A)  (wu : Γ ⊢ u : A) (wB : Γ ⊢ B) (wx : WVar Γ B x)
             (* redondant *)
               (wBe : ext Γ A u ⊢ wkT B )
               (sΓ : rC) (sA : rT sΓ) (su : rtm sA)(sB : rT sΓ)(sx : rtm sB) :
        rl_C wΓ sΓ -> rl_T wΓ wA (mkpT sA) ->
        rl_t wΓ wA wu (mkpt su) ->  rl_T wΓ wB (mkpT sB) ->
        rl_V wΓ wB wx (mkpt sx) ->
        rl_V (Γ := ext Γ A u) (A := wkT B) (x := vwk x)
             (w_ext wΓ wA wu) wBe (w_vwk  wx wu)
             (mkpt
             (sΓ :=  r_rl_ext su)
             (r_wkt su sx))
    | rl_v1 (Γ : Con)  (A : Ty) (u : Tm)  
            (wΓ : WC Γ) (wA : Γ ⊢ A)
            (wu : Γ ⊢ u : A)
             (* redondant *)
               (wAe : ext Γ A u ⊢ wkT A )
             (sΓ : rC) (sA : rT sΓ) (su : rtm sA) :
             rl_C wΓ sΓ -> rl_T wΓ wA (mkpT sA) -> rl_t wΓ wA wu (mkpt su) -> 
             rl_V (Γ := ext Γ A u) (A := wkT A) (x := v1)
                  (w_ext wΓ wA wu)
                  wAe
                  (* (eq_refl _) *)
                  ((w_v1 wu ))
                  (mkpt (sA := r_wkT su sA) (r_rl_v1 su))
    | rl_v0 (Γ : Con)  (A : Ty) (u : Tm)  
             (wΓ : WC Γ) (wA : Γ ⊢ A)  (wu : Γ ⊢ u : A)
             (* redondant *)
               (wAe : ext Γ A u ⊢ wkT A )
               (wue :  ext Γ A u ⊢ wkt u : wkT A )
             (sΓ : rC) (sA : rT sΓ) (su : rtm sA) :
             rl_C wΓ sΓ -> rl_T wΓ wA (mkpT sA) -> rl_t wΓ wA wu (mkpt su) -> 
             rl_V (Γ := ext Γ A u) (A := ar (wkT A) (va v1) (wkt u))
                  (x := v0) (w_ext wΓ wA wu)
                  (w_ar (Γ := ext Γ A u) wAe (w_va (w_v1 wu)) wue)
                  (* erefl *)
                  (* (w_ar  *)
                  (* (eq_refl _) *)
                  ( (w_v0 wu ))
                  (mkpt (sA := (r_rl_ar (r_rl_v1 su) (r_wkt su su))) (r_rl_v0 su))
with rl_S : forall (Γ Δ : Con)  (σ : sub)
              (wΓ : WC Γ)(wΔ : WC Δ) (wσ : Γ ⊢ σ ⇒ Δ),
               pS -> Type :=
     | rl_to_star (Γ : Con) (t : Tm)
                  (wΓ : WC Γ) (wt : Γ ⊢ t : star)
                  (sΓ : rC) (st : rtm (Γ := sΓ) r_rl_star) :
         rl_C wΓ sΓ -> rl_t (A := star) wΓ (w_star wΓ) wt (mkpt st) ->
         rl_S (Δ := astar) (σ := to_star t)
              wΓ w_astar (w_to_star wt) (mkpS (sΓ := sΓ) (sΔ := r_rl_astar) 
              (r_rl_to_star st))

     | rl_to_ext (Γ Δ : Con)  (A : Ty) (u : Tm) (σ : sub) (a : Tm) (f : Tm)

                 (wΓ : WC Γ)(wΔ : WC Δ)
                 (wA : Δ ⊢ A) (wu : Δ ⊢ u : A)
                 (* redondant *)
                 (wAσ : Γ ⊢ A.[σ]T) (wuσ : Γ ⊢ u.[σ]t : A.[σ]T)
                    (wσ : Γ ⊢ σ ⇒ Δ) (wa : Γ ⊢ a : A .[ σ ]T)
                    (wf : Γ ⊢ f : ar (A .[σ]T) a (u.[σ]t))

                    (sΓ : rC) (sΔ : rC)(sA : rT sΔ) (su : rtm sA)
                    (sσ : rS sΓ sΔ) (sa : rtm (r_sbT sσ sA))
                    (sf :  rtm (r_rl_ar sa (r_sbt sσ su))) :
         rl_C wΓ sΓ -> rl_C wΔ sΔ -> rl_T wΔ wA (mkpT sA) -> rl_t wΔ wA wu (mkpt su) ->
         rl_S wΓ wΔ wσ (mkpS sσ) ->
         rl_t (A := A .[ σ ]T) wΓ wAσ wa (mkpt sa) ->
         rl_t (A := ar (A .[ σ ]T) a (u.[σ]t)) wΓ (w_ar wAσ wa wuσ) wf (mkpt sf) ->

         rl_S (Δ := ext Δ A u) (σ := to_ext σ a f)  wΓ (w_ext wΔ wA wu)
              (w_to_ext  wσ wA wu wa wf)
              (mkpS (sΓ := sΓ) (sΔ := r_rl_ext su)
              (r_rl_to_ext sf)).


Definition all_eq (A : Type) (P : A -> Type) (a : A) :=
  forall a' ,  P a' -> a = a'.

Open Scope wf_scope.
Open Scope subst_scope.



(* TODO peut être intuile avec pt_eq  ?? *)
Lemma π_eq_pT (a b : pT) (e : a = b) : pT_T a ≅ pT_T b.
by now destruct e.
Qed.
Lemma π_eq_pTη a b b' (c :=@mkpT a b) (c' := @mkpT a b')
      (e : c = c') : b = b'.
  by apply/JMeq_eq:(π_eq_pT e).
Qed.

(* celui ci est peut être plus utile que les 2 autres ?? *)
Lemma π_eq_pTη' a a' b b' (c :=@mkpT a b) (c' := @mkpT a' b')
      (e : c = c') : b ≅ b'.
  change (pT_T c ≅ pT_T c').
  now destruct e.
Qed.

Lemma π_eq_pTC (a b : pT) (e : a = b) : pT_C a = pT_C b.
by now destruct e.
Qed.
Lemma π_eq_pt (a b : pTm) (e : a = b) : pt_t a ≅ pt_t b.
by now destruct e.
Qed.

Lemma π_eq_ptη' a a' b b' c c' (d :=@mkpt a b c) (d' := @mkpt a' b' c')
      (e : d = d') : c ≅ c'.
  change (pt_t d ≅ pt_t d').
  now destruct e.
Qed.

Lemma π_eq_ptη a b c c' (d :=@mkpt a b c) (d' := @mkpt a b c')
      (e : d = d') : c = c'.
  by apply/JMeq_eq:(π_eq_pt e).
Qed.
Lemma π_eq_ptTη (Γ : rC) (A B : rT Γ)(a : rtm A) (b : rtm B) (e : mkpt a = mkpt b) : A = B.
  apply:JMeq_eq.
  change (pt_T (mkpt a) ≅ pt_T (mkpt b)).
  now rewrite e.
Qed.

Lemma π_eq_ptC (a b : pTm) (e : a = b) : pt_C a = pt_C b.
by now destruct e.
Qed.
Lemma π_eq_pS (a b : pS ) (e : a = b) : pS_S a ≅ pS_S b.
by now destruct e.
Qed.

Lemma π_eq_pSη a b c c' (d :=@mkpS a b c) (d' := @mkpS a b c')
      (e : d = d') : c = c'.
  by apply/JMeq_eq:(π_eq_pS e).
Qed.
Lemma π_eq_pSC (a b : pS) (e : a = b) : pS_C1 a = pS_C1 b.
by now destruct e.
Qed.
Lemma π_eq_pSC2 (a b : pS) (e : a = b) : pS_C2 a = pS_C2 b.
by now destruct e.
Qed.


Lemma rl_hp_va  (x : Var) (Γ : Con) (wΓ : WC Γ) (A : Ty) (wA : Γ ⊢ A) (wx : WVar Γ A x) (sΓ : rC) 
      (sA : rT sΓ) (sx : rtm sA) :
  all_eq (rl_V wΓ wA wx) {| pt_C := sΓ; pt_T := sA; pt_t := sx |} ->
  all_eq (rl_t wΓ wA (w_va wx)) {| pt_C := sΓ; pt_T := sA; pt_t := sx |}.
Proof.
    move => HIx.
    move => px'.
    inversion 1; repeat clear_hprop; repeat (clear_jmsigma; subst).
    now apply:HIx.
Qed.

Lemma rl_hp_coh (B : Ty) (σ : sub) (sΔ : rC) (sB : rT sΔ) (sΓ : rC) (sσ : rS sΓ sΔ) 
    (Δ : Con) (wΔ : WC Δ) (wB : Δ ⊢ B) (Γ : Con) (wΓ : WC Γ) (wBσ : Γ ⊢ B.[σ]T) 
    (wσ : Γ ⊢ σ ⇒ Δ) :
  all_eq (rl_S wΓ wΔ wσ) {| pS_C1 := sΓ; pS_C2 := sΔ; pS_S := sσ |} ->
  all_eq (rl_T wΔ wB) {| pT_C := sΔ; pT_T := sB |} ->
  all_eq (rl_C wΔ) sΔ ->
  all_eq (rl_C wΓ) sΓ ->
  all_eq (rl_t wΓ wBσ (w_coh wΔ wB wσ)) {| pt_C := sΓ; pt_T := r_sbT sσ sB; pt_t := r_rl_coh sB sσ |}.
Proof.

    move => IHσ IHB IHΔ IHΓ.
    move => px'.
    inversion 1; subst;repeat clear_hprop; repeat (clear_jmsigma; subst).
    have ? : sΓ = sΓ0 by apply:IHΓ.
    have ? : sΔ = sΔ0 by apply:IHΔ.
    subst.
    have ? : sB = sB0 by apply:π_eq_pTη; apply:IHB.
    have ? : sσ = sσ0 by apply:π_eq_pSη; apply: IHσ.
    now subst.
Qed.

Lemma rl_T_C (Γ : Con) (A : Ty) (wΓ : WC Γ) (wA : Γ ⊢ A)
            (pA : pT)
            (* (rlΓ : rl_C wΓ sΓ) *)
            (rlA : rl_T wΓ wA pA)
      : rl_C wΓ (pT_C pA).
Proof.
  now destruct rlA.
Qed.
Lemma rl_T_Cη (Γ : Con) (A : Ty) (wΓ : WC Γ) (wA : Γ ⊢ A)
      sΓ (sA : rT sΓ)
            (pA := mkpT sA)
            (* (rlΓ : rl_C wΓ sΓ) *)
            (rlA : rl_T wΓ wA pA)
      : rl_C wΓ sΓ.
Proof.
  by move/rl_T_C:rlA.
Qed.

Lemma rl_V_C  (Γ : Con)  (A : _) (x : Var)
              (wΓ : WC Γ)(wA : Γ ⊢ A) (wx : WVar Γ A x) 
              (* (sΓ : rC)(sA : rT sΓ) *)
              (px : pTm )
              (rlt : rl_V wΓ wA wx px)
     : rl_C wΓ (pt_C px).
  destruct rlt => //=; constructor => //=.
Qed.

Lemma rl_V_Cη  (Γ : Con)  (A : _) (x : Var)
              (wΓ : WC Γ)(wA : Γ ⊢ A) (wx : WVar Γ A x) 
              (sΓ : rC)(sA : rT sΓ) (sx: rtm sA)
              (px := mkpt sx)
              (rlt : rl_V wΓ wA wx px)
     : rl_C wΓ sΓ.
  by move/rl_V_C:rlt.
Qed.
Lemma rl_t_C  (Γ : Con)  (A : _) (t : Tm)
             (wΓ : WC Γ)(wA : Γ ⊢ A) (wt : Γ ⊢ t : A)
             (pt : pTm )
             (rlt : rl_t wΓ wA wt pt)
     : rl_C wΓ  ((pt_C pt)).
Proof.
  destruct rlt => //=.
  - move/rl_V_C:r.
    apply.
Qed.
(*TODO peut etre plus utile que l'autre ? *)
Lemma rl_t_Cη  (Γ : Con)  (A : _) (t : Tm)
             (wΓ : WC Γ)(wA : Γ ⊢ A) (wt : Γ ⊢ t : A)
             sΓ (sA : rT sΓ) (st : rtm sA)
             (rlt : rl_t wΓ wA wt (mkpt st))
     : rl_C wΓ   sΓ.
Proof.
  by move/rl_t_C:rlt.
Qed.

Lemma rl_S_C1 (Γ Δ : Con)  (σ : sub)
            (wΓ : WC Γ)(wΔ : WC Δ) (wσ : Γ ⊢ σ ⇒ Δ) 
            (pσ : pS)
                (rlσ : rl_S wΓ wΔ wσ pσ) :
          (rl_C wΓ (pS_C1 pσ)) .
  destruct rlσ => //.
Qed.
Lemma rl_S_C1η (Γ Δ : Con)  (σ : sub)
            (wΓ : WC Γ)(wΔ : WC Δ) (wσ : Γ ⊢ σ ⇒ Δ) 
            sΓ sΔ (sσ : rS sΓ sΔ)
            (pσ := mkpS sσ)
                (rlσ : rl_S wΓ wΔ wσ pσ) :
          (rl_C wΓ sΓ) .
  by move/rl_S_C1:rlσ.
Qed.

Lemma rl_S_C2 (Γ Δ : Con)  (σ : sub)
            (wΓ : WC Γ)(wΔ : WC Δ) (wσ : Γ ⊢ σ ⇒ Δ) 
            (pσ : pS)
                (rlσ : rl_S wΓ wΔ wσ pσ) :
          (rl_C wΔ (pS_C2 pσ)) .
  destruct rlσ => //; constructor => //.
Qed.

Lemma rl_S_C2η (Γ Δ : Con)  (σ : sub)
            (wΓ : WC Γ)(wΔ : WC Δ) (wσ : Γ ⊢ σ ⇒ Δ) 
            sΓ sΔ (sσ : rS sΓ sΔ)
            (pσ := mkpS sσ)
                (rlσ : rl_S wΓ wΔ wσ pσ) :
          (rl_C wΔ sΔ) .
  by move/rl_S_C2:rlσ.
Qed.

(* Par récurrence sur le premier r* trouvé *)
Fixpoint rl_hpC (Γ : Con) (wΓ : WC Γ) (sΓ : rC) (rlΓ : rl_C wΓ sΓ) {struct rlΓ}
  : all_eq (rl_C wΓ) sΓ
with rl_hpT (Γ : Con) (A : Ty) (wΓ : WC Γ) (wA : Γ ⊢ A)
            (pA : pT)
            (* (rlΓ : rl_C wΓ sΓ) *)
            (rlA : rl_T wΓ wA pA) {struct rlA}
      : all_eq (rl_T wΓ wA) pA
with rl_hpt  (Γ : Con)  (A : _) (t : Tm)
             (wΓ : WC Γ)(wA : Γ ⊢ A) (wt : Γ ⊢ t : A)
             (* (sΓ : rC)(sA : rT sΓ) *)
             (pt : pTm )
             (* (rlΓ : rl_C wΓ sΓ) (rlA : rl_T wΓ wA sA) *)
             (rlt : rl_t wΓ wA wt pt)
             {struct rlt}
     : all_eq (rl_t wΓ wA wt) pt
with rl_hpV  (Γ : Con)  (A : _) (x : Var)
              (wΓ : WC Γ)(wA : Γ ⊢ A) (wx : WVar Γ A x) 
              (* (sΓ : rC)(sA : rT sΓ) *)
              (px : pTm )
              (rlt : rl_V wΓ wA wx px)

     : all_eq (rl_V wΓ wA wx) px
with rl_hpS (Γ Δ : Con)  (σ : sub)
            (wΓ : WC Γ)(wΔ : WC Δ) (wσ : Γ ⊢ σ ⇒ Δ) 
            (pσ : pS)
                (rlσ : rl_S wΓ wΔ wσ pσ) :
         all_eq  (rl_S wΓ wΔ wσ) pσ.
  - move => sΓ'.
    destruct rlΓ.
  +  
    inversion 1; subst;repeat clear_hprop; repeat (clear_jmsigma; subst).
      reflexivity.
      
  + Guarded.
    move/rl_hpC : rlΓ => IHΓ.
    move/rl_hpT : r => IHA.
    move/rl_hpt : r0 => IHu.
    inversion 1; subst;repeat clear_hprop; repeat (clear_jmsigma; subst).
    have e : sΓ = sΓ0 by apply:IHΓ.
    subst.
    have e: sA = sA0 by  apply:π_eq_pTη; apply:IHA.
    subst.
    have e : su = su0 by apply :π_eq_ptη; apply IHu.
    now subst su0.
- destruct rlA.
    + move/rl_hpC:r => HIΓ.
      move => pA'.
      inversion 1; subst;repeat clear_hprop; repeat (clear_jmsigma; subst).
      have e : sΓ = sΓ0 by apply:HIΓ.
      subst.
      reflexivity.
  + move /rl_hpC:r => IHΓ.
    move /rl_hpT:rlA => IHA.
    move /rl_hpt:r0 => IHt.
    move /rl_hpt:r1 => IHu.
    move => pA'.
    inversion 1; repeat clear_hprop; repeat (clear_jmsigma; subst).
    have e : sΓ = sΓ0 by apply:IHΓ.
    subst.
    have ? :  sA = sA0 by apply:π_eq_pTη; apply:IHA.
    subst.
    have ? :  st = st0 by apply:π_eq_ptη; apply : IHt.
    have ? :  su = su0 by apply:π_eq_ptη; apply : IHu.
    now subst.
- 
  destruct rlt.
  + move/rl_hpV : r.
    apply:  rl_hp_va.
  + 
    move/rl_hpC : r .
    move/rl_hpC : r0.
    move/rl_hpT : r1.
    move/rl_hpS : r2.
    apply:rl_hp_coh.
- destruct rlt.
  + move => px'.
    now inversion 1; repeat clear_hprop; repeat (clear_jmsigma; subst).
  + move/rl_hpC:r => IHΓ.
    move/rl_hpT:r0 => IHA.
    move/rl_hpT:r2 => IHB.
    move/rl_hpt:r1 => IHu.
    move/rl_hpV:rlt => IHx.
    move => px'.
    inversion 1; repeat clear_hprop; repeat (clear_jmsigma; subst).
    have ? : sΓ = sΓ0 by apply:IHΓ.
    subst.
    have ? :  sA = sA0 by apply:π_eq_pTη; apply:IHA.
    subst sA0.
    have ? :  su = su0 by apply:π_eq_ptη; apply : IHu.
    have ? : sB = sB0 by apply:π_eq_pTη; apply:IHB.
    subst.
    have ? :  sx = sx0 by apply:π_eq_ptη; apply : IHx.
    subst.
    now repeat split.

  + move/rl_hpC:r => IHΓ.
    move/rl_hpT:r0 => IHA.
    move/rl_hpt:r1 => IHu.
    move => px'.
    inversion 1; repeat clear_hprop; repeat (clear_jmsigma; subst).
    have ? : sΓ = sΓ0 by apply:IHΓ.
    subst.
    have ? :  sA = sA0 by apply:π_eq_pTη; apply:IHA.
    subst.
    have ? :  su = su0 by apply:π_eq_ptη; apply : IHu.
    subst.
    now repeat split.
  + move/rl_hpC:r => IHΓ.
    move/rl_hpT:r0 => IHA.
    move/rl_hpt:r1 => IHu.
    move => px'.
    inversion 1; repeat clear_hprop; repeat (clear_jmsigma; subst).
    have ? : sΓ = sΓ0 by apply:IHΓ.
    subst.
    have ? :  sA = sA0 by apply:π_eq_pTη; apply:IHA.
    subst.
    have ? :  su = su0 by apply:π_eq_ptη; apply : IHu.
    subst.
    repeat split.
- destruct rlσ.
  + move/rl_hpC:r => IHΓ.
    move/rl_hpt:r0 => IHt.
    move => pσ'.
    inversion 1; repeat clear_hprop; repeat (clear_jmsigma; subst).
    have ? : sΓ = sΓ0 by apply:IHΓ.
    subst.
    have ? :  st = st0 by apply:π_eq_ptη; apply:IHt.
    subst.
    now repeat split.
  + move/rl_hpC:r => IHΓ.
    move/rl_hpC:r0 => IHΔ.
    move/rl_hpT:r1 => IHA.
    move/rl_hpt:r2 => IHu.
    move/rl_hpS:rlσ => IHσ.
    move/rl_hpt:r3 => IHa.
    move/rl_hpt:r4 => IHf.
    move => pσ'.
    inversion 1; repeat clear_hprop; repeat (clear_jmsigma; subst).
    have ? : sΓ = sΓ0 by apply:IHΓ.
    have ? : sΔ = sΔ0 by apply:IHΔ.
    subst.
    have ? :  sA = sA0 by apply:π_eq_pTη; apply:IHA.
    subst.
    have ? :  sσ = sσ0 by apply:π_eq_pSη; apply:IHσ.
    have ? :  su = su0 by apply:π_eq_ptη; apply : IHu.
    subst.
    have ? :  sa = sa0 by apply:π_eq_ptη; apply : IHa.
    subst.
    have ? :  sf = sf0  by apply:π_eq_ptη; apply : IHf.
    subst.
    reflexivity.
Qed.
Lemma
  compr_T Γ Δ E (sσ : rS Γ Δ) (sδ : rS Δ E) sB :
  r_sbT (r_sbS sσ sδ) sB = r_sbT sσ (r_sbT sδ sB).
Proof.
  apply:JMeq_eq.
  apply : rTeq => //=.
  - cbn.
    (* erewrite (uip _ erefl). *)
      by move => γ γ' /(@JMeq_eq _ _ _) -> //.
  - move => a .
    apply:JMeq_trans;first by apply JMeq_eq_rect_r.
    apply:JMeq_sym.
    apply:JMeq_trans.
    {
    set w := (w in eq_rect_r _ _ w).
    apply : (JMeq_eq_rect_r  _ w).
    }
    set w := (w in eq_rect_r _ _ w).
    apply:  (JMeq_eq_rect_r _ w).
  -by move => γ γ' /(@JMeq_eq _ _ _) -> //.
Qed.
Lemma compr_Tm sΓ sΔ sE (sσ : rS sΓ sΔ) (sδ : rS sΔ sE)
      sA (su : rtm sA) :
  r_sbt sσ (r_sbt sδ su) ≅ r_sbt (r_sbS sσ sδ) su.
Proof.
  apply:rtmeq => //=.
  - now rewrite compr_T.
  -by move => γ γ' /(@JMeq_eq _ _ _) -> //.
Qed.
Lemma pt_eq (Γ Γ' : rC) (A  : rT Γ)(A'  : rT Γ') (x : rtm A) (x' : rtm A') 
 (* (e : A = A') : x ≅ x' -> mkpt x = mkpt x'. *)
 (e : Γ = Γ') : A ≅ A' -> x ≅ x' -> mkpt x = mkpt x'.
  subst.
  move => h1 h2.
  apply JMeq_eq in h1; subst.
  apply JMeq_eq in h2; subst.
  reflexivity.
Qed.
(* TODO : remplacer l'égalité JMeq par un transport *)
Lemma pt_eq1 (Γ : rC) (A A' : rT Γ) (x : rtm A) (x' : rtm A') 
 (* (e : A = A') : x ≅ x' -> mkpt x = mkpt x'. *)
      (* en fait inutile .. *)
 (e : A = A') : eq_rect _ _ x _ e = x' -> mkpt x = mkpt x'.
  move => ex.
  apply : pt_eq => //=.
  - by apply:JMeq_from_eq.
  - rewrite -ex.
    symmetry.
    apply:JMeq_eq_rect.
Qed.
Lemma pS_eq1 (Γ Δ Δ' : rC)  (x  : rS Γ Δ) (x'  : rS Γ Δ') 
  (e : Δ = Δ')  : eq_rect _ (rS Γ) x _ e = x' -> mkpS x = mkpS x'.
  destruct e => /= -> //=.
Qed.
Lemma pT_eq1 (Γ Γ' : rC) x x'   
 (* (e : A = A') : x ≅ x' -> mkpt x = mkpt x'. *)
 (e : Γ = Γ') : x = eq_rect_r rT x' e -> mkpT x = mkpT x'.
  destruct e => /= -> //=.
Qed.

      
Lemma tp_rTm1 Γ B B' t (wΓ : WC Γ) (wB : Γ ⊢ B)(wB' : Γ ⊢ B')
      (wt : Γ ⊢ t : B)(wt' : Γ ⊢ t : B') pt pt'
  :
  B = B' -> pt = pt' -> rl_t wΓ wB' wt' pt' -> rl_t wΓ wB wt pt .
Proof.
  move => eB et.
  destruct eB, et.
  have eB : wB = wB' by apply:WTy_hp.
  have et : wt = wt' by apply:WTm_hp.
  destruct eB, et.
  exact.
Qed.
Lemma tp_rV1 Γ B B' x (wΓ : WC Γ) (wB : Γ ⊢ B)(wB' : Γ ⊢ B')
      (wx : WVar Γ B x)(wx' : WVar Γ B' x) px px'
  :
  B = B' -> px = px' -> rl_V wΓ wB' wx' px' -> rl_V wΓ wB wx px .
Proof.
  move => eB et.
  destruct eB, et.
  have eB : wB = wB' by apply:WTy_hp.
  have et : wx = wx' by apply:WVar_hp.
  destruct eB, et.
  exact.
Qed.

Lemma tp_rT1 Γ A A'  (wΓ : WC Γ) (wA : Γ ⊢ A)(wA' : Γ ⊢ A')
       pA pA'
  :
  A = A' -> pA = pA' -> rl_T wΓ wA'  pA' -> rl_T wΓ wA pA .
Proof.
  move => eB et.
  destruct eB, et.
  have eB : wA = wA' by apply:WTy_hp.
  by rewrite eB.
Qed.
(* Lemma tp_rS2 Γ Δ σ (wΓ : WC Γ)(wΔ wΔ' : WC Δ) (wσ' wσ : Γ ⊢ σ ⇒ Δ) *)
(*       pσ pσ' *)
(*   : *)
(*    pσ = pσ' -> Drl_S wΓ wΔ wσ' pσ' -> rl_S wΓ wΔ' wσ pσ . *)
(* Proof. *)
(*   move => ->. *)
(*   by have -> // : wσ = wσ' by apply:WS_hp. *)
(* Qed. *)
Lemma tp_rS1 Γ Δ σ (wΓ : WC Γ)(wΔ : WC Δ) (wσ' wσ : Γ ⊢ σ ⇒ Δ)
      pσ pσ'
  :
   pσ = pσ' -> rl_S wΓ wΔ wσ' pσ' -> rl_S wΓ wΔ wσ pσ .
Proof.
  move => ->.
  by have -> // : wσ = wσ' by apply:WS_hp.
Qed.

Lemma r_sb_wkT (sΓ sΔ : rC) (sA sB : rT sΔ) (su : rtm sA) (sσ : rS sΓ sΔ)
      (sa : rtm (r_sbT sσ sA)) (sf : rtm (r_rl_ar sa (r_sbt sσ su)) ):
  r_sbT (r_rl_to_ext sf) (r_wkT su sB) = r_sbT sσ sB.
Proof.
  apply:JMeq_eq.
  apply:rTeq => //.
  * move => γ γ' /(@JMeq_eq _ _ _) -> //.
  * move => b.
    simpl.
    apply:JMeq_trans.
    {
      set e := (e in eq_rect_r _ _ e).
               apply:(JMeq_eq_rect_r _ e).
    }
    symmetry.
    apply:(JMeq_eq_rect_r _ ).
  * by move => γ γ' /(@JMeq_eq _ _ _) -> //.
Qed.

Lemma r_sb_wkTm (sΓ sΔ : rC) (sA sB : rT sΔ) (su : rtm sA) (sσ : rS sΓ sΔ)
      (sa : rtm (r_sbT sσ sA)) (sf : rtm (r_rl_ar sa (r_sbt sσ su)) ) (sx : rtm sB):
  r_sbt (r_rl_to_ext sf) (r_wkt su sx) ≅ r_sbt sσ sx.
Proof.
  apply:rtmeq => //.
  + now rewrite r_sb_wkT.
  + by move => γ γ' /(@JMeq_eq _ _ _) -> //.
Qed.

Lemma  r_sb_star sΓ sΔ (sσ : rS sΔ sΓ) : r_sbT sσ r_rl_star = r_rl_star.
Proof.
  apply JMeq_eq.
  apply :rTeq => //.
  intro a.
  clear.
  cbn.
  apply:JMeq_eq_rect_r.
Qed.

Lemma r_sb_to_star sΓ sΔ (st :rtm r_rl_star) (sσ : rS sΔ sΓ)
  : r_sbS sσ (r_rl_to_star (sΓ := sΓ) st) ≅ r_rl_to_star
          (eq_rect _ _ (r_sbt sσ st) _ (r_sb_star sσ)).
Proof.
  apply:rSeq => //=.
  move => γ γ' /(@JMeq_eq _ _ _) -> //.
  set e := r_sb_star  _.
  move:st.
  change (( fun A w =>
            forall
 (st : rtm A),
              t_t st (S sσ γ') ≅ t_t (eq_rect _ rtm (r_sbt sσ st) _ w) γ')
            (r_rl_star) e).
  now destruct e.
Qed.

Lemma r_sb_ar sΓ sΔ  (sσ : rS sΔ sΓ)
      sA (st su : rtm sA)
  :
  r_sbT sσ (r_rl_ar st su) = r_rl_ar (r_sbt sσ st) (r_sbt sσ su).
Proof.
  apply:JMeq_eq.
  apply:rTeq => //=.
  - by move => γ γ' /(@JMeq_eq _ _ _) -> //.
  - move => a.
    cbn.
    clear.
    apply:JMeq_trans; first by apply:JMeq_eq_rect_r.
    apply:JMeq_trans; first by apply:JMeq_eq_rect_r.
    apply:JMeq_trans; first by apply:JMeq_eq_rect_r.
    symmetry.
    apply:JMeq_trans; first by apply:JMeq_eq_rect_r.
    apply:JMeq_trans; first by apply:JMeq_eq_rect_r.
    apply:JMeq_reflh_eq_rect_r.
  - move => γ γ' /(@JMeq_eq _ _ _) => -> //=.
Qed.




Lemma JMeq_t_t Γ (A A' : rT Γ) (t : rtm A) (t' : rtm A') γ  :
  A = A' -> t ≅ t' ->  t_t t γ ≅ t_t t' γ.
destruct 1.
move/(@JMeq_eq _ _ _).
now destruct 1.
Qed.
(* Lemma JMeq_congr_r_rl_ar :  *)
(*   r_rl_ar a b *)
  (* par récurrence sur le type ou la substitution ??
   *)
Fixpoint rl_sbT (Γ Δ : Con) (A : Ty) (σ : sub)
         (wΓ : WC Γ) (wΔ : WC Δ)
         (wA : Δ ⊢ A) (wσ : Γ ⊢ σ ⇒ Δ)
         (* redondant *)
         (* (wAσ := Γ ⊢ A.[σ]T) *)
         (* (wAσ := WTy_sb wΓ wΔ wσ wA) *)
         (sΓ : rC)
         (pA : pT)
         (sσ : rS sΓ (pT_C pA))
         (* (sΔ : rC)(sA : rT sΔ) *)
         (* (rlΔ : rl_C wΔ sΔ) *)
         (rlA : rl_T wΔ wA pA)
         (rlσ : rl_S wΓ wΔ wσ (mkpS sσ)) {struct rlA} :
  rl_T wΓ (WTy_sb wΓ wΔ wσ wA) (mkpT (r_sbT sσ (pT_T pA))) 

with rl_sbt (Γ Δ : Con) (A : Ty) (t : Tm) (σ : sub)
         (wΓ : WC Γ) (wΔ : WC Δ)
         (wA : Δ ⊢ A)(wt : Δ ⊢ t : A) (wσ : Γ ⊢ σ ⇒ Δ)
         (* redondant *)
         (* (wAσ := Γ ⊢ A.[σ]T) *)
         (* (wAσ := WTy_sb wΓ wΔ wσ wA) *)
         (sΓ : rC)
         (pt : pTm)
           (sσ : rS sΓ (pt_C pt))
         (* (rlΔ : rl_C wΔ sΔ) *)
         (* (rlA : rl_T wΔ wA (mkpT ())) *)
         (rlt : rl_t wΔ wA wt pt)
         (rlσ : rl_S wΓ wΔ wσ (mkpS sσ)) {struct rlt}
     : rl_t wΓ (WTy_sb wΓ wΔ wσ wA)
                                         (Wtm_sb wΓ wΔ wσ wt)
                                         (mkpt (r_sbt sσ (pt_t pt)))
with rl_sbV (Γ Δ : Con) (A : Ty) (x : Var) (σ : sub)
         (wΓ : WC Γ) (wΔ : WC Δ)
         (wA : Δ ⊢ A)(wx : WVar Δ A x) (wσ : Γ ⊢ σ ⇒ Δ)
         (* redondant *)
         (* (wAσ := Γ ⊢ A.[σ]T) *)
         (* (wAσ := WTy_sb wΓ wΔ wσ wA) *)
         (sΓ : rC)
         (px : pTm)
           (sσ : rS sΓ (pt_C px))
         (* (rlΔ : rl_C wΔ sΔ) *)
         (* (rlA : rl_T wΔ wA (mkpT ())) *)
         (rlx : rl_V wΔ wA wx px)
         (rlσ : rl_S wΓ wΔ wσ (mkpS sσ)) {struct rlx} :
       rl_t wΓ (WTy_sb wΓ wΔ wσ wA)
                                         (Wtm_sb wΓ wΔ wσ (w_va wx))
                                         (mkpt (r_sbt sσ (pt_t px)))
with rl_sbS (Γ Δ E : Con)   (σ δ : sub)
         (wΓ : WC Γ) (wΔ : WC Δ)
         (wE : WC E)(wδ : Δ ⊢ δ ⇒ E) (wσ : Γ ⊢ σ ⇒ Δ)
         (* redondant *)
         (* (wAσ := Γ ⊢ A.[σ]T) *)
         (* (wAσ := WTy_sb wΓ wΔ wσ wA) *)
         (sΓ : rC)
         (pδ : pS)
           (sσ : rS sΓ (pS_C1 pδ))
         (* (rlΔ : rl_C wΔ sΔ) *)
         (* (rlA : rl_T wΔ wA (mkpT ())) *)
         (rlδ : rl_S wΔ wE wδ pδ)
         (rlσ : rl_S wΓ wΔ wσ (mkpS sσ)) {struct rlδ} :
       rl_S wΓ wE (WS_sb wΓ wΔ wσ wδ)
            (mkpS (r_sbS sσ (pS_S pδ))).

- destruct rlA.
  + cbn.
    move/rl_star:(rl_S_C1 rlσ) => /=.
    have -> // : r_sbT sσ r_rl_star = r_rl_star by apply:r_sb_star.
    
  +  simpl.

     move/rl_sbT:(rlA) => IHA; move/IHA:(rlσ) => {IHA} IHA.
     move/rl_sbt:(r0) => IHt; move/IHt:(rlσ) => {IHt} IHt.
     move/rl_sbt:(r1) => IHu; move/IHu:(rlσ) => {IHu} IHu.
     
     apply:tp_rT1; last first.
     * eapply rl_ar.
       -- apply:(rl_S_C1 rlσ).
       -- apply:IHA.
       -- apply:IHt.
       -- apply:IHu.
     * f_equal.
       apply:r_sb_ar.
     * reflexivity.
     
-  destruct rlt.
   + move/rl_sbV:r.
     apply.
     apply:rlσ.
   + 
     move/rl_sbS:(r2) => IHS; move/IHS:(rlσ) => {IHS} IHS.
     move/rl_sbT:(r1) => IHB.
     move/IHB:(IHS) =>  IHB'.
     move/IHB:(r2) =>  IHB''.

     simpl.
     set e := sbTcomp _ _ _.
     eapply(tp_rTm1 _ (wB' := WTy_sb wΓ wΔ (WS_sb wΓ wΓ0 wσ wσ0) wB)) ; last first.
     * {
         apply:rl_coh; last first.
         - exact:IHS.
         - apply:r1.
         - assumption.
         - apply:(rl_S_C1 rlσ).
       }
     *
       (* move => [:eqT]. *)
       apply:pt_eq1.
       --
         (* abstract :eqT. *)
          symmetry.
          apply:compr_T.
       -- simpl.
          move => eqT.
          (* TODO abstraire comme compr_T *)
          apply:JM_eq_eq_rect.
         apply : rtmeq.
         ++ reflexivity.
         ++ by rewrite eqT.
         ++ by move => γ γ' /(@JMeq_eq _ _ _) -> //.
     * apply:e.
- destruct rlx.
  + 
    inversion rlσ; repeat clear_hprop; repeat (clear_jmsigma; subst).
    repeat (clear_jmsigma; subst).
    simpl.
    apply:tp_rTm1; last first.
    * apply:X0.
    *
      (* move => [: eqT]. *)
      apply:pt_eq1.
      --
        (* abstract:eqT. *)
         (* TODO extraire ce lemme : substitution de star *)
          symmetry.
          {
            apply:JMeq_eq.
            apply:rTeq.
            - reflexivity.
            - by move => γ γ' /(@JMeq_eq _ _ _) -> //.
            - move => a //=.
              apply:JMeq_sym.
              apply:JMeq_eq_rect_r.
            - by move => γ γ' /(@JMeq_eq _ _ _) -> //.
          }
      -- (* TODO abstraire *)
         (* substitution d'un vstar *)
        {
          move => eqT.
          apply:JM_eq_eq_rect.
         apply : rtmeq.
         - reflexivity.
         - now rewrite eqT.
         - by move => γ γ' /(@JMeq_eq _ _ _) -> //.
        }
    * reflexivity.
  + (* vwk *)
    move:(WTy_sb _ _ _ _) => wBσ.
    move:(Wtm_sb _ _ _ _) => wtσ.
    simpl in rlσ.
    move:rlσ.
    (* il faut abstraire sur le pS *)
    remember {| pS_C1 := sΓ; pS_C2 := r_rl_ext su; pS_S := sσ |} as pσ eqn:epσ.
    inversion 1 ; repeat clear_hprop; repeat (clear_jmsigma; subst).
    simpl.
    move/rl_sbV : rlx => IHx.
    simpl in IHx.
      (* sΓ0 = sΔ *)
    have e : sΓ0 = sΔ by apply:rl_hpC; eassumption.
    subst.
    have e : sΓ1 = sΓ by move/(π_eq_pSC):H4.
    subst.
    have e : sA0 = sA by apply:π_eq_pTη; apply:rl_hpT; eassumption.
    subst.
    have e : su0 = su by apply:π_eq_ptη; apply:rl_hpt; eassumption.
    subst.
    have e : sσ = r_rl_to_ext sf  by apply:π_eq_pSη.
    subst.
    simpl.
    (*
    (* TODO extraire ce lemme : substitution d'un weakening au niveau des types *)

*)
    (* have eqT :   r_sbT (r_rl_to_ext sf) (r_wkT su sB) = r_sbT sσ0 sB by apply:r_sb_wkT. *)


    apply:tp_rTm1; last first.
    * apply:IHx.
      apply:X3.
    *
      {
        (* TODO abstraire : substitution d'un weakening *)
        apply:pt_eq1.
        - apply:r_sb_wkT.
        - move => h.
          apply:JM_eq_eq_rect.
          apply:r_sb_wkTm.
      }
    * apply:wkT_ext.

  + move:(WTy_sb _ _ _ _) => wBσ.
    move:(Wtm_sb _ _ _ _) => wtσ.
    move:rlσ.
    simpl.
    (* il faut abstraire sur le pS *)
    remember {| pS_C1 := sΓ; pS_C2 := r_rl_ext su; pS_S := sσ |} as pσ eqn:epσ.
    inversion 1 ; repeat clear_hprop; repeat (clear_jmsigma; subst).
    have e : sΓ0 = sΔ by apply:rl_hpC; eassumption.
    subst.
    have e : sΓ1 = sΓ by move/(π_eq_pSC):H4.
    subst.
    have e : sA0 = sA by apply:π_eq_pTη; apply:rl_hpT; eassumption.
    subst.
    have e : su0 = su by apply:π_eq_ptη; apply:rl_hpt; eassumption.
    subst.
    have e : sσ = r_rl_to_ext sf  by apply:π_eq_pSη.
    subst.
    apply:tp_rTm1; last first.
    * apply:X4.
    * {
        apply:pt_eq1.
        - apply:r_sb_wkT.
        - simpl.
          move => eqT.
          apply:JM_eq_eq_rect.
          apply:rtmeq => //.
          * now rewrite eqT.
          * by move => γ γ' /(@JMeq_eq _ _ _) -> //.
      }
    * apply:wkT_ext.
  + move:(WTy_sb _ _ _ _) => wBσ.
    move:(Wtm_sb _ _ _ _) => wtσ.
    move:rlσ.
    simpl.
    (* il faut abstraire sur le pS *)
    remember {| pS_C1 := sΓ; pS_C2 := r_rl_ext su; pS_S := sσ |} as pσ eqn:epσ.
    inversion 1 ; repeat clear_hprop; repeat (clear_jmsigma; subst).
    have e : sΓ0 = sΔ by apply:rl_hpC; eassumption.
    subst.
    have e : sΓ1 = sΓ by move/(π_eq_pSC):H4.
    subst.
    have e : sA0 = sA by apply:π_eq_pTη; apply:rl_hpT; eassumption.
    subst.
    have e : su0 = su by apply:π_eq_ptη; apply:rl_hpt; eassumption.
    subst.
    have e : sσ = r_rl_to_ext sf  by apply:π_eq_pSη.
    subst.
    apply:tp_rTm1; last first.
    * apply:X5.
    * {
        (* TODO extraire ce lemme *)
        have eT :   r_sbT (r_rl_to_ext sf) (r_rl_ar (r_rl_v1 su) (r_wkt su su))
                    = r_rl_ar sa (r_sbt sσ0 su).
        {
          apply:JMeq_eq.
          apply:rTeq => //.
          * move => γ γ' /(@JMeq_eq _ _ _) -> //.
          * move => b.
            simpl.
            apply:JMeq_trans.
            {
              set e := (e in eq_rect_r _ _ e).
                       apply:(JMeq_eq_rect_r _ e).
            }
            apply:JMeq_trans; first by apply:(JMeq_eq_rect_r _ ).
            apply:JMeq_trans; first by apply:(JMeq_eq_rect_r _ ).
            symmetry.
            apply:JMeq_trans; first by apply:(JMeq_eq_rect_r _ ).
            apply:JMeq_trans; first by apply:(JMeq_eq_rect_r _ ).
            now apply:JMeq_trans; first by apply:(JMeq_reflh_eq_rect_r).
          * by move => γ γ' /(@JMeq_eq _ _ _) -> //.
          }

        apply:pt_eq1.
        (* TODO extraire ce lemme *)
        (* - apply:JM_eq_eq_rect. *)
        (*   exact: eT. *)
        -  apply:JM_eq_eq_rect.
          apply:rtmeq => //.
          * now rewrite eT.
          * by move => γ γ' /(@JMeq_eq _ _ _) -> //.
      }
    * simpl.
      by rewrite wkT_ext wkt_ext.
- destruct rlδ.
  + simpl.
    simpl in rlσ.
    move/rl_sbt:r0 => IHt; move/IHt : rlσ => {IHt} IHt.
    simpl in IHt.
    apply:tp_rS1; last first.
    * apply :(rl_to_star ).
      -- apply:rl_t_C.
         apply:IHt.
      -- 
          apply:tp_rTm1; last by apply:IHt.
         ++ reflexivity.
         ++ unshelve eapply pt_eq1.
            ** symmetry; apply:r_sb_star.
            ** apply:eq_rect_inv.
    * cbn.
      f_equal.
      clear.
      apply:JMeq_eq.
      apply:rSeq => //=.
      move => γ γ' /(@JMeq_eq _ _ _) -> //.
      cbn.
      (* TODO factoriser avec r_sb_to_star *)
      cbn in sσ.
      set e := r_sb_star  _.
      move:st.
      change (( fun A w =>
                  forall
                    (st : rtm A),
                    t_t st (S sσ γ') ≅ t_t (eq_rect _ rtm (r_sbt sσ st) _ w) γ')
                (r_rl_star) (esym (esym e))).
      now destruct e.
  + move/rl_sbS:(rlδ) => IHS; move/IHS:(rlσ) => {IHS} IHS.
    move/rl_sbt:(r3) => IHa; move/IHa:(rlσ) => {IHa} IHa.
    move/rl_sbt:(r4) => IHf; move/IHf:(rlσ) => {IHf} IHf.
    have eqT :
      r_rl_ar (eq_rect_r rtm (r_sbt sσ sa) (compr_T sσ sσ0 sA)) (r_sbt (r_sbS sσ sσ0) su) =
      r_sbT sσ (r_rl_ar sa (r_sbt sσ0 su)).
    {
      symmetry.
      etrans.
      apply:r_sb_ar.
      { apply: (@JMeq_congr4 _ _ _ _ (@r_rl_ar _  )).
        - symmetry.
          apply:compr_T.
        - symmetry.
          apply:JMeq_eq_rect_r.
        - apply:compr_Tm.
      }
    }
    apply:tp_rS1; last first.
    * econstructor.
      -- apply:rl_S_C1.
         apply:IHS.
      -- apply:rl_S_C2.
         apply:IHS.
      -- simpl.
         eassumption.
      -- simpl.
         eassumption.
      -- exact:IHS.
      -- simpl.
         simpl in IHa.
         apply:tp_rTm1 ; last by apply:IHa.
         ++ symmetry. apply:sbTcomp; eassumption.
         ++ unshelve eapply pt_eq1.
            ** apply:compr_T.
            ** apply:eq_rect_inv.
      -- simpl in IHf.
         apply:tp_rTm1; last by apply:IHf.
         ++ symmetry.
            (* TODO factoriser : j'ai déjà fait cette preuve *)
            f_equal.
            ** apply:sbTcomp; eassumption.
            ** apply:sbTmcomp; eassumption.
         ++ apply:pt_eq1.
            (* **  apply:eqT. *)
            ** apply eq_rect_inv.
    * simpl.
      f_equal.
      clear.
      apply:JMeq_eq.
      apply:rSeq => //=.
      move => γ γ' /(@JMeq_eq _ _ _) -> //=.
      move:eqT.
      set (e :=  (compr_T _ _ _)) => eqT.
      simpl in *.
      apply:JMeq_from_eq.
      apply:JMeq_Σ.

      {
        f_equal.
        symmetry.
        apply:JMeq_eq.
        apply:JMeq_trans.
        {
          set z := eq_rect _ _ _ _ _.
          apply:(JMeq_t_t (t:=z) γ'); last first.
        - apply:JMeq_eq_rect.
        - apply:compr_T.
        }
        constructor.
      }
      {
        apply:JMeq_trans; last first.
        {
          set z := (eq_rect (r_sbT sσ (r_rl_ar sa (r_sbt sσ0 su))) rtm (r_sbt sσ sf)
                            (r_rl_ar
                               (eq_rect (r_sbT sσ (r_sbT sσ0 sA)) rtm (r_sbt sσ sa) (r_sbT (r_sbS sσ sσ0) sA) (esym e))
                               (r_sbt (r_sbS sσ sσ0) su)) (esym eqT)).
          symmetry.
          apply:(JMeq_t_t (t := z) γ'); last first.
          - apply:JMeq_eq_rect.
          - exact:eqT.
        }
        by constructor.
      }
      (* d'ou viennent tous ces trucs ?? *)
      Unshelve.
       apply:(Wtm_sb (A := star)) => //=.
       exact:wΓ0.
       assumption.
       assumption.
       {
         erewrite <- sbTcomp.
         by apply:Wtm_sb;[ | exact :wΓ0 | | ] ; eassumption.
         all:eassumption.
       }
       {
         erewrite <- sbTcomp.
         erewrite <- sbTmcomp.
         by apply:(Wtm_sb (A := ar A.[σ0]T a u.[σ0]t));[ | exact :wΓ0 | | ] ; eassumption.
           all:eassumption.
       }      
       {
         erewrite <- sbTcomp.
         by apply:WTy_sb;[ | exact :wΓ0 | | ] ; eassumption.
           all:eassumption.
       }
       {
         apply:Wtm_sb; cycle 2.
         (* on aruait ptet pu faire comme ça pour les preuves précédentes ? *)
         apply:WS_sb ;[ |  |eassumption | ] ; eassumption.
         all:eassumption.
       }
Qed.

Lemma r_wk_star sΓ (sA : rT sΓ) (su : rtm sA) :  r_wkT su r_rl_star = r_rl_star.
Proof.
  reflexivity.
Qed.
Fixpoint rl_wkT
         (Γ  : Con) (A : Ty) (u : Tm)
         (B : Ty)
         (wΓ : WC Γ) (wA : Γ ⊢ A)(wu : Γ ⊢ u : A)
         (wB : Γ ⊢ B) 
         (wBe : ext Γ A u ⊢ wkT B)
         
         sΓ (sA : rT sΓ) (su : rtm sA)
         (sB : rT sΓ)

         (rA : rl_T wΓ wA (mkpT sA))
         (ru : rl_t wΓ wA wu (mkpt su))
         (rB : rl_T wΓ wB (mkpT sB))

          {struct rB} :
  rl_T (w_ext wΓ wA wu) wBe  (mkpT (r_wkT su sB)) 

with rl_wkt
       (Γ  : Con) (A : Ty) (u : Tm)
         (B : Ty) (t  : Tm)

         (wΓ : WC Γ) (wA : Γ ⊢ A)(wu : Γ ⊢ u : A)
         (wB : Γ ⊢ B) (wt : Γ ⊢ t : B)
         (wBe : ext Γ A u ⊢ wkT B) (wte : ext Γ A u ⊢ wkt t : wkT B)

         sΓ (sA : rT sΓ) (su : rtm sA)
         (sB : rT sΓ)(st : rtm sB)

         (rA : rl_T wΓ wA (mkpT sA))
         (ru : rl_t wΓ wA wu (mkpt su))
         (rB : rl_T wΓ wB (mkpT sB))
         (rt : rl_t wΓ wB wt (mkpt st))
         
          {struct rt}
     : rl_t (w_ext wΓ wA wu) wBe wte (mkpt (r_wkt su st))
with rl_wkV 
       (Γ  : Con) (A : Ty) (u : Tm)
         (B : Ty) (x  : Var)

         (wΓ : WC Γ) (wA : Γ ⊢ A)(wu : Γ ⊢ u : A)
         (wB : Γ ⊢ B) (wx : WVar Γ B x)
         (wBe : ext Γ A u ⊢ wkT B) (wxe : WVar (ext Γ A u) (wkT B) (vwk x) )

         sΓ (sA : rT sΓ) (su : rtm sA)
         (sB : rT sΓ)(sx : rtm sB)

         (rA : rl_T wΓ wA (mkpT sA))
         (ru : rl_t wΓ wA wu (mkpt su))
         (rB : rl_T wΓ wB (mkpT sB))
         (rx : rl_V wΓ wB wx (mkpt sx))
          {struct rx}
     : rl_V (w_ext wΓ wA wu) wBe wxe (mkpt (r_wkt su sx))
with rl_wkS
       (Γ  : Con) (A : Ty) (u : Tm)
         (Δ : Con) (σ  : sub)

         (wΓ : WC Γ) (wA : Γ ⊢ A)(wu : Γ ⊢ u : A)
         (wΔ : WC Δ) (wσ : Γ ⊢ σ ⇒ Δ)
         (wσe : ext Γ A u ⊢ wkS σ ⇒ Δ)

         sΓ (sA : rT sΓ) (su : rtm sA)
         sΔ (sσ : rS sΓ sΔ)

         (rA : rl_T wΓ wA (mkpT sA))
         (ru : rl_t wΓ wA wu (mkpt su))
         (rσ : rl_S wΓ wΔ wσ (mkpS sσ))
     : rl_S  (w_ext wΓ wA wu) wΔ wσe (mkpS (r_wkS su sσ)).


  (* - admit. *)
  (*   destruct rΓ. *)
  (* + constructor. *)
  (*   apply:JMeq_eq. *)
  (*   apply :rTeq => //. *)
  (*   * move => γ γ' /(@JMeq_eq _ _ _) -> //. *)
  (*     cbn. *)
- have rΓ := rl_t_C ru.
  have rCe : rl_C (w_ext wΓ wA wu) (r_rl_ext su) by constructor; assumption.
  (* TODO faire ça dans la preuve de rl_sb* *)
  
  move:rB.
  remember {| pT_C := sΓ; pT_T := sB |} as pB eqn:eB.
  destruct 1.
  + move/π_eq_pTC:(eB) => /= e.
  
    subst sΓ0.
    move/π_eq_pTη:(eB) => /= e.
    subst sB.
    simpl in wBe.
    apply:tp_rT1; last by apply:rl_star; eassumption.
    all:reflexivity.

  + 
    move/rl_wkT:(rA) => I ; move/I:(ru)=> {I rl_wkT} rl_wkT.
    (* move/rl_wkt:(rA) => I ; move/I:(ru)=> {I rl_wkt} rl_wkt. *)
    move/rl_wkt:(ru)=> { rl_wkt} rl_wkt.
    move/π_eq_pTC:(eB) => /= e.
    subst sΓ0.
    move/π_eq_pTη:(eB) => /= e.
    subst sB.
    simpl in wBe.
    inversion wBe; subst.
    rename H3 into wA0e.
    rename H4 into wte.
    rename H5 into wue.
    have e : wBe = w_ar wA0e wte wue by apply:WTy_hp.
    subst.
    move/rl_wkT:(rB) ;  move/(_ wA0e) =>  IHB.     
    move/rl_wkt:(r0) ;move /(_ wA0e wte )=>  IHt.
    move/rl_wkt:(r1);move/(_ wA0e wue )=>  IHu. 
    (* move/rl_wkt:(r0);move /(_ wA0e wte rB)=>  IHt. *)
    (* move/rl_wkt:(r1);move/(_ wA0e wue rB)=>  IHu.  *)
    apply:tp_rT1; last first.
    -- apply:rl_ar.
       ++ eassumption.
       ++ eassumption.
       ++ exact:IHt.
       ++ exact:IHu.
    -- cbn.
       
       (* ??? pourquoi ça fait réflexivity marche alors que le lemme abstrait
r_wk_ar ne marche pas en reflexivity ????? *)
       reflexivity.
    -- reflexivity.
- have rΓ := rl_t_C ru.
  (* have rCe : rl_C (w_ext wΓ wA wu) (r_rl_ext su). *)
    (* by constructor; assumption. *)
  (* TODO faire ça dans la preuve de rl_sb* *)
  
  move:rt.
  remember {| pt_C := sΓ; pt_T := sB; pt_t := st |} as pB eqn:et.
  destruct 1.
  +
    (* move/rl_wkT:(ru)=> {rl_wkT} rl_wkT. *)
    (* move/rl_wkt:(ru)=> {rl_wkt} rl_wkt. *)
    (* move/rl_wkV:(ru)=> {rl_wkV} rl_wkV. *)
    move/rl_wkT:(rA) => I ; move/I:(ru)=> {I rl_wkT} rl_wkT.
    move/rl_wkt:(rA) => I ; move/I:(ru)=> {I rl_wkt} rl_wkt.
    move/rl_wkV:(rA) => I ; move/I:(ru)=> {I rl_wkV} rl_wkV.
    have e : sΓ0 = sΓ by move/π_eq_ptC:(et).
    subst.
    have e:   sA0 = sB by move/π_eq_ptTη:(et) .
    subst.
    have e:   sx = st by move/π_eq_ptη:(et) .
    subst.
    move/rl_wkV:(wx) => IHx.
    apply:tp_rTm1; last first.
    * apply:rl_va.
      apply:IHx; last by apply:r.
      assumption.
    * reflexivity.
    * reflexivity.
  + move/rl_wkT:(ru)=> {rl_wkT} rl_wkT.
    move/rl_wkS:(ru)=> {rl_wkS} rl_wkS.
    (* move/rl_wkV:(ru)=> {rl_wkV} rl_wkV. *)
    have e : sΓ0 = sΓ by move/π_eq_ptC:(et).
    subst.
    have e:   sB = r_sbT sσ sB0 by move/π_eq_ptTη:(et) .
    subst.
    rename sB0 into sB.
    have e:   st = r_rl_coh sB sσ by move/π_eq_ptη:(et) .
    subst.
    apply:tp_rTm1; last first.
    * apply:rl_coh; last first; last by constructor; eassumption.
      -- apply:rl_wkS; eassumption.
      -- eassumption.
      -- assumption.
    * reflexivity.
    * apply:wkT_wkS; eassumption.
      (* TODO : wkT B.[σ]T = B.[wkS σ]T *)
- have rΓ := rl_t_C ru.
  move:rx.
  remember {| pt_C := sΓ; pt_T := sB; pt_t := sx |} as px eqn:ex.
  destruct 1.
  +  move/π_eq_ptC:(ex)=> /= ?; subst sΓ.
     move/π_eq_ptTη:(ex)=> /= ?; subst sB.
     move/π_eq_ptη:(ex)=> /= ?; subst sx.
     apply:tp_rV1; last first.
     * apply:rl_vwk; last first.
       -- constructor.
       -- assumption.
       -- eassumption.
       -- assumption.
       -- assumption.
     * reflexivity.
     * reflexivity.
  + move/π_eq_ptC:(ex)=> /= ?; subst sΓ.
    move/π_eq_ptTη:(ex)=> /= ?; subst sB.
    move/π_eq_ptη:(ex)=> /= ?; subst sx.
     apply:tp_rV1; last first.
     {
      apply:rl_vwk; last first.
      {
       apply:rl_wkV; last by apply:rx.
          all:eassumption.
      }
      all:eassumption.
     }
     all:reflexivity.
  + move/π_eq_ptC:(ex)=> /= ?; subst sΓ.
    move/π_eq_ptTη:(ex)=> /= ?; subst sB.
    move/π_eq_ptη:(ex)=> /= ?; subst sx.
     apply:tp_rV1; last first.
     {
      apply:rl_vwk; last first.
       constructor.
       all:eassumption.
     }
     all:reflexivity.
  + move/π_eq_ptC:(ex)=> /= ?; subst sΓ.
    move/π_eq_ptTη:(ex)=> /= ?; subst sB.
    move/π_eq_ptη:(ex)=> /= ?; subst sx.
     apply:tp_rV1; last first.
     {
      apply:rl_vwk; last first.
       constructor.
       all:eassumption.
     }
     all:reflexivity.
- have rΓ := rl_t_C ru.
  move:rσ.
  remember {| pS_C1 := sΓ; pS_C2 := sΔ; pS_S := sσ |} as pσ eqn:eσ.
  destruct 1.
  + move/π_eq_pSC:(eσ) => /= ?; subst sΓ0.
    move/π_eq_pSC2:(eσ) => /= ?; subst sΔ.
    move/π_eq_pS:(eσ) => /= ?; subst sσ.
    apply:tp_rS1; last first.
    * apply:rl_to_star.
      -- constructor; eassumption.
      -- apply: tp_rTm1; last first.
         ++ apply:rl_wkt; last first.
            ** apply:r0.
            ** constructor => //.
            ** eassumption.
            ** assumption.
         ++ reflexivity.
         ++ reflexivity.
    * reflexivity.
  + move/π_eq_pSC:(eσ) => /= ?; subst sΓ0.
    move/π_eq_pSC2:(eσ) => /= ?; subst sΔ.      
    move/π_eq_pS:(eσ) => /= ?; subst sσ.          
    rename A0 into B.
    have rTbiz :   rl_T wΓ wAσ {| pT_C := sΓ; pT_T := r_sbT sσ0 sA0 |}.
    {
      apply:tp_rT1; last by apply:(rl_sbT (pA := mkpT sA0)); eassumption.
      reflexivity.
      reflexivity.
    }


    apply:tp_rS1; last first.                   
    * apply:rl_to_ext.
      -- constructor; eassumption.
      -- eassumption.
      -- eassumption.
      -- eassumption.
      -- apply:rl_wkS; last first.
         ++ apply:rσ.
         ++ assumption.
         ++ assumption.
      -- apply:tp_rTm1; last first.
         ++ apply:rl_wkt; last first.
            ** exact:r3.
            ** assumption.
            ** eassumption.
            ** assumption.
         ++ reflexivity.
         ++ symmetry; apply:wkT_wkS ; eassumption.
      --  apply:tp_rTm1; last first.
         ++ apply:rl_wkt; last first.
            ** exact:r4.
            ** constructor => //.
               apply:tp_rTm1; last by apply:(rl_sbt (pt := mkpt su0)); eassumption.
               all:reflexivity.
            ** eassumption.
            ** assumption.
         ++ reflexivity.
         ++ cbn.
            erewrite wkT_wkS.
            erewrite wkt_wkS.
            reflexivity.
            all:eassumption.
    * reflexivity.
      
(* aucune idée d'ou viennent ces preuves *)
Unshelve.

all:try assumption.
all: try repeat constructor => //.
all: try (erewrite <- wkt_wkS; try eassumption).
all: try (erewrite <- wkT_wkS; try eassumption).
all: try by apply:WTm_wk.
all: try by apply:WTy_wk.
all: try by apply:WS_wk.
by apply:(WTm_wk _ (B := star)).
by apply:(WTm_wk _ (B := ar B.[σ]T a u0.[σ]t)).
Qed.

Lemma rl_V_T  (Γ : Con)  (A : _) (x : Var)
              (wΓ : WC Γ)(wA : Γ ⊢ A) (wx : WVar Γ A x) 
              px
              (rlt : rl_V wΓ wA wx px)
     : rl_T wΓ wA (mkpT (pt_T px)).
  destruct rlt => /=.
  - by repeat constructor.
  - apply:rl_wkT;eassumption.
  - apply:rl_wkT;eassumption.
  - repeat constructor => //=.
    + apply:rl_wkT; eassumption.
    + apply:rl_wkt; eassumption.
Qed.

Lemma rl_V_Tη  (Γ : Con)  (A : _) (x : Var)
              (wΓ : WC Γ)(wA : Γ ⊢ A) (wx : WVar Γ A x) 
              (sΓ : rC)(sA : rT sΓ) (sx: rtm sA)
              (px := mkpt sx)
              (rlt : rl_V wΓ wA wx px)
     : rl_T wΓ wA (mkpT sA).
  change (mkpT sA) with (mkpT (pt_T px)).
  apply:rl_V_T;eassumption.
Qed.


Lemma rl_t_T  (Γ : Con)  (A : _) t
              (wΓ : WC Γ)(wA : Γ ⊢ A) (wt : Γ ⊢ t : A)
              pt 
              (rlt : rl_t wΓ wA wt pt)
     : rl_T wΓ wA (mkpT (pt_T pt)).
  (* change (mkpT sA) with (mkpT (pt_T pt)). *)
  destruct rlt => /=.
  - apply: rl_V_Tη ; eassumption.
  - apply:tp_rT1; last first.
    + apply:rl_sbT; eassumption.
    + reflexivity.
    + reflexivity.
Qed.
Lemma rl_t_Tη  (Γ : Con)  (A : _) t
              (wΓ : WC Γ)(wA : Γ ⊢ A) (wt : Γ ⊢ t : A)
              (sΓ : rC)(sA : rT sΓ) (st: rtm sA)
              (pt := mkpt st)
              (rlt : rl_t wΓ wA wt pt)
     : rl_T wΓ wA (mkpT sA).
  change (mkpT sA) with (mkpT (pt_T pt)).
  apply:rl_t_T; eassumption.
Qed.


End OmegaGroupoid.
