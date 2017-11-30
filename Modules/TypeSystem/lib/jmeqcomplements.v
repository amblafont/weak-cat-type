Require Import ssreflect ssrfun ssrbool .
Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Unset Strict Implicit.
Unset Printing Implicit Defensive.
(*


Complements about JMeq that are not in the standard library



*)
From Modules Require Import jmeq stuff Axioms HomotopicalEquality.


Notation "x ≅ y" := (JMeq  x  y) (at level 70, y at next level, no associativity).
(* So that symmetry and reflexivity work with
JMeq *)
(*
Require Import Coq.Classes.RelationClasses.
Impossible de faire marcher ce truc!!!
TODO: demadner à Gaetan Nicolas ou Matthieu

Instance Reflexive_JMeq (A : Type) :
  (Reflexive (A := A) (fun a b => JMeq a b )) := @JMeq_refl A.


(* Parameter (B : Type). *)
Parameter (R : forall A, A -> A -> Prop).
(* Parameter (Q : B -> B -> Prop). *)
   Typeclasses eauto := debug.
(* Instance ReflexiveR (A : Type) : *)
(*   Reflexive (A := A) (@R A). *)
(* Admitted. *)
  Set Typeclasses Debug Verbosity 100.
  Hint Resolve Reflexive_JMeq : typeclass_instances.
  Hint Extern 1 => apply Reflexive_JMeq : typeclass_instances.
Goal (forall A (a : A), a ≅ a).
  intros.
  Check (JMeq a).
  change ((fun x y => @JMeq A x A y) a a).
  set 
  rewrite lock
  reflexivity.
  pattern a.
  reflexivity.
       reflexivity.
Goal (forall A (a : A), R a a).
  reflexivity.
Existing Instance JMeq_refl : Reflexive.
*)



Lemma transport2 (A : Type)  (P : A -> Type)(Q : forall (a:A), P a -> Type)
      (x : A) (p : P x)(y : A)(q : P y)(e : x = y)(e' : p ≅ q)  (Px : Q _ p) : Q _ q.
Proof.
  destruct e.
  apply JMeq_eq in e'.
  by destruct e'.
Defined.


(* Heteregoneous equality that we use systematically *)

Lemma JM_projT2  (A : Type) (P : A -> Type) (a b : {x : A & P x})
      (e : a = b) : a..2 ≅ b..2.
Proof.
  now destruct e.
Qed.


(*
Replaces hypothesis of the form (x ,Σ y) = (x ,Σ y')
with y = y'
 *)
Ltac clear_jmsigma :=
  match goal with
  | x : (?C ,Σ ?D) = (_ ,Σ ?E) |- _ =>
     (apply JM_projT2,JMeq_eq in x; simpl in x)
    (* have {x} x : D = E by apply : JMeq_eq;apply:(JM_projT2  x) *)
  | x : ?C = ?C |- _ => clear x
  end.

Lemma JMeq_eq_refl A (x  : A) : JMeq_eq (JMeq_refl (x:=x)) = erefl.
  apply:uip.
Qed.
Lemma JMeq_eq_rect (A : Type) (x : A) (P : A -> Type) (Px : P x) (y : A) (w : x= y) :
      eq_rect x P Px y w ≅ Px.
  now destruct w.
Defined.
Lemma JMeq_eq_rect_r (A : Type) (x : A) (P : A -> Type) (Px : P x) (y : A) (w : y= x) :
      @eq_rect_r A x P Px y w ≅ Px.
  now destruct w.
Defined.

Lemma JM_eq_eq_rect_r (A : Type) (x : A) (P : A -> Type) (Px : P x) (y : A) (w : y= x) Py :
    Px ≅ Py ->
      @eq_rect_r A x P Px y w = Py.
  destruct w.
  now move/(@JMeq_eq _ _ _).
Qed.
Lemma JM_eq_eq_rect (A : Type) (x : A) (P : A -> Type) (Px : P x) (y : A) (w : x= y) Py :
    Px ≅ Py ->
      @eq_rect A x P Px y w = Py.
  destruct w.
  now move/(@JMeq_eq _ _ _).
Qed.

Lemma JMeq_transport (A : Type) (x : A) (P : A -> Type) (Px : P x) (y : A) (w : x= y) :
      @transport A x P y w Px ≅ Px.
  now destruct w.
Qed.
Lemma JMeq_transport2  (A : Type)  (P : A -> Type)(Q : forall (a:A), P a -> Type)
      (x : A) (p : P x)(y : A)(q : P y)(e : x = y)(e' : p ≅ q)  (Px : Q _ p) :
  transport2 e e' Px ≅ Px.
Proof.
  destruct e.
  simpl.
  by destruct (JMeq_eq e').
Qed.

Lemma JMeq_from_eq (A : Type) (x y : A) : x = y -> x ≅ y.
  by destruct 1.
Qed.

Lemma JMeq_congr3 (A : Type) (B : A -> Type)(D: Type) (C : forall a : A, B a -> D)
      (x x' : A) (b : B x) (b'  : B x') : x = x' -> b ≅ b' -> C x b = C x' b'.
destruct 1.
move => eb.
apply JMeq_eq in eb.
now destruct eb.
Qed.
Lemma JMeq_congr4 (A : Type) (B : A -> Type) (C : forall a : A, B a -> Type)
      (D : Type) (E : forall a b (c : @C a b), D)
      (x x' : A) (b : B x) (b'  : B x')
      (c : C _ b) (c' : C _ b')
  : x = x' -> b ≅ b' -> c ≅ c' -> E  _ _ c =  E _ _ c'.
destruct 1.
move => eb ec.
apply JMeq_eq in eb.
destruct eb.
apply JMeq_eq in ec.
now destruct ec.
Qed.

Lemma JMeq_Σ (A : Type) (P : A -> Type) (x x': A) (y : P x) (y' : P x') :
  x = x' -> y ≅ y' -> x ,Σ y = (x' ,Σ y').
destruct 1.
move/(@JMeq_eq _ _ _).
now destruct 1.
Qed.

Lemma JMeq_eqh (A B : Type) (x y : A) (x' y':B) (e : A = B) (ex : x ≅ x')
      (ey: y ≅ y') : (x =h y) = (x' =h y').
  destruct e.
  apply JMeq_eq in ex.
  apply JMeq_eq in ey.
  by destruct ex, ey.
Qed.
Lemma JMeq_reflh_eq_rect_r (A : Type) (x : A) (P : A -> Type) (Px : P x) (y : A) (w : y= x) :
      reflh (@eq_rect_r A x P Px y w) ≅ reflh Px.
  now destruct w.
Qed.