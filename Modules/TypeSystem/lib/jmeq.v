(* File copied from the standard library, but we use uip instead of JMeq_eq *)
From Modules Require Import Axioms.
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** John Major's Equality as proposed by Conor McBride

  Reference:

  [McBride] Elimination with a Motive, Proceedings of TYPES 2000,
  LNCS 2277, pp 197-216, 2002.

*)

Set Implicit Arguments.


(* Definition in the standard library *)
(* Inductive JMeq (A:Type) (x:A) : forall B:Type, B -> Type := *)
(*     JMeq_refl : JMeq x x. *)

(* I invert a and B because otherwise typeclass inference fails to find isntances of
reflexivity and symmetry (Cf complements) *)
(* Definition JMeq (A:Type)(B:Type) (a:A)  (b:B) := *)
Definition JMeq (A:Type) (a:A) (B:Type) (b:B) :=
  { e : A = B & eq_rect _ _ a _ e = b }.

Definition JMeq_refl (A : Type) (x : A) : JMeq x x := existT _ eq_refl eq_refl.

Arguments JMeq_refl {A x} , [A] x.


(* Elimination scheme *)
Lemma JMeq_elim:
  forall (A : Type) (x : A) (P : forall (B : Type) (b : B), JMeq x b -> Type),
  P A x (JMeq_refl x) -> forall (B : Type) (b : B) (e : JMeq x b), P B b e.
Proof.
  intros A x P  Px B b [e1 e2].
  destruct e1.
  simpl in *.
  now destruct e2.
Defined.

(* Elimination scheme *)
(* Lemma JMeq_elim: *)
(*   forall (A : Type) (x : A) (P : forall (B : Type) (b : B), JMeq x b -> Type), *)
(*   P A x (JMeq_refl x) -> forall (B : Type) (b : B) (e : JMeq x b), P B b e. *)
(* Proof. *)
(*   intros A x P  Px B b [e1 e2]. *)
(*   destruct e1. *)
(*   simpl in *. *)
(*   now destruct e2. *)
(* Defined. *)
(* Set Elimination Schemes. *)


Hint Resolve JMeq_refl.

Definition JMeq_hom {A : Type} (x y : A) := JMeq x y.

Lemma JMeq_sym : forall (A B:Type) (x:A) (y:B), JMeq x y -> JMeq y x.
Proof. 
intros; destruct H using JMeq_elim; trivial.
(* Defined instead of Qed *)
Defined.

Hint Immediate JMeq_sym.

Lemma JMeq_trans :
 forall (A B C:Type) (x:A) (y:B) (z:C), JMeq x y -> JMeq y z -> JMeq x z.
Proof.
destruct 2 using JMeq_elim; trivial.
Qed.

(* Original version *)
(* Axiom JMeq_eq : forall (A:Type) (x y:A), JMeq x y -> x = y. *)
Lemma JMeq_eq : forall (A:Type) (x y:A), JMeq x y -> x = y.
Proof.
  intros A x y .
  assert ( h : forall (A B:Type) (y:A) (x:B)(e : A = B), JMeq x y -> x = eq_rect _ _ y _ e).
  {
    clear.
    intros A B y x e e'.
    destruct e' using JMeq_elim.
    now rewrite (uip e eq_refl).
  }
  apply (h _ _ _ _ eq_refl).
Defined.

Lemma JMeq_ind : forall (A:Type) (x:A) (P:A -> Prop),
  P x -> forall y, JMeq x y -> P y.
Proof.
intros A x P H y H'; case JMeq_eq with (1 := H'); trivial.
Qed.

Lemma JMeq_rec : forall (A:Type) (x:A) (P:A -> Set),
  P x -> forall y, JMeq x y -> P y.
Proof.
intros A x P H y H'; case JMeq_eq with (1 := H'); trivial.
Qed.

Lemma JMeq_rect : forall (A:Type) (x:A) (P:A->Type),
  P x -> forall y, JMeq x y -> P y.
Proof.
intros A x P H y H'; case JMeq_eq with (1 := H'); trivial.
Qed.

Lemma JMeq_ind_r : forall (A:Type) (x:A) (P:A -> Prop),
   P x -> forall y, JMeq y x -> P y.
Proof.
intros A x P H y H'; case JMeq_eq with (1 := JMeq_sym H'); trivial.
Qed.

Lemma JMeq_rec_r : forall (A:Type) (x:A) (P:A -> Set),
   P x -> forall y, JMeq y x -> P y.
Proof.
intros A x P H y H'; case JMeq_eq with (1 := JMeq_sym H'); trivial.
Qed.

Lemma JMeq_rect_r : forall (A:Type) (x:A) (P:A -> Type),
   P x -> forall y, JMeq y x -> P y.
Proof.
intros A x P H y H'; case JMeq_eq with (1 := JMeq_sym H'); trivial.
Qed.

Lemma JMeq_congr :
 forall (A:Type) (x:A) (B:Type) (f:A->B) (y:A), JMeq x y -> f x = f y.
Proof.
intros A x B f y H; case JMeq_eq with (1 := H); trivial.
Qed.


