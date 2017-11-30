(* -*- coq-prog-name: "coqtop"; -*- *)

Require Import ssreflect ssrfun ssrbool .


Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "x ..1" := (projT1 x) (at level 2).
Notation "x ..2" := (projT2 x) (at level 2).
Notation "x ,Σ y" := (existT _ x y)  (at level 70).

Lemma transport (A : Type) (x : A) (P : A -> Type) (y : A)(e : x = y)  (Px : P x) : P y.
Proof.
  apply:eq_rect e => //=.
Defined.

Ltac etrans := eapply trans_eq.

Definition is_center (A : Type) (a : A) :=
  forall ( a' : A),  a' = a.

(*
(* Could also be defined this way *)
Definition JMeq_alt (A : Type) (a : A) (B : Type) (b : B) :=
  (A ,Σ a) = (B ,Σ b).


(* JMeq is not stronger than JMeq_alt. (actually they are equivalent) *)
Lemma JMeq_alt_JMeq (A : Type) (a : A) (B : Type) (b : B) (e : JMeq_alt a b) :  a ≅ b.
  apply:(JM_projT2 e).
Defined.

Lemma JMeq_JMeq_alt (A : Type) (a : A) (B : Type) (b : B) (e : JMeq a b) : JMeq_alt a b.
  now destruct e.
Defined.

(* We require funext, although we believe it is possible to avoid it in our
current formalization  *)
Axiom funext : forall (A : Type) (B : A -> Type) (f g : forall a, B a),
    (forall a, f a = g a) -> f = g.

(* The following axiom that we use is equivalent to uip *)
Check (JMeq_eq : forall (A:Type) (x y:A), x ≅ y -> x = y).

(* uip implies JMeq_eq *)
Lemma uip_JMeq_eq (uip : forall (A : Type) (x y : A) (e e' : x = y) , e = e') :
  forall (A:Type) (x y:A), x ≅ y -> x = y.
Proof.
  move => A x y.
  suff h : forall (A B:Type) (y:A) (x:B)(e : A = B), x ≅ y -> x = transport e y.
  by apply :(h _ _ _ _ erefl).
  clear -uip.
  move => A B y x e e'.
  move:e.
  destruct e' => e'.
  by rewrite (uip _ _ _ e' (erefl B)).
Qed.
(* No assumption is made here *)
Print Assumptions uip_JMeq_eq.

(* JMeq_eq implies uip *)
Lemma uip (A : Type) (x y : A) (e e' : x = y) : e = e'.
  apply JMeq_eq.
  destruct e.
  destruct e'.
  reflexivity.
Qed.

Print Assumptions uip.

*)







  


