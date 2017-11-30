(* More axioms are in HomotopicalEquality *)

Set Implicit Arguments.

Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* We require funext, although we believe it is possible to avoid it in our
current formalization  *)
Axiom funext : forall (A : Type) (B : A -> Type) (f g : forall a, B a),
    (forall a, f a = g a) -> f = g.

Axiom uip : forall (A : Type) (x y : A) (e e' : x = y) , e = e'.