Set Implicit Arguments.
Unset Strict Implicit.

Axiom eqh : forall (A:Type) (x:A) , A -> Type.

Notation "x =h y" := (eqh x y)  (at level 70).

Axiom reflh : forall {A : Type} (x : A), x =h x.

Axiom Fib : Type -> Type.
Axiom unit_Fib : Fib unit.
Axiom prod_Fib : forall {A : Type} {B : A -> Type}  ( fibA : Fib A ) 
                   ( fibB : forall {a : A} , Fib (B a) ) , Fib (forall (a : A) , B a).

Axiom sigma_Fib : forall {A : Type} {B : A -> Type}  ( fibA : Fib A ) 
                   ( fibB : forall {a : A} , Fib (B a) ) , Fib { a : A & B a}.
Axiom eq_Fib : forall {A : Type} (fibA : Fib A) (x : A) (y : A), Fib (x =h y).

Axiom  Jh : forall {A : Type} ( fibA : Fib A )
    {x : A}
    (P : forall {y : A},  y =h x -> Type) 
    ( fibP : forall (y : A) (w : y =h x) , Fib (P w) ) ,
    P (reflh _) -> forall {y : A}  (w : y =h x) , P w.

Axiom βJh :  
  forall {A : Type} ( fibA : Fib A )
    {x : A}
    (P : forall {y : A},  y =h x -> Type) 
    ( fibP : forall (y : A) (w : y =h x) , Fib (P w) ) 
    (r : P (reflh _)) ,
      Jh fibA  fibP  r (reflh _) = r.

