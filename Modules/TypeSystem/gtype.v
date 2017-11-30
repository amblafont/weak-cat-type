Require Import ssreflect ssrfun ssrbool .

From Modules Require Import Syntax HomotopicalEquality lib.
Set Bullet Behavior "Strict Subproofs".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

CoInductive GType :=
  Gtyp { ob : Type ;
         hom : ob -> ob -> GType }.

Notation "∣ A ∣" := (ob A) (at level 99).




CoFixpoint G_of_T (T : Type) : GType.
  unshelve econstructor.
  - exact:T.
  - move => a b.
    apply:G_of_T.
    exact: (a =h b).
Defined.
(* Notation "∣ X ∣" := (ob X). *)


