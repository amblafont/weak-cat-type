
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Class PreSyntax  :=
  {
    Con : Type;
    Ty : Type;
    Tm : Type;
    sub : Type;
    }.
Class Syntax {S : PreSyntax} :=
  {
    WC : Con -> Type;
    WTy : Con -> Ty -> Type;
    Wtm : Con -> Ty -> Tm -> Type;
    WS : Con -> Con -> sub -> Type }.
Reserved Notation "Gamma ⊢"
  (at level 68,  no associativity,
   format "Gamma  ⊢ ").

Reserved Notation "Gamma ⊢ A : B"
  (at level 68, A at level 99, no associativity,
   format "Gamma  ⊢  A  :  B").
Reserved Notation "Gamma ⊢ A"
  (at level 68, A at level 99, no associativity,
   format "Gamma  ⊢  A").

Reserved Notation "Gamma ⊢ A ⇒ B"
  (at level 68, A at level 99, no associativity,
   format "Gamma  ⊢  A  ⇒  B").

Reserved Notation "Gamma ⊢_v A : B"
  (at level 68, A at level 99, no associativity,
   format "Gamma  ⊢_v  A  :  B").

Notation "Gamma ⊢ " := (WC Gamma )  : wf_scope.
Notation "Gamma ⊢ A" := (WTy Gamma A)  : wf_scope.
Notation "Gamma ⊢ s : A" := (Wtm Gamma A s) : wf_scope.
Notation "Gamma ⊢  s  ⇒ Delta" :=
  (WS Gamma Delta s)
    : wf_scope.

Open Scope wf_scope.

(* Reserved Notation "sigma ∘ tau"  (at level 56, left associativity). *)

Reserved Notation "s .[ sigma ]T" (at level 2, sigma at level 200, left associativity,
   format "s .[ sigma ]T" ).
Reserved Notation "s .[ sigma ]oT" (at level 2, sigma at level 200, left associativity,
   format "s .[ sigma ]oT" ).

Reserved Notation "s .[ sigma ]wT" (at level 2, sigma at level 200, left associativity,
   format "s .[ sigma ]wT" ).

Reserved Notation "s .[ sigma ]t" (at level 2, sigma at level 200, left associativity,
   format "s .[ sigma ]t" ).

Reserved Notation "s .[ sigma ]V" (at level 2, sigma at level 200, left associativity,
   format "s .[ sigma ]V" ).

Reserved Notation "sigma ∘ delta"  (at level 40, left associativity).
