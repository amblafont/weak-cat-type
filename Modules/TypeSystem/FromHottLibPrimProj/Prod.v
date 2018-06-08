(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about cartesian products *)

(* Require Import HoTT.Basics. *)
(* Require Import Types.Empty Types.Unit. *)
Require Import Modules.TypeSystem.FromHottLibPrimProj.Notations.
Require Import Modules.TypeSystem.FromHottLibPrimProj.Overture.
Require Import Modules.TypeSystem.FromHottLibPrimProj.PathGroupoids.
Require Import Modules.TypeSystem.FromHottLibPrimProj.Contractible.
Require Import Modules.TypeSystem.FromHottLibPrimProj.Equivalences.
Require Import Modules.TypeSystem.FromHottLibPrimProj.Trunc.
Local Open Scope path_scope.

Generalizable Variables X A B f g n.

Scheme prod_ind := Induction for prod Sort Type.
Arguments prod_ind {A B} P f p.

(** ** Unpacking *)

(** Sometimes we would like to prove [Q u] where [u : A * B] by writing [u] as a pair [(fst u ; snd u)]. This is accomplished by [unpack_prod]. We want tight control over the proof, so we just write it down even though is looks a bit scary. *)

Definition unpack_prod `{P : A * B -> Type} (u : A * B) :
  P (fst u, snd u) -> P u
  := match u with (a , b) => idmap end.

Arguments unpack_prod / .

(** Now we write down the reverse. *)
Definition pack_prod `{P : A * B -> Type} (u : A * B) :
  P u -> P (fst u, snd u)
  := match u with (a , b) => idmap end.

Arguments pack_prod / .

(** ** Eta conversion *)

Definition eta_prod `(z : A * B) : (fst z, snd z) = z
  := match z with (a , b) => 1 end.

Arguments eta_prod / .

(** ** Paths *)

(** With this version of the function, we often have to give [z] and [z'] explicitly, so we make them explicit arguments. *)
Definition path_prod_uncurried {A B : Type} (z z' : A * B)
  (pq : (fst z = fst z') * (snd z = snd z'))
  : (z = z').
Proof.
  destruct z as [z1 z2] , z' as [z1' z2'].

  cbn in pq.
  (* change ((fst z, snd z) = (fst z', snd z')). *)
  case (fst pq). case (snd pq).
  reflexivity.
Defined.

(** This is the curried one you usually want to use in practice.  We define it in terms of the uncurried one, since it's the uncurried one that is proven below to be an equivalence. *)
Definition path_prod {A B : Type} (z z' : A * B) :
  (fst z = fst z') -> (snd z = snd z') -> (z = z')
  := fun p q => path_prod_uncurried z z' (p,q).

(** This version produces only paths between pairs, as opposed to paths between arbitrary inhabitants of product types.  But it has the advantage that the components of those pairs can more often be inferred. *)
Definition path_prod' {A B : Type} {x x' : A} {y y' : B}
  : (x = x') -> (y = y') -> ((x,y) = (x',y'))
  := fun p q => path_prod (x,y) (x',y') p q.

(** Now we show how these things compute. *)

Definition ap_fst_path_prod {A B : Type} {z z' : A * B}
  (p : fst z = fst z') (q : snd z = snd z') :
  ap fst (path_prod _ _ p q) = p.
Proof.
  destruct z as [z1 z2] , z' as [z1' z2'].
  cbn in p,q.
  destruct p, q.
  reflexivity.
Defined.

Definition ap_snd_path_prod {A B : Type} {z z' : A * B}
  (p : fst z = fst z') (q : snd z = snd z') :
  ap snd (path_prod _ _ p q) = q.
Proof.
  destruct z as [z1 z2] , z' as [z1' z2'].
  cbn in p,q.
  destruct p, q.
  reflexivity.
Defined.

Definition eta_path_prod {A B : Type} {z z' : A * B} (p : z = z') :
  path_prod _ _(ap fst p) (ap snd p) = p.
Proof.
  destruct p,z.
  reflexivity.
Defined.

Definition ap_path_prod {A B C : Type} (f : A -> B -> C)
           {z z' : A * B} (p : fst z = fst z') (q : snd z = snd z')
: ap (fun z => f (fst z) (snd z)) (path_prod _ _ p q)
  = ap011 f p q.
Proof.
  destruct z, z'; simpl in *; destruct p, q; reflexivity.
Defined.

(** Now we show how these compute with transport. *)

(*
Lemma transport_path_prod_uncurried {A B} (P : A * B -> Type) {x y : A * B}
      (H : (fst x = fst y) * (snd x = snd y))
      (Px : P x)
: transport P (path_prod_uncurried _ _ H) Px
  = transport (fun x => P (x, snd y))
              (fst H)
              (transport (fun y => P (fst x, y))
                         (snd H)
                         Px).
Proof.
  destruct x, y, H; simpl in *.
  path_induction.
  reflexivity.
Defined.

Definition transport_path_prod {A B} (P : A * B -> Type) {x y : A * B}
           (HA : fst x = fst y)
           (HB : snd x = snd y)
           (Px : P x)
: transport P (path_prod _ _ HA HB) Px
  = transport (fun x => P (x, snd y))
              HA
              (transport (fun y => P (fst x, y))
                         HB
                         Px)
  := transport_path_prod_uncurried P (HA, HB) Px.

Definition transport_path_prod'
           {A B} (P : A * B -> Type)
           {x y : A}
           {x' y' : B}
           (HA : x = y)
           (HB : x' = y')
           (Px : P (x,x'))
: transport P (path_prod' HA HB) Px
  = transport (fun x => P (x, y'))
              HA
              (transport (fun y => P (x, y))
                         HB
                         Px)
  := @transport_path_prod _ _ P (x, x') (y, y') HA HB Px.
*)

(** This lets us identify the path space of a product type, up to equivalence. *)
Global Instance isequiv_path_prod {A B : Type} {z z' : A * B}
: IsEquiv (path_prod_uncurried z z') | 0.
Proof.
  unshelve refine (BuildIsEquiv _ _ _
            (fun r => (ap fst r, ap snd r))
            eta_path_prod
            _
            _).
  - intros [p q].
    apply path_prod'.
    exact (ap_fst_path_prod p q).
    exact (ap_snd_path_prod p q).
  - destruct z as [x y], z' as [x' y'].
    intros [p q]; simpl in p, q.
    destruct p, q; reflexivity.
Defined.


Definition equiv_path_prod {A B : Type} (z z' : A * B)
  : (fst z = fst z') * (snd z = snd z')  <~>  (z = z')
  := BuildEquiv _ _ (path_prod_uncurried z z') _.

(** Path algebra *)

(** Composition.  The next three lemma are displayed equations in section 2.6 of the book, but they have no numbers so we can't put them into [HoTTBook.v]. *)
Definition path_prod_pp {A B : Type} (z z' z'' : A * B)
           (p : fst z = fst z') (p' : fst z' = fst z'')
           (q : snd z = snd z') (q' : snd z' = snd z'')
: path_prod z z'' (p @ p') (q @ q') = path_prod z z' p q @ path_prod z' z'' p' q'.
Proof.
  destruct z, z', z''; simpl in *; destruct p, p', q, q'.
  reflexivity.
Defined.

(** Associativity *)
Definition path_prod_pp_p  {A B : Type} (u v z w : A * B)
           (p : fst u = fst v) (q : fst v = fst z) (r : fst z = fst w)
           (p' : snd u = snd v) (q' : snd v = snd z) (r' : snd z = snd w)
: path_prod_pp u z w (p @ q) r (p' @ q') r'
  @ whiskerR (path_prod_pp u v z p q p' q') (path_prod z w r r')
  @ concat_pp_p (path_prod u v p p') (path_prod v z q q') (path_prod z w r r')
  = ap011 (path_prod u w) (concat_pp_p p q r) (concat_pp_p p' q' r')
    @ path_prod_pp u v w p (q @ r) p' (q' @ r')
    @ whiskerL (path_prod u v p p') (path_prod_pp v z w q r q' r').
Proof.
  destruct u, v, z, w; simpl in *; destruct p, p', q, q', r, r'.
  reflexivity.
Defined.

(** Inversion *)
Definition path_prod_V {A B : Type} (u v: A * B)
           (p : fst u = fst v)
           (q : snd u = snd v)
  : path_prod v u p^ q^ = (path_prod u v p q)^.
Proof.
  destruct u, v; simpl in *; destruct p, q.
  reflexivity.
Defined.

(** ** Transport *)

Definition transport_prod {A : Type} {P Q : A -> Type} {a a' : A} (p : a = a')
  (z : P a * Q a)
  : transport (fun a => P a * Q a) p z  =  (p # (fst z), p # (snd z))
  := match z with (za , zb) =>  match p with idpath => 1 end end.

(** ** Functorial action *)

Definition functor_prod {A A' B B' : Type} (f:A->A') (g:B->B')
  : A * B -> A' * B'
  := fun z => (f (fst z), g (snd z)).

Definition ap_functor_prod {A A' B B' : Type} (f:A->A') (g:B->B')
  (z z' : A * B) (p : fst z = fst z') (q : snd z = snd z')
  : ap (functor_prod f g) (path_prod _ _ p q)
  = path_prod (functor_prod f g z) (functor_prod f g z') (ap f p) (ap g q).
Proof.
  destruct z as [a b]; destruct z' as [a' b'].
  simpl in p, q. destruct p, q. reflexivity.
Defined.

(** ** Equivalences *)

Global Instance isequiv_functor_prod `{IsEquiv A A' f} `{IsEquiv B B' g}
: IsEquiv (functor_prod f g) | 1000.
Proof.
  refine (BuildIsEquiv
            _ _ (functor_prod f g) (functor_prod f^-1 g^-1)
            (fun z => path_prod' (eisretr f (fst z)) (eisretr g (snd z))
                      @ eta_prod z)
            (fun w => path_prod' (eissect f (fst w)) (eissect g (snd w))
                      @ eta_prod w)
            _).
  intros [a b]; simpl.
  unfold path_prod'.
  rewrite !concat_p1.
  rewrite ap_functor_prod.
  rewrite !eisadj.
  reflexivity.
Defined.

Definition equiv_functor_prod `{IsEquiv A A' f} `{IsEquiv B B' g}
  : A * B <~> A' * B'.
Proof.
  exists (functor_prod f g).
  exact _. (* i.e., search the context for instances *)
Defined.

Definition equiv_functor_prod' {A A' B B' : Type} (f : A <~> A') (g : B <~> B')
  : A * B <~> A' * B'.
Proof.
  exists (functor_prod f g).
  exact _.
Defined.

Notation "f *E g" := (equiv_functor_prod' f g) : equiv_scope.

Definition equiv_functor_prod_l {A B B' : Type} (g : B <~> B')
  : A * B <~> A * B'
  := 1 *E g.

Definition equiv_functor_prod_r {A A' B : Type} (f : A <~> A')
  : A * B <~> A' * B
  := f *E 1.

(** ** Symmetry *)

(** This is a special property of [prod], of course, not an instance of a general family of facts about types. *)

Definition equiv_prod_symm (A B : Type) : A * B <~> B * A
  := BuildEquiv
       _ _ _
       (BuildIsEquiv
          (A*B) (B*A)
          (fun ab => (snd ab, fst ab))
          (fun ba => (snd ba, fst ba))
          (fun p => match p with (a , b) => 1 end)
          (fun p => match p with (a , b) => 1 end)
          (fun p => match p with (a , b) => 1 end)
          ).

(** ** Associativity *)

(** This, too, is a special property of [prod], of course, not an instance of a general family of facts about types. *)
Definition equiv_prod_assoc (A B C : Type) : A * (B * C) <~> (A * B) * C
  := BuildEquiv
       _ _ _
       (BuildIsEquiv
          (A * (B * C)) ((A * B) * C)
          (fun abc => ((fst abc, fst (snd abc)), snd (snd abc)))
          (fun abc => (fst (fst abc), (snd (fst abc), snd abc)))
          (fun p => match p with (a , b , c) => 1 end)
          (fun p => match p with (a , (b , c)) => 1 end)
          (fun p => match p with (a , (b , c) ) => 1 end)).
          (* (fun _ => 1) *)
          (* (fun _ => 1) *)
          (* (fun _ => 1)). *)

(** ** Unit and annihilation *)

(*
Definition prod_empty_r X : X * Empty <~> Empty
  := (BuildEquiv _ _ snd _).

Definition prod_empty_l X : Empty * X <~> Empty
  := (BuildEquiv _ _ fst _).

Definition prod_unit_r X : X * Unit <~> X.
Proof.
  refine (BuildEquiv _ _ fst _).
  simple refine (BuildIsEquiv _ _ _ (fun x => (x,tt)) _ _ _).
  - intros x; reflexivity.
  - intros [x []]; reflexivity.
  - intros [x []]; reflexivity.
Defined.

Definition prod_unit_l X : Unit * X <~> X.
Proof.
  refine (BuildEquiv _ _ snd _).
  simple refine (BuildIsEquiv _ _ _ (fun x => (tt,x)) _ _ _).
  - intros x; reflexivity.
  - intros [[] x]; reflexivity.
  - intros [[] x]; reflexivity.
Defined.
*)

(** ** Universal mapping properties *)

(** Ordinary universal mapping properties are expressed as equivalences of sets or spaces of functions.  In type theory, we can go beyond this and express an equivalence of types of *dependent* functions.  Moreover, because the product type can expressed both positively and negatively, it has both a left universal property and a right one. *)

(* First the positive universal property. *)
(*
Global Instance isequiv_prod_ind `(P : A * B -> Type)
: IsEquiv (prod_ind P) | 0
  := BuildIsEquiv
       _ _
       (prod_ind P)
       (fun f x y => f (x, y))
       (fun _ => 1)
       (fun _ => 1)
       (fun _ => 1).

Definition equiv_prod_ind `(P : A * B -> Type)
  : (forall (a : A) (b : B), P (a, b)) <~> (forall p : A * B, P p)
  := BuildEquiv _ _ (prod_ind P) _.

(* The non-dependent version, which is a special case, is the currying equivalence. *)
Definition equiv_uncurry (A B C : Type)
  : (A -> B -> C) <~> (A * B -> C)
  := equiv_prod_ind (fun _ => C).

(* Now the negative universal property. *)
Definition prod_coind_uncurried `{A : X -> Type} `{B : X -> Type}
  : (forall x, A x) * (forall x, B x) -> (forall x, A x * B x)
  := fun fg x => (fst fg x, snd fg x).

Definition prod_coind `(f : forall x:X, A x) `(g : forall x:X, B x)
  : forall x, A x * B x
  := prod_coind_uncurried (f, g).

Global Instance isequiv_prod_coind `(A : X -> Type) (B : X -> Type)
: IsEquiv (@prod_coind_uncurried X A B) | 0
  := BuildIsEquiv
       _ _
       (@prod_coind_uncurried X A B)
       (fun h => (fun x => fst (h x), fun x => snd (h x)))
       (fun _ => 1)
       (fun _ => 1)
       (fun _ => 1).

Definition equiv_prod_coind `(A : X -> Type) (B : X -> Type)
  : ((forall x, A x) * (forall x, B x)) <~> (forall x, A x * B x)
  := BuildEquiv _ _ (@prod_coind_uncurried X A B) _.
*)

(** ** Products preserve truncation *)

Global Instance trunc_prod `{IsTrunc n A} `{IsTrunc n B} : IsTrunc n (A * B) | 100.
Proof.
  generalize dependent B; generalize dependent A.
  simple_induction n n IH; simpl; (intros A ? B ?).
  { exists (center A, center B).
    intros z; apply path_prod; apply contr. }
  { intros x y.
    exact (trunc_equiv _ (equiv_path_prod x y)). }
Defined.

Global Instance contr_prod `{CA : Contr A} `{CB : Contr B} : Contr (A * B) | 100
  := @trunc_prod -2 A CA B CB.

(** ** Decidability *)

(*
Global Instance decidable_prod {A B : Type}
       `{Decidable A} `{Decidable B}
: Decidable (A * B).
Proof.
  destruct (dec A) as [x1|y1]; destruct (dec B) as [x2|y2].
  - exact (inl (x1,x2)).
  - apply inr; intros [_ x2]; exact (y2 x2).
  - apply inr; intros [x1 _]; exact (y1 x1).
  - apply inr; intros [x1 _]; exact (y1 x1).
Defined.
*)
