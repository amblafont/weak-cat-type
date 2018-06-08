This folder is a new attempt to formalize the syntax of Brunerie Type Theory
(including all contexts, not only those which are not contractible). I follow
Ambrus' systematic suggestion of translating an Inductive-Inductive to an indexed recursive,
which consists in fully annoting the untyped syntax (theses annotations give more
induction hypothesis), and defining the well-formed judgements not as a inductive datatype but
by recursion on the untyped syntax, and the same for the functional relation (Cf slides TYPES 2018).

The Inductive-Inductive part I am translating is the following :
the usual Con, Ty : Con -> U, Tm : ..
but also:
- isContr : Con → U
- isCTy : ∀ Γ , isContr Γ → Ty Γ → U
- isCTm : ..
- isCSub : ..

This is because the proof by induction that types are weak omega groupoids works with these
additionnals predicate isCTm, isCSub, isCTy (you can check the definition of a model of this type theory
in FullBruneriePrimProj).

All these files depend on files that I stole from coq hott project, that are in the folder FromHottLibPrimProj
( I use Primitive Projection because it makes Coq accepts quicklier the functional relation).

Here is the order of the compiled files :

FullBruneriePrimProj : extrinsic syntax of Brunerie TT, definition of a model and of the functional
  relation underlying the non dependent recursor (with the proof that it is hprop)
FullBrunerieStuff : somme tactics
FullBrunerieSuite : the functional relation is inhabited here. What is misssing : show that the functional
  relation is stable under weakening and subsitution (these are the admits of this file)
  
  
Once we show that types are weak omega groupoids, we can try to state the fundamental functor from types 
to weak omega groupoids and then asks that it is a quillen equivalence.
Then, any finite context of Brunerie Type Theory induces a weak omega groupoid, in particular the context
x : *, f : x = x which should yields the circle.

But I am far from having theses definitions working.




