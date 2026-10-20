/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

/-!
# Exercise 5.8 (Scott 1981, PRG-19, §5) — combinatory completeness

> **(For combinator nuts.)** Table 5.5 was meant to show how combinators could be defined in terms
> of `λ`-expressions. Can the tables be turned to show that with enough combinators available, every
> `λ`-expression can be defined by combining combinators, using `σ(τ)` as the *only* mode of
> combination?

The answer is **yes**: this is the classical theorem of *combinatory completeness* (bracket
abstraction). With the three combinators

```
I = λx.x,        K = λx,y.x,        S = λf,g,x. f(x)(g(x))
```

available, every `λ`-abstraction can be eliminated in favour of pure application of combinators. We
formalise this in the neighbourhood-system framework as follows.

* `Dom` packages a token type with its neighbourhood system, and `Dom.arrow A B` is the function
  domain `(A → B)` (its carrier is `ApproximableMap A.sys B.sys`).
* `I`, `K`, `S` are realised as concrete elements (`Ielem`, `Kelem`, `Selem`) of the appropriate
  function domains, with their **value equations** `Ielem_apply`, `Kelem_apply`, `Selem_apply`
  proved through the project's `curry`/`eval`/projection API.
* `Poly X A` is the intrinsically-typed syntax of `λ`-bodies with **one** free variable of type `X`:
  the variable itself, closed constants (any element — "enough combinators available"), and
  application. Its denotation `Poly.denote t : |X| → |A|` is the open term as a function of the
  variable, i.e. the body whose abstraction `λx.t` we wish to express.
* `CL A` is the syntax of **variable-free** combinator expressions: constants and application only
  (`σ(τ)` is the *only* mode of combination). Its denotation `CL.denote : |A|` is a single element.
* `bracket : Poly X A → CL (X.arrow A)` is **bracket abstraction**: it turns an open body `t` into a
  *closed* combinator expression, using only application together with the constants `I`, `K`, `S`
  and the constants already occurring in `t` — exactly Scott's challenge.

The completeness theorem is `bracket_spec`:

```
(bracket t).denote, applied to x, equals t.denote x       for every x.
```

i.e. the variable-free combinator expression `bracket t` denotes precisely the function `λx.t`. By
induction on `t` this is driven by the three combinator identities, turning the table around as Scott
asks.

Everything is **data**; the combinators are built from `idMap`, `curry`, `proj`, `eval` and are
choice-free.
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise508

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-! ### A generic round-trip for the function-space representation. -/

variable {α β γ : Type*}

/-! ### The `S` combinator as an approximable map.

`S = λf, g, x. f(x)(g(x))`. We build the uncurried body
`Sbody(⟨⟨F, G⟩, x⟩) = eval(eval(F, x), eval(G, x))`
out of projections, pairing and `eval`, then curry twice. -/

variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}

/-- The uncurried body of `S`: with `F : 𝒟ₓ → (𝒟ₐ → 𝒟_b)`, `G : 𝒟ₓ → 𝒟ₐ`, `x : 𝒟ₓ`,
`Sbody⟨⟨F, G⟩, x⟩ = (F x)(G x)`, expressed using only `proj`, `pair` and `eval`. -/
def Sbody (Vx : NeighborhoodSystem αx) (Va : NeighborhoodSystem αa) (Vb : NeighborhoodSystem αb) :
    ApproximableMap
      (prod (prod (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)) Vx) Vb :=
  (evalMap Va Vb).comp
    (paired
      ((evalMap Vx (funSpace Va Vb)).comp
        (paired
          ((proj₀ (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)).comp
            (proj₀ (prod (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)) Vx))
          (proj₁ (prod (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)) Vx)))
      ((evalMap Vx Va).comp
        (paired
          ((proj₁ (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)).comp
            (proj₀ (prod (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)) Vx))
          (proj₁ (prod (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)) Vx))))

/-- `S = λf, g, x. f(x)(g(x))`, the curried form
`(𝒟ₓ → (𝒟ₐ → 𝒟_b)) → ((𝒟ₓ → 𝒟ₐ) → (𝒟ₓ → 𝒟_b))`. -/
def Smap (Vx : NeighborhoodSystem αx) (Va : NeighborhoodSystem αa) (Vb : NeighborhoodSystem αb) :
    ApproximableMap (funSpace Vx (funSpace Va Vb))
      (funSpace (funSpace Vx Va) (funSpace Vx Vb)) :=
  curry (curry (Sbody Vx Va Vb))

/-! ### Domains as data, and the function-domain constructor. -/

/-- A *domain*: a token type together with its neighbourhood system. Bundling lets us build an
intrinsically-typed syntax of combinator terms. We work over `Type` (universe `0`), which covers all
the concrete domains of these lectures (`N`, `T`, `C`, …) and their products/function spaces. -/
structure Dom where
  /-- The token type. -/
  carrier : Type
  /-- The neighbourhood system on `carrier`. -/
  sys : NeighborhoodSystem carrier

/-- The function domain `(A → B)`; its carrier is `ApproximableMap A.sys B.sys` and its system is the
function space `funSpace A.sys B.sys`. -/
abbrev Dom.arrow (A B : Dom) : Dom := ⟨ApproximableMap A.sys B.sys, funSpace A.sys B.sys⟩

/-! ### The three combinators as elements of the appropriate function domains. -/

/-- `I = λx.x` as an element of `(X → X)`. -/
def Ielem (X : Dom) : (X.arrow X).sys.Element := toFilter (idMap X.sys)

/-- `K = λx, y.x` as an element of `(A → (X → A))`. -/
def Kelem (A X : Dom) : (A.arrow (X.arrow A)).sys.Element := toFilter (curry (proj₀ A.sys X.sys))

/-- `S = λf, g, x. f(x)(g(x))` as an element of
`((X → (A → B)) → ((X → A) → (X → B)))`. -/
def Selem (X A B : Dom) :
    ((X.arrow (A.arrow B)).arrow ((X.arrow A).arrow (X.arrow B))).sys.Element :=
  toFilter (Smap X.sys A.sys B.sys)

/-! ### Syntax of `λ`-bodies with one free variable, and of variable-free combinator expressions. -/

/-- `Poly X A`: an open term of type `A` with a single free variable of type `X`. Constructors:
the variable, a closed constant (any element of any domain — "enough combinators available"), and
application. This is the syntax of `λ`-bodies whose abstraction we want to eliminate. -/
inductive Poly (X : Dom) : Dom → Type 1 where
  | var : Poly X X
  | con {A : Dom} (c : A.sys.Element) : Poly X A
  | app {A B : Dom} (f : Poly X (A.arrow B)) (a : Poly X A) : Poly X B

/-- `CL A`: a **variable-free** combinator expression of type `A`. The only constructors are
constants and application, so application (`σ(τ)`) is the sole mode of combination. -/
inductive CL : Dom → Type 1 where
  | con {A : Dom} (c : A.sys.Element) : CL A
  | app {A B : Dom} (f : CL (A.arrow B)) (a : CL A) : CL B

/-- The denotation of an open term: the body as a function of its free variable. -/
def Poly.denote {X : Dom} : {A : Dom} → Poly X A → X.sys.Element → A.sys.Element
  | _, .var, x => x
  | _, .con c, _ => c
  | _, .app f a, x => (toApproxMap (f.denote x)).toElementMap (a.denote x)

/-- The denotation of a variable-free combinator expression: a single element. -/
def CL.denote : {A : Dom} → CL A → A.sys.Element
  | _, .con c => c
  | _, .app f a => (toApproxMap f.denote).toElementMap a.denote

/-! ### Bracket abstraction. -/

/-- **Bracket abstraction.** Turn an open body `t` (a `λ`-body with one free variable) into a
*variable-free* combinator expression denoting `λx.t`, using only application and the combinators
`I`, `K`, `S` together with the constants already occurring in `t`:

* `[x] x        = I`
* `[x] c        = K(c)`           (`c` a constant / closed term)
* `[x] (f a)    = S([x]f)([x]a)`.
-/
def bracket {X : Dom} : {A : Dom} → Poly X A → CL (X.arrow A)
  | _, .var => .con (Ielem X)
  | _, .con c => .app (.con (Kelem _ X)) (.con c)
  | _, .app f a => .app (.app (.con (Selem X _ _)) (bracket f)) (bracket a)
end DomainTheory.NeighbourhoodSystems.Exercise508
