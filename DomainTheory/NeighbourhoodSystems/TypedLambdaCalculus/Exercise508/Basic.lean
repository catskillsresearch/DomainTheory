module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Dom

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Poly
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.CL
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Sbody
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Smap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Ielem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Kelem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Selem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.bracket

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



/-! ### Domains as data, and the function-domain constructor. -/


/-! ### The three combinators as elements of the appropriate function domains. -/




/-! ### Syntax of `λ`-bodies with one free variable, and of variable-free combinator expressions. -/



/-! ### Bracket abstraction. -/

end DomainTheory.NeighbourhoodSystems.Exercise508
