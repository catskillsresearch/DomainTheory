module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.unfold
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.fold
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.head
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.tail
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.push
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.diag
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.mapBody
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.mapOp
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.mapMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.iterProdIso_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.head_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.tail_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.Arg

@[expose] public section

/-!
# Exercise 5.11 (Scott 1981, PRG-19, §5) — `D^∞` as stacks; stack combinators

Regarding `D^∞ = iterSys D` (Exercise 3.16) as (bottomless) *stacks* of elements of `D`, Scott asks
for combinators with the obvious meanings

```
head : D^∞ → D,      tail : D^∞ → D^∞,      push : D × D^∞ → D^∞,
```

then for `diag : D → D^∞` with `diag(x) = ⟨x⟩ₙ` (every component equal to `x`), defined by the
recursion `diag(x) = push(x, diag(x))`, and finally a combinator

```
map : (D → D)^∞ × D → D^∞,      map(⟨fₙ⟩, x) = ⟨fₙ(x)⟩ₙ.
```

We build `head`, `tail`, `push` from the order-isomorphism `iterProdIso : D^∞ ≅ D × D^∞` of
Exercise 3.16 (so `unfold = ofIso iterProdIso`, `fold = ofIso iterProdIso.symm`), and obtain the
**stack laws**

* `head_push`  : `head(push(x, s)) = x`,
* `tail_push`  : `tail(push(x, s)) = s`,
* `push_head_tail` : `push(head z, tail z) = z`,

together with the component readings `head z = z₀` and `(tail z)ₙ = zₙ₊₁`.

`diag` and `map` are defined as least fixed points (Theorem 4.1/4.2); for `diag` we prove Scott's
emphasised property that **all** components equal `x` (`component_diag`), and for `map` that the
`n`-th component is `fₙ(x)` (`component_map`).

The only classical input is what is inherited from `iterProdIso` / `fixMap` and the project's
`Element.ext` machinery.
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise511

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)

/-! ### `unfold`/`fold` from the isomorphism `D^∞ ≅ D × D^∞`. -/




/-! ### The stack combinators. -/






/-! ### `diag : D → D^∞`, the constant stack `⟨x⟩ₙ`, by recursion `diag(x) = push(x, diag(x))`. -/


/-! ### `map : (D → D)^∞ × D → D^∞`, `map(⟨fₙ⟩, x) = ⟨fₙ(x)⟩ₙ`, by recursion. -/




end DomainTheory.NeighbourhoodSystems.Exercise511
