/-ai
This module gathers and re-exports the body of the while recursion, the loop operator, the least fixed point of that operator, and the approximable map denoted by that fixed point.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise512.bodyMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise512.Wop
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise512.whileFix
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise512.whileMap

@[expose] public section

/-!
# Exercise 5.12 (Scott 1981, PRG-19, §5) — the `while` combinator

Given a domain `D`, a *predicate* `p : D → T` (into the truth domain of Example 1.2) and an
*update* `f : D → D`, Scott's `while`-loop

```
while p do f
```

is the function `D → D` that keeps applying `f` while `p` holds. It is characterised as the least
solution `w : D → D` of the recursion

```
w(x) = cond(p(x), w(f(x)), x).
```

We realise this *semantically* inside the approximable-map framework: the right-hand side, read as
a function of the unknown `w`, is an approximable operator

```
Wop : (D → D) → (D → D),   Wop(w) = λx. cond(p(x), w(f(x)), x),
```

built from the conditional `cond` of Exercise 3.26, evaluation `eval`, the projections, pairing and
composition. The loop is then `whileFix = fixElement Wop`, the least fixed point of `Wop`
(Theorem 4.1), and `whileMap = toApproxMap whileFix : D → D` the approximable function it denotes.

We prove:

* `whileMap_rec` — the defining recursion `w(x) = cond(p(x), w(f(x)), x)`;
* `whileMap_true`  — if `p(x) = true`  then `w(x) = w(f(x))` (loop body runs);
* `whileMap_false` — if `p(x) = false` then `w(x) = x` (loop exits);
* `whileMap_bot`   — if `p(x) = ⊥`     then `w(x) = ⊥` (divergent test diverges);
* `whileMap_least` — leastness: any `w'` satisfying the recursion dominates `whileMap`.

Everything is choice-free in spirit; the only classical input is inherited from `cond`/`T`
(Example 1.2) and the project's `Element.ext` / `ext_of_toElementMap` machinery.
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise512

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond TD)

variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)




end DomainTheory.NeighbourhoodSystems.Exercise512
