/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem41
public import DomainTheory.Neighborhood.Exercise326

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

namespace DomainTheory.Neighborhood.Exercise512

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Exercise326 (cond TD)

variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)

/-- The body of the loop as a two-argument map `M : (D → D) × D → D`,
`M(w, x) = cond(p(x), w(f(x)), x)`. It is assembled from `cond`, `eval`, the projections,
pairing and composition, hence approximable. -/
def bodyMap : ApproximableMap (prod (funSpace V V) V) V :=
  (cond V).comp
    (paired (p.comp (proj₁ (funSpace V V) V))
      (paired
        ((evalMap V V).comp
          (paired (proj₀ (funSpace V V) V) (f.comp (proj₁ (funSpace V V) V))))
        (proj₁ (funSpace V V) V)))

/-- The loop operator `Wop : (D → D) → (D → D)`, `Wop(w) = λx. cond(p(x), w(f(x)), x)`. -/
def Wop : ApproximableMap (funSpace V V) (funSpace V V) := curry (bodyMap V p f)

/-- The `while`-loop element of the function space `D → D`: the least fixed point of `Wop`. -/
def whileFix : (funSpace V V).Element := (Wop V p f).fixElement

/-- The approximable function `while p do f : D → D` denoted by `whileFix`. -/
def whileMap : ApproximableMap V V := toApproxMap (whileFix V p f)
end DomainTheory.Neighborhood.Exercise512
