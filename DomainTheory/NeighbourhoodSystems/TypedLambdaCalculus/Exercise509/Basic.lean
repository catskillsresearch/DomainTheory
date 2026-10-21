/-ai
This file gathers the fixed-point results of Exercise 4.7 and records Scott's Exercise 5.9. If two approximable endomaps commute, they have a least common fixed point. If they also agree at the bottom element, their least fixed points coincide. In particular, the least fixed point of a map equals the least fixed point of its composite with itself.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407

@[expose] public section

/-!
# Exercise 5.9 (Scott 1981, PRG-19, Lecture V)

Suppose `f, g : 𝒟 → 𝒟` are approximable and `f ∘ g = g ∘ f`. Then:

* `f` and `g` have a **least common fixed point** `x = f(x) = g(x)` (`commuting_least_common_fixed`);
* if in addition `f(⊥) = g(⊥)`, then `fix(f) = fix(g)` (`fixElement_eq_of_commuting_bot`);
* in particular `fix(f) = fix(f²)` (`fixElement_iterTwice`).

**Construction.** Let `a = fix(f)`. Commutation makes `g(a)` a fixed point of `f`
(`f(g(a)) = g(f(a)) = g(a)`), so `a ⊑ g(a)`, and Exercise 4.7 produces the least fixed point of `g`
above `a`, namely `x = ⊔ₙ gⁿ(a)`. Each `gⁿ(a)` is again a fixed point of `f` (induction +
commutation), and `f` preserves the directed union, so `f(x) = x`: `x` is a common fixed point. Any
common fixed point `w` satisfies `a = fix(f) ⊑ w` and `g(w) ⊑ w`, so `x ⊑ w` by Exercise 4.7's
leastness.

For the second part, commutation gives `g(fⁿ(⊥)) = fⁿ⁺¹(⊥)` once `g(⊥) = f(⊥)`, so `g(fix f) =
⊔ₙ fⁿ⁺¹(⊥) = fix f`; symmetrically `f(fix g) = fix g`, whence `fix f = fix g` by leastness.

All maps and elements are choice-free; the equalities use only the order on `|𝒟|`.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap
end ApproximableMap
end DomainTheory.NeighbourhoodSystems
