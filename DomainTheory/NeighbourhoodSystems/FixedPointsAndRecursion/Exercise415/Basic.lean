module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise124
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413

@[expose] public section

/-!
# Exercise 4.15 (Scott 1981, PRG-19, Lecture IV) — a maximal (and a least) fixed point

(For set theorists.) Let `f : |𝒟| → |𝒟|` be a *monotone* function on the elements of a domain. Then
`f` has a **maximal** fixed point — a fixed point that cannot be extended to a larger one — and
(consequently) a **least** fixed point.

**Maximal fixed point (Zorn).** Consider the set `S = {x ∣ x ⊑ f(x)}` of *post*-fixed points. It is
non-empty (`⊥ ∈ S`) and every chain `C ⊆ S` has an upper bound in `S`: its union `⊔C`
(Exercise 1.24's `chainUnion`, Scott's "use 2.11 to remark `⊔C ∈ |𝒟|`") is again post-fixed, since
each `x ∈ C` has `x ⊑ f(x) ⊑ f(⊔C)`. By Zorn's Lemma (`zorn_le₀`) `S` has a maximal element `m`.
Then `m` is a fixed point: `m ⊑ f(m)` (it is in `S`) and `f(m) ⊑ m` (because `f(m) ∈ S` too, by
monotonicity, and `m` is maximal). It is *maximal among fixed points*
(`exists_maximal_fixedPoint`).

**Least fixed point.** Having produced *some* fixed point `m`, we have `f(m) ⊑ m`, so Exercise
4.13(1) (the monotone-only intersection construction `monoFix`) applies and yields the *least* fixed
point `fix(f) = ⋂{x ∣ f(x) ⊑ x} ⊑ m` (`exists_least_fixedPoint`).

This is the explicitly **classical** exercise (Zorn ⟹ `Classical.choice`), exactly like Exercise
1.24; the `chainUnion` construction itself is choice-free.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem
end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
