module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.embed
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.restrict
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relIso
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem_master
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.embed_le
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.embed_restrict
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.restrict_embed
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.embed_mono
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.le_of_embed_le

@[expose] public section

/-!
# Exercise 4.10 (Scott 1981, PRG-19, Lecture IV) — the relativized domain `Dₐ`

Given a domain `𝒟` and an element `a ∈ |𝒟|`, construct a domain `Dₐ` whose elements are exactly
the elements below `a`:

  `|Dₐ| = {x ∈ |𝒟| ∣ x ⊑ a}`.

**Construction.** `relSystem a` keeps the same tokens and master `Δ`, but takes as neighbourhoods
exactly the *members of the filter `a`* (`mem X := a.mem X`). This is a neighbourhood system because
`a`, being a filter, contains `Δ` and is closed under consistent intersections. Its filters are in
order-isomorphism with the elements of `𝒟` below `a` (`relIso`): a `Dₐ`-filter `g` is sent to its
`𝒟`-upward-closure `embed a g`, and an element `x ⊑ a` is sent to its restriction `restrict a x`
(automatically a `Dₐ`-filter since `x.mem ⊆ a.mem`).

**Restriction of `f`.** If `f : 𝒟 → 𝒟` is approximable and `f(a) = a` (e.g. `a = fix(f)`, by
Theorem 4.1), then `f` restricts to an approximable `f' : Dₐ → Dₐ` (`relMap`) with the same
action (`embed a (f'(g)) = f(embed a g)`, `relMap_toElementMap_embed`). The codomain condition
`f.rel X Y ⟹ a.mem Y` for `a`-neighbourhoods `X` holds because `↑X ⊑ a`, so `Y ∈ f(↑X) ⊑ f(a) = a`.

**How many fixed points does `f'` have?** When `a = fix(f)`, *exactly one* (`relMap_unique_fixed`):
the top element of `Dₐ` (corresponding to `fix(f)` itself). Any fixed point of `f` below `fix(f)` is
a pre-fixed point, hence `⊒ fix(f)` by leastness (`fixElement_below_unique`), so it *equals* `fix(f)`.

All constructions are **choice-free**; equalities of `Element`/maps use the project's permitted
`Element.ext`.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-! ### The relativized domain `Dₐ`. -/












/-! ### Restricting an endomap with `f(a) = a`. -/


/-! ### How many fixed points does `f'` have? -/
end ApproximableMap
end DomainTheory.NeighbourhoodSystems
