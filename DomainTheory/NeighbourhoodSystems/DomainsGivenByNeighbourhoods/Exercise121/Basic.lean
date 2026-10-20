module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise121.IsComplete
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise121.filterFixedBy

@[expose] public section

/-!
# Exercise 1.21 (Scott 1981, PRG-19, §1) — Theorem 1.10 in greater detail

Scott asks to work out the proof of Theorem 1.10 more fully and to observe two further
properties of the element-token system `{[X]}` over `|𝒟|`:

* it is **positive** (`tokenSystem_isPositive`), giving "in a different way the same kind of
  conclusion as in 1.20";
* it is **complete** (`tokenSystem_complete`): every filter is *fixed* by a unique point — the
  point whose filter of containing neighbourhoods it is. We formalize "fixed by a point" as
  `IsComplete`, and derive it from the bijection `tokenIso` of Theorem 1.10
  (`tokenSystem_toToken_bijective`). Thus tokens and (partial) elements are identified.

Finally, consistency of `{Xᵢ ∣ i < n}` is equivalent to
`⋂_{i<n} [Xᵢ] ≠ ∅` (`consistent_iff_iInter_bracket_nonempty`), the finite generalization of
Theorem 1.10(2) via Theorem 1.1c.

Everything is `[propext, Quot.sound]` (the corollaries inherit the constructive proofs of
Theorem 1.10 / Theorem 1.1c).
-/

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-! ### Completeness: every filter is fixed by a unique point. -/



/-! ### Consistency ⟺ non-empty intersection of brackets. -/
end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
