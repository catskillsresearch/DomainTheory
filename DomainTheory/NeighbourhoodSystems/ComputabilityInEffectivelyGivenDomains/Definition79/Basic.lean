module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79.PDmem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Definition 7.9 — the preparation `𝒟†`.** Scott prepares `𝒟` for the power-domain
construct by replacing it with the isomorphic system `𝒟† = {↓X ∣ X ∈ 𝒟}`, which is exactly
Exercise 1.20's `powerSystem` (over the token type `Δ† = 𝒟`, i.e. `Set α`). It is a *positive*
neighbourhood system (`powerSystem_isPositive`). -/
abbrev dagger : NeighborhoodSystem (Set α) := V.powerSystem


end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
