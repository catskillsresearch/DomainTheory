/-ai
The down-set of the master neighbourhood is a neighbourhood of the Smyth power domain.

Apply the fact that the down-set of any neighbourhood is a power-domain neighbourhood to the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79.PDmem_upSet

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Definition 7.9 — the master neighbourhood `↓Δ`.** The largest neighbourhood of `ℙ𝒟` is
`↓Δ = 𝒟` (all `𝒟`-neighbourhoods), itself a finite union (the case `X₀ = Δ`). -/
theorem PDmem_master : V.PDmem (V.upSet V.master) := V.PDmem_upSet V.master_mem

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
