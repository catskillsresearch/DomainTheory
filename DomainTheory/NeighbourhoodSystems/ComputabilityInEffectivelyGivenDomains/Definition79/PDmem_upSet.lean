/-ai
The down-set of any neighbourhood is a neighbourhood of the Smyth power domain.

Witness it by the singleton list containing that neighbourhood. By membership in a union of down-sets, a set lies in the corresponding union exactly when it lies in this down-set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79.mem_PDunion

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Definition 7.9 — singletons.** Every down-set `↓X` (`X ∈ 𝒟`) is a neighbourhood of `ℙ𝒟`
(the case `n = 1`); these are exactly the neighbourhoods of the prepared system `𝒟†`. -/
theorem PDmem_upSet {X : Set α} (hX : V.mem X) : V.PDmem (V.upSet X) := by
  refine ⟨[X], ?_, ?_⟩
  · intro Y hY; rw [List.mem_singleton] at hY; subst hY; exact hX
  · ext z
    rw [mem_PDunion]
    constructor
    · intro hz; exact ⟨X, List.mem_singleton.mpr rfl, hz⟩
    · rintro ⟨Y, hY, hz⟩; rw [List.mem_singleton] at hY; subst hY; exact hz

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
