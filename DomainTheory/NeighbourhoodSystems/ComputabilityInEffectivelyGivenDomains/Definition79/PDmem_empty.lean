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


/-- **Definition 7.9 — the empty union.** "The finite unions in `ℙ𝒟` can be empty (i.e. if
`n = 0`)." The empty neighbourhood `∅` is a neighbourhood of `ℙ𝒟` (witnessed by `L = []`). -/
theorem PDmem_empty : V.PDmem ∅ := by
  refine ⟨[], ?_, ?_⟩
  · intro X hX; cases hX
  · ext z
    rw [mem_PDunion]
    constructor
    · intro h; exact absurd h (Set.notMem_empty z)
    · rintro ⟨X, hX, _⟩; cases hX

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
