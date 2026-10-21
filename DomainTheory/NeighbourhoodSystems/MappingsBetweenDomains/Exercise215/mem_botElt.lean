/-ai
A set belongs to the bottom element if and only if it is the universe.

The bottom element is the bottom element of O, whose members are the master neighbourhood, and that master neighbourhood is the universe.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.botElt

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- `Y ∈ ⊥` iff `Y = Δ = univ`. -/
theorem mem_botElt {Y : Set (Fin 1)} : botElt.mem Y ↔ Y = (Set.univ : Set (Fin 1)) := by
  rw [botElt, O.mem_bot, O_master]

end DomainTheory.NeighbourhoodSystems.Exercise215
