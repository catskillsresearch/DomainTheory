/-ai
The master neighbourhood of the one-token system is the whole token set.

The two sides are definitionally equal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

@[simp] theorem O_master : O.master = (Set.univ : Set (Fin 1)) := rfl

end DomainTheory.NeighbourhoodSystems.Exercise215
