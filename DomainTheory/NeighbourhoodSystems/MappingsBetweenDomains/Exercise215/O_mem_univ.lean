/-ai
The universe is a neighbourhood of O.

It is the left disjunct of the membership alternative, by reflexivity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


theorem O_mem_univ : O.mem (Set.univ : Set (Fin 1)) := Or.inl rfl

end DomainTheory.NeighbourhoodSystems.Exercise215
