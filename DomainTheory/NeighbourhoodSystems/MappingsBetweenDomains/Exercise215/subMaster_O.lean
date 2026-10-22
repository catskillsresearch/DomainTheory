module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.memO

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem subMaster_O : ∀ {X : Set (Fin 1)}, memO X → X ⊆ Set.univ := fun _ => Set.subset_univ _

end DomainTheory.NeighbourhoodSystems.Exercise215
