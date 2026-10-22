module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- Membership for `𝒪`: a neighbourhood is the master `Δ = univ` or the empty set. -/
def memO (X : Set (Fin 1)) : Prop := X = Set.univ ∨ X = ∅

end DomainTheory.NeighbourhoodSystems.Exercise215
