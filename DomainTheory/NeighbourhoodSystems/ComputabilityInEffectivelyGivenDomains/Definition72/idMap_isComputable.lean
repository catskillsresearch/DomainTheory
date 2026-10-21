/-ai
The identity approximable map is computable relative to any computable presentation.

The identity relation is equivalent to inclusion of the enumerated neighbourhoods: the relation yields the inclusion, and an inclusion rebuilds the relation because both enumerated sets are neighbourhoods. Inclusion is recursively decidable for the presentation, and a recursively decidable predicate is recursively enumerable.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}



variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}

/-- **The identity map is computable** (the identity half of Proposition 7.3). The relation
`Xₙ I Xₘ` is `Xₙ ⊆ Xₘ` (`incl_computable`), which is recursively *decidable*, hence recursively
enumerable. -/
theorem idMap_isComputable (P : ComputablePresentation V) :
    IsComputableMap P P (idMap V) :=
  (RecDecidable.of_iff (fun t => by
    simp only [idMap_rel]
    exact ⟨fun h => h.2.2, fun h => ⟨P.mem_X _, P.mem_X _, h⟩⟩)
    P.incl_computable).re

end DomainTheory.NeighbourhoodSystems
