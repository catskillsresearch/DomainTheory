module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.memO
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.nestedOrDisjoint_O
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.subMaster_O

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Exercise 2.15 — the one-token system `𝒪 = {Δ, ∅}`.** -/
def O : NeighborhoodSystem (Fin 1) :=
  NeighborhoodSystem.ofNestedOrDisjoint memO Set.univ Set.univ_nonempty
    (Or.inl rfl) nestedOrDisjoint_O subMaster_O

end DomainTheory.NeighbourhoodSystems.Exercise215
