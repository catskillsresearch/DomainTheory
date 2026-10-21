/-ai
The one-token system on a one-point token set has neighbourhoods the whole set and the empty set. It is obtained from the nested-or-disjoint constructor, with the whole set as master, using the neighbourhood predicate and the nested-or-disjoint and submaster facts.
ai-/
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
