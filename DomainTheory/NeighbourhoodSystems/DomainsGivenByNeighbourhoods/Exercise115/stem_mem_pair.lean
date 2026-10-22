/-ai
The pair {0, 1} is a neighbourhood of the stem domain.

It is the middle disjunct of stem membership.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


theorem stem_mem_pair : stem.mem {0, 1} := Or.inr (Or.inl rfl)
end DomainTheory.NeighbourhoodSystems.Exercise115
