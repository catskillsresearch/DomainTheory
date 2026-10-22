module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.mem_tail
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.tail_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem nestedOrDisjoint : NestedOrDisjoint mem := by
  rintro X Y ⟨n, rfl⟩ ⟨m, rfl⟩
  rcases le_total n m with h | h
  · exact Or.inr (Or.inl (tail_subset_iff.mpr h))
  · exact Or.inl (tail_subset_iff.mpr h)

end DomainTheory.NeighbourhoodSystems.Exercise112
