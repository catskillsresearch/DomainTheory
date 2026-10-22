module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise114.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise114

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


theorem empty_not_mem : ¬ mem (∅ : Set ℕ) := by
  rintro (h | ⟨_, h⟩)
  · exact Set.empty_ne_univ h
  · exact Set.not_nonempty_empty h

end DomainTheory.NeighbourhoodSystems.Exercise114
