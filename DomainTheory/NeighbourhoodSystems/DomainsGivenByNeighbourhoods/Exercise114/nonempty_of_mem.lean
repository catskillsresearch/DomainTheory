module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise114.mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise114

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem nonempty_of_mem {X : Set ℕ} (h : mem X) : X.Nonempty := by
  rcases h with rfl | h
  · exact Set.univ_nonempty
  · exact h.2

end DomainTheory.NeighbourhoodSystems.Exercise114
