module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.tail
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.mem_tail

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- A longer tail is a *smaller* set: `tail n ⊆ tail m ↔ m ≤ n`. -/
theorem tail_subset_iff {n m : ℕ} : tail n ⊆ tail m ↔ m ≤ n := by
  constructor
  · intro h
    exact h (show n ∈ tail n from le_refl n)
  · intro hmn k hk
    exact le_trans hmn hk

end DomainTheory.NeighbourhoodSystems.Exercise112
