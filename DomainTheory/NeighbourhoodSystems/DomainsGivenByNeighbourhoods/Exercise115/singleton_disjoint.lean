/-ai
If n and m are distinct natural numbers, the intersection of the singletons {n} and {m} is empty.

By extensionality, an element of the intersection would equal both n and m.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- `{n} ∩ {m} = ∅` for `n ≠ m`. -/
theorem singleton_disjoint {n m : ℕ} (h : n ≠ m) : ({n} : Set ℕ) ∩ {m} = ∅ := by
  ext k
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨rfl, h2⟩
  exact h h2

end DomainTheory.NeighbourhoodSystems.Exercise115
