module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The finite intersection is antitone in its length: a longer prefix is contained in a shorter
one. -/
theorem interUpTo_antitone (X : ℕ → Set α) {j k : ℕ} (h : j ≤ k) :
    V.interUpTo X k ⊆ V.interUpTo X j := by
  induction k with
  | zero => rw [Nat.le_zero.mp h]
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · rw [h']
    · exact Set.inter_subset_left.trans (ih (Nat.lt_succ_iff.mp h'))

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
