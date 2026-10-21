/-ai
A longer finite intersection is contained in a shorter one.

The proof is by induction on the longer index. If it is zero, the shorter index is zero as well. If it is a successor equal to the shorter index, the two sides agree. If the shorter index is strictly smaller, the successor intersection is contained in the previous intersection, and that is contained in the shorter one by the inductive hypothesis.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

set_option linter.unusedSectionVars false

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
