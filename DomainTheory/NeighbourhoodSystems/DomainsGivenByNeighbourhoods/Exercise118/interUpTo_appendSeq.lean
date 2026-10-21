/-ai
The intersection of the first n1 + j entries of a concatenated sequence equals the intersection of the first n1 entries of the first sequence with the intersection of the first j entries of the second sequence.

The proof is by induction on j. At zero, the prefix identity identifies the intersection along the concatenation with the intersection of the first sequence, and intersecting with the empty intersection, which is the master neighbourhood, leaves that set unchanged. At a successor, the inductive hypothesis and the successor clause of the intersection meet the next concatenated entry. That entry equals the corresponding entry of the second sequence, and associativity matches the successor clause on the right-hand side.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.appendSeq
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.interUpTo_subset_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.interUpTo_appendSeq_left

@[expose] public section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The key identity: `⋂_{i<n1+n2} (X1 ⧺ X2)ᵢ = (⋂_{i<n1} X1ᵢ) ∩ (⋂_{i<n2} X2ᵢ)`. -/
theorem interUpTo_appendSeq (X1 : ℕ → Set α) (n1 : ℕ) (X2 : ℕ → Set α) :
    ∀ {j : ℕ}, V.interUpTo (appendSeq X1 n1 X2) (n1 + j)
      = V.interUpTo X1 n1 ∩ V.interUpTo X2 j := by
  intro j
  induction j with
  | zero =>
    rw [Nat.add_zero, V.interUpTo_appendSeq_left X1 n1 X2 (le_refl n1), interUpTo_zero]
    exact (Set.inter_eq_left.mpr (V.interUpTo_subset_master X1 n1)).symm
  | succ j ih =>
    rw [Nat.add_succ, interUpTo_succ, ih]
    have happ : appendSeq X1 n1 X2 (n1 + j) = X2 j := by
      simp only [appendSeq, ite_eq_right (by omega : ¬ n1 + j < n1)]
      congr 1
      omega
    rw [happ, interUpTo_succ, Set.inter_assoc]

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
