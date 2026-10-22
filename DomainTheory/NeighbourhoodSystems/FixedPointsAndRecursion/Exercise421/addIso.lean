module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.upSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise421

open DomainTheory.NeighbourhoodSystems.Exercise414

/-- **Exercise 4.21 (Scott 1981, PRG-19).** The structure-preserving bijection between
`⟨ℕ, 0, ⁺⟩` and `⟨[m], m, ⁺⟩` (where `[m] = {k ∣ m ≤ k}`, with distinguished element `m` and the
successor `⁺`). It is **ordinary addition** by `m`: `n ↦ m + n`. -/
def addIso (m : ℕ) : ℕ ≃ {k : ℕ // k ∈ upSet m} where
  toFun n := ⟨m + n, Nat.le_add_right m n⟩
  invFun k := k.1 - m
  left_inv n := by show m + n - m = n; omega
  right_inv := by
    rintro ⟨k, hk⟩
    exact Subtype.ext (Nat.add_sub_of_le hk)

end DomainTheory.NeighbourhoodSystems.Exercise421
