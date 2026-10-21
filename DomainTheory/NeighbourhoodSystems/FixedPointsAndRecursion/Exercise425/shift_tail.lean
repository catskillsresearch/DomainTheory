/-ai
The shift of the tail of length n is the tail of length n + 1.

The successor of a number at least n is at least n + 1, and a number at least n + 1 is the successor of its predecessor, which is at least n.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.tail
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.shift
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.mem_tail

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise425

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- `1·(1ⁿ⊥) = 1ⁿ⁺¹⊥`: shifting a tail. -/
theorem shift_tail (n : ℕ) : shift (tail n) = tail (n + 1) := by
  ext k
  simp only [shift, tail, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, hm, rfl⟩; omega
  · intro h; exact ⟨k - 1, by omega, by omega⟩

end DomainTheory.NeighbourhoodSystems.Exercise425
