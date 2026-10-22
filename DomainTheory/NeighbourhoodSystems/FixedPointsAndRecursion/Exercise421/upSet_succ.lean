/-ai
The up-set of m + 1 is the successor image of the up-set of m.

After unfolding both sides, a number at least m + 1 has predecessor at least m, and the successor of a number at least m is at least m + 1.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise421

open DomainTheory.NeighbourhoodSystems.Exercise414


/-- `[m⁺] = [m]⁺`: the recursion step of 4.13(3). -/
theorem upSet_succ (m : ℕ) : upSet (m + 1) = succImage (upSet m) := by
  ext k
  simp only [upSet, succImage, Set.mem_ofPred_eq]
  constructor
  · intro h
    exact ⟨k - 1, by omega, by omega⟩
  · rintro ⟨j, hj, rfl⟩
    omega

end DomainTheory.NeighbourhoodSystems.Exercise421
