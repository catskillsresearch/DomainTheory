/-ai
Applying nextCellStep to the packing of n and m returns the packing of the two components of nextCell (n, m).

Unfold the step and simplify the unpairing. If n is zero, the zero test equals 1, so the selector takes the first branch, which is definitionally the cell step. If n is a successor, the zero test equals 0, so the selector takes the second branch, again definitionally the cell step.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)


theorem nextCellStep_eq (n m : ℕ) :
    nextCellStep (Nat.pair n m) = Nat.pair (nextCell (n, m)).1 (nextCell (n, m)).2 := by
  unfold nextCellStep
  simp only [unpair_pair_fst, unpair_pair_snd]
  rcases n with _ | k
  · have hz : isZero 0 = 1 := by unfold isZero; omega
    rw [hz, selectFn_one]; rfl
  · have hz : isZero (k + 1) = 0 := by unfold isZero; omega
    rw [hz, selectFn_zero]; rfl

end DomainTheory.NeighbourhoodSystems.Exercise723
