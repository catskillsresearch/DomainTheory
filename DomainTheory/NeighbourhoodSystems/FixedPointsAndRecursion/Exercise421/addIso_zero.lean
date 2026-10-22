module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise421

open DomainTheory.NeighbourhoodSystems.Exercise414


/-- The isomorphism sends `0` to the distinguished element `m` of `[m]`. -/
theorem addIso_zero (m : ℕ) : (addIso m 0 : ℕ) = m := by simp [addIso]

end DomainTheory.NeighbourhoodSystems.Exercise421
