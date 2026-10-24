module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.leOp
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.leRel
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.succImage
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.upSet
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.addIso
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.mulOp

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise421

open DomainTheory.NeighbourhoodSystems.Exercise414


/-- The isomorphism is given by addition: `addIso m n = m + n`. -/
theorem addIso_apply (m n : ℕ) : (addIso m n : ℕ) = m + n := rfl

end DomainTheory.NeighbourhoodSystems.Exercise421
