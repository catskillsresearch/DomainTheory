/-ai
The addition equivalence sends the pair of naturals m and n to m + n.

The equality holds by definition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise421

open DomainTheory.NeighbourhoodSystems.Exercise414









/-- The isomorphism is given by addition: `addIso m n = m + n`. -/
theorem addIso_apply (m n : ℕ) : (addIso m n : ℕ) = m + n := rfl

end DomainTheory.NeighbourhoodSystems.Exercise421
