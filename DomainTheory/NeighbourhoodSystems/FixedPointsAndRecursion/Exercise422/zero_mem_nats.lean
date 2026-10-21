/-ai
Zero lies in the carved-out set.

For an arbitrary set closed under the generating operator, the closure hypothesis applied to the zero clause places zero in the set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.nats

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise422

open DomainTheory.NeighbourhoodSystems DomainTheory.NeighbourhoodSystems.Exercise414

variable {M : Type*} (zero : M) (succ : M → M)

/-- `0 ∈ N` — directly from the `lfpSet` definition (no monotonicity needed), keeping the
construction choice-free. -/
theorem zero_mem_nats : zero ∈ nats zero succ := by
  intro x hx
  exact hx (Or.inl rfl)

end DomainTheory.NeighbourhoodSystems.Exercise422
