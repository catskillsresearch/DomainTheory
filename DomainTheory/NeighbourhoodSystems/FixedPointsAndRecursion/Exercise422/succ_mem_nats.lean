/-ai
The carved-out set is closed under successor.

For an arbitrary set closed under the generating operator, the given element lies in that set by the same membership hypothesis, and the closure hypothesis applied to the successor clause places the successor in the set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.nats

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise422

open DomainTheory.NeighbourhoodSystems DomainTheory.NeighbourhoodSystems.Exercise414

variable {M : Type*} (zero : M) (succ : M → M)

/-- `N` is closed under the successor: `n ∈ N ⟹ n⁺ ∈ N` — again directly from `lfpSet`. -/
theorem succ_mem_nats {n : M} (hn : n ∈ nats zero succ) : succ n ∈ nats zero succ := by
  intro x hx
  exact hx (Or.inr ⟨n, hn x hx, rfl⟩)

end DomainTheory.NeighbourhoodSystems.Exercise422
