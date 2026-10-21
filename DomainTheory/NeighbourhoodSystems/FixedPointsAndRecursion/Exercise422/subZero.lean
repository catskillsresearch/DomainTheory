/-ai
The zero of the carved-out subtype is the ambient zero, which lies in the carved-out set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.zero_mem_nats
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.Nat'

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise422

open DomainTheory.NeighbourhoodSystems DomainTheory.NeighbourhoodSystems.Exercise414

variable {M : Type*} (zero : M) (succ : M → M)

/-- The zero of the subtype. -/
def subZero : Nat' zero succ := ⟨zero, zero_mem_nats zero succ⟩

end DomainTheory.NeighbourhoodSystems.Exercise422
