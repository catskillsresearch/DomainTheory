/-ai
Successor on the carved-out subtype sends an element to the successor of its underlying element, which remains in the carved-out set by closure under successor.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.succ_mem_nats
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.Nat'

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise422

open DomainTheory.NeighbourhoodSystems DomainTheory.NeighbourhoodSystems.Exercise414

variable {M : Type*} (zero : M) (succ : M → M)

/-- The successor of the subtype (well-defined by closure `succ_mem_nats`). -/
def subSucc (n : Nat' zero succ) : Nat' zero succ := ⟨succ n.1, succ_mem_nats zero succ n.2⟩

end DomainTheory.NeighbourhoodSystems.Exercise422
