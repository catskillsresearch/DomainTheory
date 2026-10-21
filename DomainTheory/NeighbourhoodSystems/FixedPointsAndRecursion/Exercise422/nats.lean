/-ai
The carved-out subset is the least fixed point of the generating operator.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.genOp

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise422

open DomainTheory.NeighbourhoodSystems DomainTheory.NeighbourhoodSystems.Exercise414

variable {M : Type*} (zero : M) (succ : M → M)

/-- The carved-out subset `N ⊆ N*`: the least fixed point of `g` (Exercise 4.13(2)/4.14). -/
def nats : Set M := lfpSet (genOp zero succ)

end DomainTheory.NeighbourhoodSystems.Exercise422
