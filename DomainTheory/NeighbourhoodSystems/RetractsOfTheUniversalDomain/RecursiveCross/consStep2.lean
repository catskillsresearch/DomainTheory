/-ai
The cons step reads a code as an element, an accumulator, and a parameter, and returns one more than the pair of the element and the accumulator.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive

@[expose] public section

set_option linter.unusedSectionVars false

namespace Domain.Recursive

/-- `foldCode`'s step for consing the popped element `x` onto the accumulator (ignoring the
threaded parameter). -/
def consStep2 (w : ℕ) : ℕ := Nat.pair w.unpair.1 w.unpair.2.unpair.1 + 1

end Domain.Recursive
