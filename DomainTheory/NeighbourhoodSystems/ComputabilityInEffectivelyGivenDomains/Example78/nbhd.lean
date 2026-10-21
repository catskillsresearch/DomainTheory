/-ai
The neighbourhood indexed by a natural number n is the set of positions k at which the k-th bit of n is unset.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example78

open Domain.Recursive NeighborhoodSystem

/-- The neighbourhood `ℕ ∖ Eₙ` of the powerset domain: the cofinite set of bit positions **not**
set in `n`. Scott's `Eₙ` is `{k ∣ n.testBit k}`, so `nbhd n = {k ∣ n.testBit k = false}`. -/
def nbhd (n : ℕ) : Set ℕ := {k | n.testBit k = false}

end DomainTheory.NeighbourhoodSystems.Example78
