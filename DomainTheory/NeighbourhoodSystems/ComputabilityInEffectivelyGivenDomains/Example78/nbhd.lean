module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example78

open Domain.Recursive NeighborhoodSystem

/-- The neighbourhood `ℕ ∖ Eₙ` of the powerset domain: the cofinite set of bit positions **not**
set in `n`. Scott's `Eₙ` is `{k ∣ n.testBit k}`, so `nbhd n = {k ∣ n.testBit k = false}`. -/
def nbhd (n : ℕ) : Set ℕ := {k | n.testBit k = false}

end DomainTheory.NeighbourhoodSystems.Example78
