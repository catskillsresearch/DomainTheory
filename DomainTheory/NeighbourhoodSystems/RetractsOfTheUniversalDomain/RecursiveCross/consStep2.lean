module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive

@[expose] public section

namespace Domain.Recursive

/-- `foldCode`'s step for consing the popped element `x` onto the accumulator (ignoring the
threaded parameter). -/
def consStep2 (w : ℕ) : ℕ := Nat.pair w.unpair.1 w.unpair.2.unpair.1 + 1

end Domain.Recursive
