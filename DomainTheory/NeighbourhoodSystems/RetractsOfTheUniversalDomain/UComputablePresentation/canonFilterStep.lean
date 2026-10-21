/-ai
The filter step of a pair code is the singleton list code of the clipped pair when that clipped pair is nondegenerate, and the empty list code otherwise. The choice is selection on the nonempty test of the clipped code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.qpClipCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `[qpClipCode e]` if the clipped pair is non-degenerate, else `[]` (the empty list code `0`). -/
def canonFilterStep (e : ℕ) : ℕ :=
  selectFn (qpNonemptyBop (qpClipCode e)) (Nat.pair (qpClipCode e) 0 + 1) 0

end DomainTheory.NeighbourhoodSystems
