/-ai
The code-level clip pairs the rational maximum of the first component of a rational-pair code with the code of zero and the rational minimum of the second component with the code of one.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- Code-level `qpClip`: `(r,s) ↦ (r⊔0, s⊓1)` on a rational-pair code. -/
def qpClipCode (e : ℕ) : ℕ :=
  Nat.pair (ratMaxCode (Nat.pair e.unpair.1 zeroCode)) (ratMinCode (Nat.pair e.unpair.2 oneCode))

end DomainTheory.NeighbourhoodSystems
