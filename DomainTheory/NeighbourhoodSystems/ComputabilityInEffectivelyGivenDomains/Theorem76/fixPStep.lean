/-ai
The pure fixed-point step, with function-space parameter, an accumulator pairing a previous index with a flag, and a current index, returns the pairing of the current index with the selection of the one-entry inclusion bit of the previous index and the current index when the flag is on, and with 0 when the flag is off.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.codePair

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

variable (P : ComputablePresentation V)

/-- The pure left-fold step corresponding to `fixStp` (parameter `c`, accumulator `acc = pair prev
flag`, current element `x`). -/
def fixPStep (fincl : ℕ → ℕ) (c acc x : ℕ) : ℕ :=
  Nat.pair x (selectFn acc.unpair.2 (isOne (fincl (Nat.pair c (codePair acc.unpair.1 x)))) 0)

end DomainTheory.NeighbourhoodSystems
