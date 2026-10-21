/-ai
The packed fixed-point step, on a state whose first component is the current index and whose second component pairs the previous accumulator with the function-space parameter, returns the pairing of the current index with the selection of the one-entry inclusion bit of the previous index and the current index when the previous flag is on, and with 0 when the flag is off.
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

/-- One packed `foldCode` step: state `pair acc params` with `acc = pair prev flag`, current element
`x`. Updates the flag with the one-step consistency test and advances `prev` to `x`. -/
def fixStp (fincl : ℕ → ℕ) (w : ℕ) : ℕ :=
  Nat.pair w.unpair.1
    (selectFn w.unpair.2.unpair.1.unpair.2
      (isOne (fincl (Nat.pair w.unpair.2.unpair.2
        (codePair w.unpair.2.unpair.1.unpair.1 w.unpair.1)))) 0)

end DomainTheory.NeighbourhoodSystems
