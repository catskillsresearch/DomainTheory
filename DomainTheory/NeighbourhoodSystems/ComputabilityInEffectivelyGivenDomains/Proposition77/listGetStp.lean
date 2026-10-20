module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- One step of the list-indexing fold: state `pair countdown value`; capture the current element
when `countdown = 1`, else carry the value and decrement. -/
def listGetStp (t : ℕ) : ℕ :=
  Nat.pair (t.unpair.2.unpair.1.unpair.1 - 1)
    (selectFn (isOne t.unpair.2.unpair.1.unpair.1) t.unpair.1 t.unpair.2.unpair.1.unpair.2)

end Proposition77

end DomainTheory.NeighbourhoodSystems
