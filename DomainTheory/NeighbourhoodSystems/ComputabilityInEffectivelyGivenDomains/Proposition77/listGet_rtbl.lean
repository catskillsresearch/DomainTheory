/-ai
For v strictly below w, the entry at position w minus one minus v of the reverse memo table at w is the course-of-values value at v.

The table is the code of the reverse memo list, lookup on a code is defaulted indexing, and that index of the reverse list is the value at v; the two index expressions agree.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGet_encodeList
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.rtbl
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.gOf
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.rtbl_eq_encode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.getD_gList

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **The course-of-values lookup.** Inside `step` at `w`, position `w-1-v` of the reverse table is
exactly `g v`, for any earlier `v < w`. -/
theorem listGet_rtbl (step : ℕ → ℕ) {v w : ℕ} (hv : v < w) :
    listGet (rtbl step w) (w - 1 - v) = gOf step v := by
  rw [rtbl_eq_encode, listGet_encodeList, getD_gList step w (w - 1 - v) (by omega)]
  congr 1; omega

end Proposition77

end DomainTheory.NeighbourhoodSystems
