module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.rtbl

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- The course-of-values value at `w`: `g w = step (pair w (table of g below w))`. -/
def gOf (step : ℕ → ℕ) (w : ℕ) : ℕ := step (Nat.pair w (rtbl step w))

end Proposition77

end DomainTheory.NeighbourhoodSystems
