/-ai
The course-of-values value of a step at w equals the step applied to the pair of w and the reverse memo table at w.

The two sides are the same by definition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.rtbl
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.gOf

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem gOf_def (step : ℕ → ℕ) (w : ℕ) : gOf step w = step (Nat.pair w (rtbl step w)) := rfl

end Proposition77

end DomainTheory.NeighbourhoodSystems
