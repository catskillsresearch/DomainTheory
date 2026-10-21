/-ai
If the tag of a code is 0 and the payload is zero, then one extra unit of fuel decodes the code as sigma.

Unfold the decoder and substitute the tag and the zero payload.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

theorem decodeFuel_succ_sigma (fuel c : ℕ) (h : c.unpair.1 = 0) (hσ : c.unpair.2 = 0) :
    decodeFuel (fuel + 1) c = some .sigma := by simp [decodeFuel, h, hσ]

end Exercise722

end DomainTheory.NeighbourhoodSystems
