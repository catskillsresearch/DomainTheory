/-ai
If the tag of a code is at least 4, then one extra unit of fuel decodes the code as nothing.

Match the tag. The values 0, 1, 2, and 3 contradict the bound. A tag of the form t + 4 simplifies the decoder to nothing.
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

theorem decodeFuel_succ_junk (fuel c : ℕ) (h : 4 ≤ c.unpair.1) :
    decodeFuel (fuel + 1) c = none := by
  match tag : c.unpair.1 with
  | 0 | 1 | 2 | 3 => omega
  | t + 4 => simp [decodeFuel, tag]

end Exercise722

end DomainTheory.NeighbourhoodSystems
