/-ai
If the tag of a code is 2, then one extra unit of fuel decodes it as the concatenation of the two subcodes decoded with the remaining fuel, or as nothing if either subcode fails.

Unfold the decoder and substitute the tag. The two sides agree.
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

theorem decodeFuel_succ_cat (fuel c : ℕ) (h : c.unpair.1 = 2) :
    decodeFuel (fuel + 1) c =
      match decodeFuel fuel c.unpair.2.unpair.1, decodeFuel fuel c.unpair.2.unpair.2 with
      | some a, some b => some (.cat a b)
      | _, _ => none := by
  simp [decodeFuel, h]
  rfl

end Exercise722

end DomainTheory.NeighbourhoodSystems
