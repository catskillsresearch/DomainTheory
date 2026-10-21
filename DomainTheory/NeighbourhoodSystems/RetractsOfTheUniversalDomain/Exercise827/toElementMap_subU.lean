/-ai
The combinator sub on the universal domain sends an element w to i-arrow of subApprox applied to j-arrow of w.

Unfold the definition and apply the composition law for element maps twice.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.subU

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- `subU`'s defining formula unfolded at the element level. -/
theorem toElementMap_subU (w : U.Element) :
    subU.toElementMap w = iArrow.toElementMap (Sub8_6.subApprox.toElementMap
      (jArrow.toElementMap w)) := by
  unfold subU
  rw [toElementMap_comp, toElementMap_comp]

end DomainTheory.NeighbourhoodSystems
