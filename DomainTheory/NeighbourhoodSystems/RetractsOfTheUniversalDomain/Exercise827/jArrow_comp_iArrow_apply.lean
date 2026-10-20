module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

theorem jArrow_comp_iArrow_apply (v : (funSpace U U).Element) :
    jArrow.toElementMap (iArrow.toElementMap v) = v := by
  rw [show jArrow.toElementMap (iArrow.toElementMap v) = (jArrow.comp iArrow).toElementMap v from
    (toElementMap_comp jArrow iArrow v).symm, jArrow_comp_iArrow, toElementMap_idMap]

end DomainTheory.NeighbourhoodSystems
