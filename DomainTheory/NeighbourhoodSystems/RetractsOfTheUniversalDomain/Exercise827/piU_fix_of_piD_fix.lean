module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.jArrow_comp_iArrow_apply
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.toElementMap_piU

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- Mirrors `subU_fix_of_subApprox_fix`. -/
theorem piU_fix_of_piD_fix {d : ApproximableMap U U} {φ : (funSpace U U).Element}
    (hφ : (piD d).toElementMap φ = φ) :
    (piU d).toElementMap (iArrow.toElementMap φ) = iArrow.toElementMap φ := by
  rw [toElementMap_piU, jArrow_comp_iArrow_apply, hφ]

end DomainTheory.NeighbourhoodSystems
