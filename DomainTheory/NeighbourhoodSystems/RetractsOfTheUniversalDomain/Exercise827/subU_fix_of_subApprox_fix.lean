module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.subU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.toElementMap_subU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.jArrow_comp_iArrow_apply

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

theorem subU_fix_of_subApprox_fix {φ : (funSpace U U).Element}
    (hφ : Sub8_6.subApprox.toElementMap φ = φ) :
    subU.toElementMap (iArrow.toElementMap φ) = iArrow.toElementMap φ := by
  rw [toElementMap_subU, jArrow_comp_iArrow_apply, hφ]

end DomainTheory.NeighbourhoodSystems
