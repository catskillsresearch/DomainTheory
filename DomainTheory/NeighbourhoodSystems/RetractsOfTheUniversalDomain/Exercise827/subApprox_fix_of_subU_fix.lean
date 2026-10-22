module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.subU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.toElementMap_subU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.jArrow_comp_iArrow_apply

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- Unfolds `subU.toElementMap w = w` (via `jArrow_comp_iArrow`) into the statement that
`j_→(w)` is already a fixed point of `subApprox`. Used for both `subUFixIso.toFun`'s well-typing
and its `left_inv`. -/
theorem subApprox_fix_of_subU_fix {w : U.Element} (hw : subU.toElementMap w = w) :
    Sub8_6.subApprox.toElementMap (jArrow.toElementMap w) = jArrow.toElementMap w := by
  rw [toElementMap_subU] at hw
  have hstep := congrArg jArrow.toElementMap hw
  rwa [jArrow_comp_iArrow_apply] at hstep

end DomainTheory.NeighbourhoodSystems
