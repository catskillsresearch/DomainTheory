/-ai
If the universal-domain product of d fixes an element w, then the function-space product fixes j-arrow of w.

Unfold the element map of the universal-domain product. Apply j-arrow to both sides and cancel j-arrow after i-arrow.
ai-/
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

/-- Unfolds `(piU d).toElementMap w = w` into the statement that `j_→(w)` is already a fixed
point of `piD d` (mirrors `subApprox_fix_of_subU_fix`). -/
theorem piD_fix_of_piU_fix {d : ApproximableMap U U} {w : U.Element}
    (hw : (piU d).toElementMap w = w) :
    (piD d).toElementMap (jArrow.toElementMap w) = jArrow.toElementMap w := by
  rw [toElementMap_piU] at hw
  have hstep := congrArg jArrow.toElementMap hw
  rwa [jArrow_comp_iArrow_apply] at hstep

end DomainTheory.NeighbourhoodSystems
