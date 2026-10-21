/-ai
The order isomorphism between the fixed points of sub on the universal domain and the fixed points of subApprox sends a fixed element to j-arrow of it and sends a fixed function-space element back by i-arrow. The forward composite recovers the element because the element-map formula for sub, the fixed-point hypothesis, and the transported fixed-point equation identify i-arrow of j-arrow of the element with the element. The backward composite is the identity j-arrow after i-arrow. An inequality of the decoded elements reflects to the elements because i-arrow is monotone and the same recovery equations hold on both fixed points, and an inequality of the elements is preserved because j-arrow is monotone.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.subU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.toElementMap_subU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.jArrow_comp_iArrow_apply
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.subApprox_fix_of_subU_fix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.subU_fix_of_subApprox_fix

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- **`Fix(subU) ≃o Fix(subApprox)`.** Forward: `w ↦ j_→(w)`; backward: `φ ↦ i_→(φ)`. Needs only
`j_→∘i_→ = I` (no inequality on `i_→∘j_→`). -/
noncomputable def subUFixIso :
    {w : U.Element // subU.toElementMap w = w} ≃o
      {φ : (funSpace U U).Element // Sub8_6.subApprox.toElementMap φ = φ} where
  toFun w := ⟨jArrow.toElementMap w.1, subApprox_fix_of_subU_fix w.2⟩
  invFun φ := ⟨iArrow.toElementMap φ.1, subU_fix_of_subApprox_fix φ.2⟩
  left_inv w := by
    apply Subtype.ext
    show iArrow.toElementMap (jArrow.toElementMap w.1) = w.1
    have hw := toElementMap_subU w.1
    rw [w.2] at hw
    rw [subApprox_fix_of_subU_fix w.2] at hw
    exact hw.symm
  right_inv φ := by
    apply Subtype.ext
    exact jArrow_comp_iArrow_apply φ.1
  map_rel_iff' := by
    intro w w'
    show jArrow.toElementMap w.1 ≤ jArrow.toElementMap w'.1 ↔ w.1 ≤ w'.1
    constructor
    · intro hle
      have h2 := iArrow.toElementMap_mono hle
      have e1 : iArrow.toElementMap (jArrow.toElementMap w.1) = w.1 := by
        have hw := toElementMap_subU w.1
        rw [w.2, subApprox_fix_of_subU_fix w.2] at hw
        exact hw.symm
      have e2 : iArrow.toElementMap (jArrow.toElementMap w'.1) = w'.1 := by
        have hw' := toElementMap_subU w'.1
        rw [w'.2, subApprox_fix_of_subU_fix w'.2] at hw'
        exact hw'.symm
      rwa [e1, e2] at h2
    · intro hle
      exact jArrow.toElementMap_mono hle

end DomainTheory.NeighbourhoodSystems
