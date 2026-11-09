module

public import DomainTheory.BridgeTheorems.PresentationDomains.RoundInfoSysElement
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.domainOrderIso

@[expose] public section

namespace DomainTheory.BridgeTheorems

open Order

variable {D : Type*} [CompleteLattice D] [DecidableEq D]

noncomputable def roundInfoSys_ideal_iso :
    RoundInfoSysElement (D := D) ≃o
      { I : Ideal (InfoSysToIdealCompletion.FiniteElement
          (wayBelowNbhdBasis (D := D)).toInfoSys) //
        IsRoundInfoSysElement (D := D)
          ((InfoSysToIdealCompletion.domainOrderIso
            (wayBelowNbhdBasis (D := D)).toInfoSys).symm I) } := by
  let A := (wayBelowNbhdBasis (D := D)).toInfoSys
  let ιE := InfoSysToIdealCompletion.domainOrderIso A
  refine {
    toFun := fun e => ⟨ιE e.1, by
      change IsRoundInfoSysElement (ιE.symm (ιE e.1))
      rw [OrderIso.symm_apply_apply]
      exact e.2⟩
    invFun := fun I => ⟨ιE.symm I.1, I.2⟩
    left_inv := fun e => Subtype.ext (ιE.left_inv e.1)
    right_inv := fun I => Subtype.ext (ιE.right_inv I.1)
    map_rel_iff' := by
      intro e₁ e₂
      exact ιE.map_rel_iff
  }

end DomainTheory.BridgeTheorems
