module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app
public import DomainTheory.DataTypesAsLattices.Functionality.inrightC_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (4.33).** ` (a ⊕ b) ∘ inright ∘ b : b ∘→ (a ⊕ b) `. -/
theorem eq_4_33 {a b : Pomega} (hb : Retract b) :
    typed (comp (plusR a b) (comp inrightC b)) (arrowR b (plusR a b)) := by
  change comp (plusR a b) (comp inrightC b) =
    funOf (arrowR b (plusR a b)) (comp (plusR a b) (comp inrightC b))
  rw [arrowR_app]
  apply graph_ext
  intro x
  simp only [comp_app, inrightC_app, retract_app hb]
  rw [plusR_app, plusR_app, pairSeq_app_zero, pairSeq_app_one,
    dcondSet_ofNat_one, retract_app hb]
  rw [pairSeq_app_zero, pairSeq_app_one, dcondSet_ofNat_one, retract_app hb]

end DomainTheory.DataTypesAsLattices
