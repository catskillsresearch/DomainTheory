module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app
public import DomainTheory.DataTypesAsLattices.Functionality.inleftC_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (4.32).** ` (a ⊕ b) ∘ inleft ∘ a : a ∘→ (a ⊕ b) `. -/
theorem eq_4_32 {a b : Pomega} (ha : Retract a) :
    typed (comp (plusR a b) (comp inleftC a)) (arrowR a (plusR a b)) := by
  change comp (plusR a b) (comp inleftC a) =
    funOf (arrowR a (plusR a b)) (comp (plusR a b) (comp inleftC a))
  rw [arrowR_app]
  apply graph_ext
  intro x
  simp only [comp_app, inleftC_app, retract_app ha]
  rw [plusR_app, plusR_app, pairSeq_app_zero, pairSeq_app_one,
    dcondSet_ofNat_zero, retract_app ha]
  rw [pairSeq_app_zero, pairSeq_app_one, dcondSet_ofNat_zero, retract_app ha]

end DomainTheory.DataTypesAsLattices
