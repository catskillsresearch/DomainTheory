module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_fst

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (4.36).** `which ∘ (a ⊕ b) : (a ⊕ b) ∘→ bool`. -/
theorem eq_4_36 (a b : Pomega) :
    typed (comp whichC (plusR a b)) (arrowR (plusR a b) boolR) := by
  change comp whichC (plusR a b) =
    funOf (arrowR (plusR a b) boolR) (comp whichC (plusR a b))
  rw [arrowR_app]
  apply graph_ext
  intro u
  simp only [comp_app, whichC, fstC_app]
  rw [plusR_fst, boolR_app, plusR_fst, plusR_fst, dcondSet_bool_idem, dcondSet_bool_idem]

end DomainTheory.DataTypesAsLattices
