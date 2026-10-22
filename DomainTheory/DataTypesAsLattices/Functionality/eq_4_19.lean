module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app
public import DomainTheory.DataTypesAsLattices.Functionality.diagC_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (4.19).** `diag ∘ a : a ∘→ a ⊗ a`. -/
theorem eq_4_19 {a : Pomega} (ha : Retract a) :
    typed (comp diagC a) (arrowR a (tensorR a a)) := by
  change comp diagC a = funOf (arrowR a (tensorR a a)) (comp diagC a)
  rw [arrowR_app]
  apply graph_ext
  intro u
  simp only [comp_app, diagC_app, retract_app ha]
  rw [tensorR_app, pairSeq_app_zero, pairSeq_app_one, retract_app ha]

end DomainTheory.DataTypesAsLattices
