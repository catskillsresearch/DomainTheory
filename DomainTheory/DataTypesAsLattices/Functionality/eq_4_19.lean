/-ai
Scott 1976, (4.19). If a is a retract, then the diagonal combinator composed with a is typed as an arrow from a to the tensor of a with itself.

Typedness unfolds to the arrow equation, which rewrites by the arrow rule. Graph extensionality and simplification by composition, the diagonal application rule, and the retract equation of a are followed by the tensor rule, both pair projections, and the retract equation of a again.
ai-/
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
theorem eq_4_19 {a : Pomega} (ha : IsRetract a) :
    typed (comp diagC a) (arrowR a (tensorR a a)) := by
  change comp diagC a = funOf (arrowR a (tensorR a a)) (comp diagC a)
  rw [arrowR_app]
  apply graph_ext
  intro u
  simp only [comp_app, diagC_app, retract_app ha]
  rw [tensorR_app, pairSeq_app_zero, pairSeq_app_one, retract_app ha]

end DomainTheory.DataTypesAsLattices
