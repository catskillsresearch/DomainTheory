/-ai
Scott 1976, (4.12). The composite of the tensor of a and b with the tensor of a' and b' equals the tensor of the composite of a with a' and the composite of b with b'.

The equality follows by graph extensionality at the argument, two applications of the tensor rule, the zero and one projections of the pair sequence, and the application rule for composition.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (4.12).** `(a ⊗ b) ∘ (a' ⊗ b') = (a ∘ a') ⊗ (b ∘ b')`. -/
theorem eq_4_12 (a b a' b' : Pomega) :
    comp (tensorR a b) (tensorR a' b') = tensorR (comp a a') (comp b b') := by
  apply graph_ext
  intro u
  rw [tensorR_app, tensorR_app, pairSeq_app_zero, pairSeq_app_one]
  simp only [comp_app]

end DomainTheory.DataTypesAsLattices
