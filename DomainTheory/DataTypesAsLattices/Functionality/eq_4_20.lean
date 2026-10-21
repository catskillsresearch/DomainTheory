/-ai
Scott 1976, (4.20). First projection composed with the tensor of f and f' equals f composed with first projection.

The proof unfolds composition, then uses graph extensionality, the first-projection rule, the tensor rule, the zero projection, and the first-projection rule again.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















/-- **Scott 1976, (4.20).** `fst ∘ (f ⊗ f') = f ∘ fst`. -/
theorem eq_4_20 (f f' : Pomega) :
    comp fstC (tensorR f f') = comp f fstC := by
  simp only [comp]
  apply graph_ext
  intro u
  rw [fstC_app, tensorR_app, pairSeq_app_zero, fstC_app]

end DomainTheory.DataTypesAsLattices
