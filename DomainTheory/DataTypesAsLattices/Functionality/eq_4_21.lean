/-ai
Scott 1976, (4.21). Second projection composed with the tensor of f and f' equals f' composed with second projection.

The proof unfolds composition, then uses graph extensionality, the second-projection rule, the tensor rule, the one projection, and the second-projection rule again.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (4.21).** `snd ∘ (f ⊗ f') = f' ∘ snd`. -/
theorem eq_4_21 (f f' : Pomega) :
    comp sndC (tensorR f f') = comp f' sndC := by
  simp only [comp]
  apply graph_ext
  intro u
  rw [sndC_app, tensorR_app, pairSeq_app_one, sndC_app]

end DomainTheory.DataTypesAsLattices
