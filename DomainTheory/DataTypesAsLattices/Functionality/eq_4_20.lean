module

public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.fstC
public import DomainTheory.DataTypesAsLattices.Retracts.tensorR
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Pomega.e
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
  rw [fstC.app, tensorR_app, pairSeq_app_zero, fstC.app]

end DomainTheory.DataTypesAsLattices
