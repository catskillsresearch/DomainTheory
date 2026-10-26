module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.funRetract
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_funRetract

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem funRetract_isClosure : Closure funRetract :=
  ⟨⟨Icomb_subset_funRetract, funRetract.isRetract⟩⟩

end DomainTheory.DataTypesAsLattices
