module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_funRetract

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































theorem funRetract_isClosure : IsClosure funRetract :=
  ⟨Icomb_subset_funRetract, funRetract_isRetract⟩

end DomainTheory.DataTypesAsLattices
