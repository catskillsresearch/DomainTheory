module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_intR

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































theorem intR_isClosure : IsClosure intR :=
  ⟨Icomb_subset_intR, intR_isRetract⟩

end DomainTheory.DataTypesAsLattices
