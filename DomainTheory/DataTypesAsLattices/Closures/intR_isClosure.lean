module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.intR
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_intR

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem intR_isClosure : Closure intR :=
  ⟨⟨Icomb_subset_intR, intR.isRetract⟩⟩

end DomainTheory.DataTypesAsLattices
