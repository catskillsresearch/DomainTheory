module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.openR
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.openR_isRetract
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_openR

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (4.6) / §5.** `open` is a closure. -/
theorem openR_isClosure : Closure openR :=
  ⟨⟨Icomb_subset_openR, openR_isRetract⟩⟩

end DomainTheory.DataTypesAsLattices
