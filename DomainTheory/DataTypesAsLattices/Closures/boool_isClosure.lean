module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_boool
public import DomainTheory.DataTypesAsLattices.Closures.boool_isRetract

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (5.3).** `boool` is a closure. -/
theorem boool_isClosure : Closure boool :=
  ⟨⟨Icomb_subset_boool, boool_isRetract⟩⟩

end DomainTheory.DataTypesAsLattices
