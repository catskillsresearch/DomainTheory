/-ai
Scott 1976, (5.3). The boolean retract boool is a closure.

A closure is an expansive retract. The two components are the inclusion of the identity combinator in boool and the retract equation for boool.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_boool
public import DomainTheory.DataTypesAsLattices.Closures.boool_isRetract

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (5.3).** `boool` is a closure. -/
theorem boool_isClosure : IsClosure boool :=
  ⟨Icomb_subset_boool, boool_isRetract⟩

end DomainTheory.DataTypesAsLattices
