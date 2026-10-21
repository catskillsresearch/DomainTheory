/-ai
Scott 1976, (4.6), used in section 5. The open retract is a closure.

A closure is an expansive retract. The two components are the inclusion of the identity combinator in the open retract and the retract equation for the open retract.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.openR_isRetract
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_openR

@[expose] public section


namespace DomainTheory.DataTypesAsLattices



































/-- **Scott 1976, (4.6) / §5.** `open` is a closure. -/
theorem openR_isClosure : IsClosure openR :=
  ⟨Icomb_subset_openR, openR_isRetract⟩

end DomainTheory.DataTypesAsLattices
