/-ai
The function-space retract is a closure.

A closure is an expansive retract. The two components are the inclusion of the identity combinator in the function-space retract and the retract equation for that retract.
ai-/
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
