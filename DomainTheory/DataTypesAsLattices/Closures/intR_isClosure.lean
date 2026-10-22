/-ai
The integer retract is a closure.

A closure is an expansive retract. The two components are the inclusion of the identity combinator in the integer retract and the retract equation for that retract.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_intR

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem intR_isClosure : Closure intR :=
  ⟨⟨Icomb_subset_intR, intR_isRetract⟩⟩

end DomainTheory.DataTypesAsLattices
