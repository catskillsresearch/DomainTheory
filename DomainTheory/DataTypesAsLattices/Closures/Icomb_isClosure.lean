/-ai
The identity combinator is a closure.

It contains itself, and it is a retract.
ai-/

module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































theorem Icomb_isClosure : IsClosure Icomb :=
  ⟨subset_rfl, Icomb_isRetract⟩

end DomainTheory.DataTypesAsLattices
