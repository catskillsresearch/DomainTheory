/-ai
For fixed a and x, the step sending y to the union of x with a(y) is Scott continuous.

Union on the right preserves Scott continuity, and application of the fixed element a is Scott continuous.
ai-/

module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.union_right_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Vstep_isScottContinuous (a x : Pomega) :
    IsScottContinuous (Vstep a x) :=
  union_right_isScottContinuous x (funOf_isScottContinuous a)

end DomainTheory.DataTypesAsLattices
