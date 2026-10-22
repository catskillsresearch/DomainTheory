
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.union_right_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Vstep_isScottContinuous (a x : Pomega) :
    IsScottContinuous (Vstep a x) :=
  union_right_isScottContinuous x (funOf_isScottContinuous a)

end DomainTheory.DataTypesAsLattices
