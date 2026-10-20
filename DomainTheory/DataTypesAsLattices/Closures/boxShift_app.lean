module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.boxShift_map_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































theorem boxShift_app (a x : Pomega) :
    funOf (boxShift a) x = ofNat 0 ∪ succSet (funOf a (predSet x)) :=
  beta (boxShift_map_isScottContinuous a) x

end DomainTheory.DataTypesAsLattices
