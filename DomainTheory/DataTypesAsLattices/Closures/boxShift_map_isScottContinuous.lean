/-ai
The map defining the shift, sending x to the union of the singleton zero with the successor set of a applied to the predecessor of x, is Scott continuous.

It is the composite of union on the left with a constant, successor, application of a, and the predecessor set, each of which is Scott continuous.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.union_const_left_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem boxShift_map_isScottContinuous (a : Pomega) :
    IsScottContinuous (fun x => ofNat 0 ∪ succSet (funOf a (predSet x))) :=
  theorem_1_3 (union_const_left_isScottContinuous (ofNat 0))
    (theorem_1_3 succSet_isScottContinuous
      (theorem_1_3 (funOf_isScottContinuous a) predSet_isScottContinuous))

end DomainTheory.DataTypesAsLattices
