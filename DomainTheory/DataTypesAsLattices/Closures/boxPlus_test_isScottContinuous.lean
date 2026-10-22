/-ai
The occupancy test of the boxed sum, sending u to the union of the tag of the left square component at zero and the tag of the right square component at one, is Scott continuous.

The paired continuity theorem applies to continuity of union in each argument and to the two composites of a continuous occupancy tag with a continuous square projection.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.squareFst_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Closures.squareSnd_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Closures.union_left_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Closures.union_const_left_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Closures.boxTag_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem boxPlus_test_isScottContinuous :
    IsScottContinuous (fun u => boxTag 0 (squareFst u) ∪ boxTag 1 (squareSnd u)) :=
  theorem_1_3_tuple
    (fun y => union_left_isScottContinuous y)
    (fun x => union_const_left_isScottContinuous x)
    (theorem_1_3 (boxTag_isScottContinuous 0) squareFst_isScottContinuous)
    (theorem_1_3 (boxTag_isScottContinuous 1) squareSnd_isScottContinuous)

end DomainTheory.DataTypesAsLattices
