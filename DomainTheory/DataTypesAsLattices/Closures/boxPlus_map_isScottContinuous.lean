/-ai
The map defining the boxed sum, sending u to the double conditional of the occupancy-tag union with the two shifted square-pair branches, is Scott continuous.

The ternary continuity theorem applies to the three continuity lemmas for the double conditional, the continuity of the occupancy test, and the two branches. Each branch is a continuous square pairing of a constant empty set with the composite of application of the corresponding shift and the corresponding square projection.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.squareFst_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Closures.squareSnd_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Closures.squarePair_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Closures.squarePair_isScottContinuous_right
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_test_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem boxPlus_map_isScottContinuous (a b : Pomega) :
    IsScottContinuous (fun u =>
      dcondSet (boxTag 0 (squareFst u) ∪ boxTag 1 (squareSnd u))
        (squarePair (funOf (boxShift a) (squareFst u)) botElem)
        (squarePair botElem (funOf (boxShift b) (squareSnd u)))) :=
  theorem_1_3_nary
    (fun y z => dcondSet_isScottContinuous_left y z)
    (fun x z => dcondSet_isScottContinuous_mid x z)
    (fun x y => dcondSet_isScottContinuous_right x y)
    boxPlus_test_isScottContinuous
    (theorem_1_3 (f := fun x => squarePair x botElem)
      (g := fun u => funOf (boxShift a) (squareFst u))
      (squarePair_isScottContinuous_left botElem)
      (theorem_1_3 (funOf_isScottContinuous (boxShift a)) squareFst_isScottContinuous))
    (theorem_1_3 (f := fun y => squarePair botElem y)
      (g := fun u => funOf (boxShift b) (squareSnd u))
      (squarePair_isScottContinuous_right botElem)
      (theorem_1_3 (funOf_isScottContinuous (boxShift b)) squareSnd_isScottContinuous))

end DomainTheory.DataTypesAsLattices
