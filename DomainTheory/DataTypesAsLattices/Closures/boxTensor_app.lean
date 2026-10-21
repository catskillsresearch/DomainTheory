/-ai
Applying the boxed product of a and b to u equals the square pair of a applied to the first square component and b applied to the second.

This is the beta law for a Scott-continuous map assembled as a pair. Each coordinate is a continuous square pairing of an application of a or b, and the two inputs are the continuous square projections.
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

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem boxTensor_app (a b u : Pomega) :
    funOf (boxTensor a b) u =
      squarePair (funOf a (squareFst u)) (funOf b (squareSnd u)) :=
  beta (theorem_1_3_tuple
    (f := fun x y => squarePair (funOf a x) (funOf b y))
    (fun y => theorem_1_3 (f := fun x => squarePair x (funOf b y)) (g := funOf a)
      (squarePair_isScottContinuous_left (funOf b y))
      (funOf_isScottContinuous a))
    (fun x => theorem_1_3 (f := fun y => squarePair (funOf a x) y) (g := funOf b)
      (squarePair_isScottContinuous_right (funOf a x))
      (funOf_isScottContinuous b))
    squareFst_isScottContinuous squareSnd_isScottContinuous) u

end DomainTheory.DataTypesAsLattices
