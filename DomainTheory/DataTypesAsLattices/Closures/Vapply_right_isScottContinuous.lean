/-ai
For each fixed a, the map sending x to V(a)(x) is Scott continuous.

Equation (5.14) identifies V(a)(x) with the least fixed point of the step y ↦ x ∪ a(y). The fixed-point operator is Scott continuous in a parameter when the body is Scott continuous in each variable separately. The map x ↦ x ∪ a(y) is Scott continuous by union on the left, and each step in y is Scott continuous.
ai-/

module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.Vstep_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_14
public import DomainTheory.DataTypesAsLattices.Closures.union_left_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































theorem Vapply_right_isScottContinuous (a : Pomega) :
    IsScottContinuous (fun x => Vapply a x) := by
  have : (fun x => Vapply a x) = (fun x => VapplyY a x) := by
    funext x; exact (eq_5_14 a x).symm
  rw [this]
  exact fix_param_isScottContinuous
    (fun y => union_left_isScottContinuous (funOf a y))
    (fun x => Vstep_isScottContinuous a x)

end DomainTheory.DataTypesAsLattices
