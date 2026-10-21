/-ai
For each stage and each value, the iterator is Scott continuous in the function argument.

Induct on the stage. Stage zero is the constant function with the given value. A successor is binary continuous substitution of application, combining the identity in the function argument with the inductive map.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_tuple

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Z_isScottContinuous_left (n : ℕ) (x : Pomega) :
    IsScottContinuous (fun f => Z n f x) := by
  induction n with
  | zero => simpa [Z] using const_isScottContinuous x
  | succ n ih =>
    simpa [Z] using
      continuous_tuple
        (fun y => funOf_isScottContinuous_left y)
        (fun u => funOf_isScottContinuous u)
        id_isScottContinuous ih

end DomainTheory.DataTypesAsLattices
