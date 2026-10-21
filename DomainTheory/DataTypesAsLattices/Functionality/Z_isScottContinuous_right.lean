/-ai
For each stage and each function, the iterator is Scott continuous in the value argument.

Induct on the stage. Stage zero is the identity. A successor is substitution of application of the function into the inductive map.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Z_isScottContinuous_right (n : ℕ) (f : Pomega) :
    IsScottContinuous (fun x => Z n f x) := by
  induction n with
  | zero => simpa [Z] using id_isScottContinuous
  | succ n ih =>
    simpa [Z] using theorem_1_3 (funOf_isScottContinuous f) ih

end DomainTheory.DataTypesAsLattices
