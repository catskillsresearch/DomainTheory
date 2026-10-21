/-ai
If a is a retract, then the application of a to any element is typed by a.

This is the symmetric form of the retract application law.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem typed_apply_retract {a x : Pomega} (ha : IsRetract a) :
    typed (funOf a x) a :=
  (retract_app ha x).symm

end DomainTheory.DataTypesAsLattices
