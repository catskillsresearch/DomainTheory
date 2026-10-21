/-ai
If a is a retract, then x is related by the kernel of a to the application of a to x.

The symmetric form of the retract application equation says that a applied to x equals a applied to a applied to x.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem kerE_repr {a : Pomega} (ha : IsRetract a) (x : Pomega) :
    (kerE a).rel x (funOf a x) :=
  (retract_app ha x).symm

end DomainTheory.DataTypesAsLattices
