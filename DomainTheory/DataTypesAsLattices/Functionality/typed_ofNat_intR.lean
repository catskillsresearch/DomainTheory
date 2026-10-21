/-ai
Every numeral is typed by the integer retract.

This is the symmetric form of the numeral law for the integer retract.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem typed_ofNat_intR (n : ℕ) : typed (ofNat n) intR :=
  (intR_ofNat n).symm

end DomainTheory.DataTypesAsLattices
