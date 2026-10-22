
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem typed_ofNat_intR (n : ℕ) : typed (ofNat n) intR :=
  (intR_ofNat n).symm

end DomainTheory.DataTypesAsLattices
