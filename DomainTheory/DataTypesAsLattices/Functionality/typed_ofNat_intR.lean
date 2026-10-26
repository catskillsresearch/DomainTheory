
module

public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.intR
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem typed_ofNat_intR (n : ℕ) : typed (ofNat n) intR :=
  (intR.app_ofNat n).symm

end DomainTheory.DataTypesAsLattices
