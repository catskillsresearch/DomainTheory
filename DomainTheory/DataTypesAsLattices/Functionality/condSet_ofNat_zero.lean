module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem condSet_ofNat_zero (x y : Pomega) : condSet (ofNat 0) x y = x := by
  ext n
  simp [condSet, ofNat]

end DomainTheory.DataTypesAsLattices
