module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem condSet_ofNat_one (x y : Pomega) : condSet (ofNat 1) x y = y := by
  ext n
  simp [condSet, ofNat]

end DomainTheory.DataTypesAsLattices
