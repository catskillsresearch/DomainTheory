
module

public import DomainTheory.DataTypesAsLattices.Retracts.lambF
public import DomainTheory.DataTypesAsLattices.Retracts.lambR
public import DomainTheory.DataTypesAsLattices.Functionality.eq_4_39

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem lambR_fixedPoint : lambF lambR = lambR := by
  simpa [lambF] using eq_4_39.symm

end DomainTheory.DataTypesAsLattices
