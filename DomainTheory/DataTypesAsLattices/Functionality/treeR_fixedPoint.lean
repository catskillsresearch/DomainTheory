
module

public import DomainTheory.DataTypesAsLattices.Retracts.treeF
public import DomainTheory.DataTypesAsLattices.Retracts.treeR
public import DomainTheory.DataTypesAsLattices.Functionality.eq_4_38

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem treeR_fixedPoint : treeF treeR = treeR := by
  simpa [treeF] using eq_4_38.symm

end DomainTheory.DataTypesAsLattices
