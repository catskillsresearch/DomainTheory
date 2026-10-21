/-ai
The tree retract is a fixed point of the tree functional.

This is the symmetric form of equation (4.38), simplified by the definition of the functional.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.eq_4_38

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






























theorem treeR_fixedPoint : treeF treeR = treeR := by
  simpa [treeF] using eq_4_38.symm

end DomainTheory.DataTypesAsLattices
