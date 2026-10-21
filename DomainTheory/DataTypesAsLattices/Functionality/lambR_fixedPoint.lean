/-ai
The lambda retract is a fixed point of lambF.

Unfolding the definition of lambF, this is the symmetric form of equation (4.39).
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.eq_4_39

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem lambR_fixedPoint : lambF lambR = lambR := by
  simpa [lambF] using eq_4_39.symm

end DomainTheory.DataTypesAsLattices
