module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


























theorem sigmaJ_bot (j : ℕ) : sigmaJ j botElem = botElem := by
  ext p
  simp [sigmaJ, botElem]

end DomainTheory.DataTypesAsLattices
