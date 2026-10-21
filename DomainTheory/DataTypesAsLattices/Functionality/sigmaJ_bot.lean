/-ai
The independent successor σ_j sends bottom to bottom.

Extensionality and unfolding: bottom contains no pair code, so the defining membership of σ_j is empty.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem sigmaJ_bot (j : ℕ) : sigmaJ j botElem = botElem := by
  ext p
  simp [sigmaJ, botElem]

end DomainTheory.DataTypesAsLattices
