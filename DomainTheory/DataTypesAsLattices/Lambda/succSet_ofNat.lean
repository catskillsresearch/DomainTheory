/-ai
The successor of the numeral j is the numeral j + 1.

Extensionality and the definitions of the successor and of the numeral give the equality.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem succSet_ofNat (j : ℕ) : succSet (ofNat j) = ofNat (j + 1) := by
  ext k
  simp [succSet, ofNat]

end DomainTheory.DataTypesAsLattices
