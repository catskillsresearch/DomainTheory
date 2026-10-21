/-ai
The predecessor of the numeral of n + 1 is the numeral of n.

Extensionality simplifies the definitions of the predecessor and the numeral.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















































theorem predSet_ofNat_succ (n : ℕ) : predSet (ofNat (n + 1)) = ofNat n := by
  ext k
  simp [predSet, ofNat]

end DomainTheory.DataTypesAsLattices
