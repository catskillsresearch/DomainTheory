module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem succSet_ofNat (j : ℕ) : succSet (ofNat j) = ofNat (j + 1) := by
  ext k
  simp [succSet, ofNat]

end DomainTheory.DataTypesAsLattices
