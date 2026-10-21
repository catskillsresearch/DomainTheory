/-ai
Scott 1976, (2.6). The predecessor of the numeral 0 is ⊥.

Unfolding the predecessor and the numeral leaves no elements.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices























/-- **Scott 1976, (2.6).** `0 − 1 = ⊥`. -/
theorem eq_2_6 : predSet (ofNat 0) = botElem := by
  ext k
  simp [predSet, ofNat, botElem]

end DomainTheory.DataTypesAsLattices
