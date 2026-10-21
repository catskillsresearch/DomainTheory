/-ai
The two-element sequence of two sets, applied to the numeral one, equals the second set.

The application law for the two-element sequence is followed by extensionality and simplification of the conditional, the predecessor, the numeral, and the bottom element.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.seq2_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem seq2_app_one (x y : Pomega) : funOf (seq2 x y) (ofNat 1) = y := by
  rw [seq2_app]
  ext n
  simp [condSet, predSet, ofNat, botElem]

end DomainTheory.DataTypesAsLattices
