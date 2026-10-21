/-ai
The two-element sequence of two sets, applied to the numeral zero, equals the first set.

The application law for the two-element sequence is followed by extensionality and simplification of the conditional, the predecessor, the numeral, and the bottom element.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.seq2_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


























theorem seq2_app_zero (x y : Pomega) : funOf (seq2 x y) (ofNat 0) = x := by
  rw [seq2_app]
  ext n
  simp [condSet, predSet, ofNat, botElem]

end DomainTheory.DataTypesAsLattices
