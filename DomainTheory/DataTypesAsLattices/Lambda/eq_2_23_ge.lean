/-ai
The binary sequence of x and y, applied to the numeral n + 2, is ⊥.

The application formula for the binary sequence rewrites the value as a conditional, which simplifies to ⊥.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.seq2_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices



































theorem eq_2_23_ge (x y : Pomega) (n : ℕ) :
    funOf (seq2 x y) (ofNat (n + 2)) = botElem := by
  rw [seq2_app]
  ext k
  simp [condSet, predSet, ofNat, botElem]

end DomainTheory.DataTypesAsLattices
