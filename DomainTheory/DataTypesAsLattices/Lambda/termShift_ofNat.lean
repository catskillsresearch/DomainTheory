/-ai
Applying the term shift of u to the numeral i equals applying u to the numeral i + 1.

Rewrite by the application law for the shift and by the fact that the successor of a numeral is the next numeral.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.succSet_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.termShift_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem termShift_ofNat (u : Pomega) (i : ℕ) :
    funOf (termShift u) (ofNat i) = funOf u (ofNat (i + 1)) := by
  rw [termShift_app, succSet_ofNat]

end DomainTheory.DataTypesAsLattices
