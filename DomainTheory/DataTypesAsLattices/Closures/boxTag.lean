module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (5.13).** The occupancy tag `[u]ᵢ ⊃ i, i`: the constant
`i` whenever the component is nonempty, and `⊥` when it is empty. -/
def boxTag (i : ℕ) (x : Pomega) : Pomega :=
  condSet x (ofNat i) (ofNat i)

end DomainTheory.DataTypesAsLattices
