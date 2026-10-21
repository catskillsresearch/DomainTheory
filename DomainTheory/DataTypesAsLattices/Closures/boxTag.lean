/-ai
Scott 1976, (5.13). The occupancy tag of a component x at an index i is the conditional set of x with both branches equal to the singleton i. It returns the constant i when the component is nonempty and the empty set when the component is empty.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (5.13).** The occupancy tag `[u]ᵢ ⊃ i, i`: the constant
`i` whenever the component is nonempty, and `⊥` when it is empty. -/
def boxTag (i : ℕ) (x : Pomega) : Pomega :=
  condSet x (ofNat i) (ofNat i)

end DomainTheory.DataTypesAsLattices
