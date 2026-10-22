/-ai
The occupancy tag of the empty set, at any index, is empty.

Extensionality and the definitions of the tag, the conditional set, and the empty set give the equality.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem boxTag_bot (i : ℕ) : boxTag i botElem = botElem := by
  ext n
  simp [boxTag, condSet, botElem]

end DomainTheory.DataTypesAsLattices
