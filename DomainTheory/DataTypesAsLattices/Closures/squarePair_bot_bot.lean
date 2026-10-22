/-ai
The disjoint pairing of two empty sets is empty.

Both sides are empty by the definitions of disjoint pairing and of the empty set.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem squarePair_bot_bot : squarePair botElem botElem = (botElem : Pomega) := by
  ext k
  simp [squarePair, botElem]

end DomainTheory.DataTypesAsLattices
