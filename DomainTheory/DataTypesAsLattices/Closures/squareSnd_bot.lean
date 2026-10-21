/-ai
The second projection of the empty set is empty.

Both sides are empty by the definitions of the second projection and of the empty set.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem squareSnd_bot : squareSnd botElem = botElem := by
  ext m
  simp [squareSnd, botElem]

end DomainTheory.DataTypesAsLattices
