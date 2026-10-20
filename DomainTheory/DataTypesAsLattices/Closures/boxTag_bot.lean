module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































theorem boxTag_bot (i : ℕ) : boxTag i botElem = botElem := by
  ext n
  simp [boxTag, condSet, botElem]

end DomainTheory.DataTypesAsLattices
