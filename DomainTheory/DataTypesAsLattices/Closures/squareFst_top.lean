/-ai
The first projection of the full set of natural numbers is the full set.

Every natural number belongs to the full set, and so does every double.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem squareFst_top : squareFst topElem = topElem := by
  ext n
  constructor
  · intro; exact Set.mem_univ n
  · intro; exact Set.mem_univ (2 * n)

end DomainTheory.DataTypesAsLattices
