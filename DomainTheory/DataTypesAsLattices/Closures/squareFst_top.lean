module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
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
